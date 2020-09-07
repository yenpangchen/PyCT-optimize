import builtins, coverage, func_timeout, inspect, json, logging, multiprocessing, os, re, sys, traceback
from conbyte.path import PathToConstraint
from conbyte.solver import Solver
from conbyte.utils import ConcolicObject, unwrap

log = logging.getLogger("ct.explore")
sys.setrecursionlimit(1000000) # For some special cases, the original limit is not enough.

def prepare():
    #################################################################
    # Since the source code in https://github.com/python/cpython/blob/e822e37946f27c09953bb5733acf3b07c2db690f/Modules/socketmodule.c#L6485
    # only accepts "unwrapped" input arguments, we simply do it here.
    #################################################################
    import socket
    _socket_getaddrinfo = socket.getaddrinfo
    def socket_getaddrinfo(*args, **kwargs):
        return _socket_getaddrinfo(*map(unwrap, args), **{k: unwrap(v) for (k, v) in kwargs.items()})
    socket.getaddrinfo = socket_getaddrinfo
    #####################################################################
    # The builtin len(...) function will automatically unwrap our result,
    # so we want to avoid this by doing the following line.
    #####################################################################
    builtins.len = lambda x: x.__len__()

class ExplorationEngine:
    def __init__(self, solver, timeout, safety=0, query_store=None):
        self.__init2__()
        Solver.set_solver_timeout_safety_querystore(solver, timeout, safety, query_store)
        ############################################################
        # We add our new logging level called "SMTLIB2" to print out
        # messages related to the solving process.
        ############################################################
        logging.SMTLIB2 = (logging.DEBUG + logging.INFO) // 2
        logging.addLevelName(logging.SMTLIB2, "SMTLIB2")
        def smtlib2(self, message, *args, **kwargs): # https://stackoverflow.com/questions/2183233/how-to-add-a-custom-loglevel-to-pythons-logging-facility/13638084#13638084
            if self.isEnabledFor(logging.SMTLIB2): # Yes, logger takes its '*args' as 'args'.
                self._log(logging.SMTLIB2, message, args, **kwargs)
        logging.Logger.smtlib2 = smtlib2

    def __init2__(self):
        self.constraints_to_solve = [] # 指的是還沒、但即將被 solver 解出 model 的 constraint
        self.path = PathToConstraint()
        self.inputs = []
        self.errors = []
        self.results = []
        self.coverage_data = coverage.CoverageData()
        self.coverage_accumulated_missing_lines = {}
        self.var_to_types = {}

    def explore(self, filename, entry, ini_vars, max_iterations, timeout, deadcode=None):
        self.__init2__()
        self.module_name = os.path.basename(filename).replace(".py", "") # 先只單純記下字串，等到要真正 import 的時候再去做 # __import__(module)
        self.coverage = coverage.Coverage(data_file=None, branch=True, source=[self.module_name])
        self.var_to_types = {}
        iterations = 1
        cont = self._one_execution(iterations, filename, entry, ini_vars, timeout, deadcode) # the 1st execution
        while cont and iterations < max_iterations and len(self.constraints_to_solve) > 0:
            ##############################################################
            # In each iteration, we take one constraint out of the queue
            # and try to solve for it. After that we'll obtain a model as
            # a list of arguments and continue the next iteration with it.
            constraint = self.constraints_to_solve.pop(0)
            model = Solver.find_model_from_constraint(self, constraint)
            ##############################################################
            if model is not None:
                log.info(f"=== Iterations: {iterations} ==="); iterations += 1
                args = list(model.values()) # from model to argument
                cont = self._one_execution(iterations, filename, entry, args, timeout, deadcode) # other consecutive executions following the 1st execution
        return iterations - 1

    def _one_execution(self, iterations, filename, entry, init_vars, timeout, deadcode):
        entry = self.module_name if entry is None else entry
        parent, child = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            sys.path.append(os.path.abspath(filename).replace(os.path.basename(filename), ""))
            prepare(); self.path.__init__(); log.info("Inputs: " + str(init_vars))
            import conbyte.wrapper; execute = getattr(__import__(self.module_name), entry)
            success = False; result = None; conc_args = self._get_concolic_parameters(execute, init_vars)
            try:
                result = conbyte.utils.unwrap(func_timeout.func_timeout(timeout, execute, args=conc_args))
                success = True
                log.info(f"Return: {result}")
            except func_timeout.FunctionTimedOut as e:
                log.error(f"Execution Timeout: {init_vars}")
                print('Timeout Input Vector:', init_vars); print(e) #; traceback.print_exc(); sys.exit(1)
            except Exception as e:
                log.error(f"Execution Exception for: {init_vars}")
                print('Exception Input Vector:', init_vars); print(e) #; traceback.print_exc()
            child.send([success, init_vars, result, self.constraints_to_solve, self.path, self.var_to_types]); child.close()
            os._exit(os.EX_OK)
        success, init_vars, result, self.constraints_to_solve, self.path, self.var_to_types = parent.recv(); parent.close()
        if not success:
            self.errors.append(init_vars)
        else:
            self.inputs.append(init_vars); self.results.append(result)
            parent, child = multiprocessing.Pipe()
            if os.fork() == 0: # child process
                sys.path.append(os.path.abspath(filename).replace(os.path.basename(filename), ""))
                self.coverage.start(); ans = getattr(__import__(self.module_name), entry)(*init_vars); self.coverage.stop()
                self.coverage_data.update(self.coverage.get_data())
                if iterations == 1:
                    for file in self.coverage_data.measured_files():
                        _, _, missing_lines, _ = self.coverage.analysis(file)
                        self.coverage_accumulated_missing_lines[file] = set(missing_lines)
                else: # iterations > 1
                    for file in self.coverage_data.measured_files():
                        _, _, missing_lines, _ = self.coverage.analysis(file)
                        self.coverage_accumulated_missing_lines[file] = self.coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
                child.send(ans)
                child.send(self.coverage_data)
                child.send(self.coverage_accumulated_missing_lines)
                child.close(); os._exit(os.EX_OK)
            ans = parent.recv()
            self.coverage_data = parent.recv()
            self.coverage_accumulated_missing_lines = parent.recv()
            parent.close()
            if result != ans: print('Input:', init_vars, '／My answer:', result, '／Correct answer:', ans)
            assert result == ans
        for file in self.coverage_data.measured_files():
            missing_lines = self.coverage_accumulated_missing_lines[file]
            if missing_lines:
                if not (file == os.path.abspath(filename) and deadcode == missing_lines):
                    log.info(f"Not Covered: {file} {missing_lines}"); return True
        return False

    def _get_concolic_parameters(self, func, init_vars):
        para = inspect.signature(func).parameters.copy() # 要加 copy，否則 para 不給修改
        for a, b in zip(para.values(), init_vars):
            para[a.name] = a.replace(default=b)
        if not self.var_to_types:
            for v in para.values():
                if isinstance(v.default, bool): self.var_to_types[v.name] = 'Bool'
                elif isinstance(v.default, float): self.var_to_types[v.name] = 'Real'
                elif isinstance(v.default, int): self.var_to_types[v.name] = 'Int'
                elif isinstance(v.default, str): self.var_to_types[v.name] = 'String'
                elif v.default is not None:
                    raise NotImplementedError
        copy_vars = []
        for v in para.values():
            if isinstance(v.default, (bool, float, int, str)):
                copy_vars.append(ConcolicObject(v.default, v.name, self))
            elif v.default is not None:
                raise NotImplementedError
        return copy_vars

    def coverage_statistics(self):
        total_lines = 0
        executed_lines = 0
        executed_branches = 0
        missing_lines = {}
        for file in self.coverage_data.measured_files():
            _, executable_lines, _, _ = self.coverage.analysis(file)
            m_lines = self.coverage_accumulated_missing_lines[file]

            total_lines += len(set(executable_lines))
            executed_lines += len(set(executable_lines)) - len(m_lines) # len(set(self.coverage_data.lines(file)))
            executed_branches += 0 #len(set(self.coverage_data.arcs(file)))

            # executable_lines starting from 1 do discard the 'def xx():' line
            # m_lines = []
            # for line in set(executable_lines[1:]):
            #     if line not in self.coverage_data.lines(file):
            #         m_lines.append(line)
            if m_lines:
                missing_lines[file] = m_lines
        return total_lines, executed_lines, missing_lines, executed_branches

    def print_coverage(self):
        total_lines, executed_lines, missing_lines, executed_branches = self.coverage_statistics()
        print("\nLine coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        print(f"Branch coverage {executed_branches}")
        if len(missing_lines) > 0:
            print("Missing lines:")
            for file, lines in missing_lines.items():
                print(f"  {file}: {sorted(lines)}")
        print("")
