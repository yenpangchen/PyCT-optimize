import builtins, coverage, func_timeout, inspect, json, logging, multiprocessing, os, re, sys, traceback
from conbyte.path import PathToConstraint
from conbyte.solver import Solver
from conbyte.utils import ConcolicObject, unwrap, get_funcobj_from_modpath_and_funcname

log = logging.getLogger("ct.explore")
sys.setrecursionlimit(1000000) # The original limit is not enough in some special cases.

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
    class Exception: pass # used to indicate occurrence of Exception during execution

    def __init__(self, *, solver='cvc4', timeout=10, safety=0, store=None, verbose=1, logfile=None):
        self.__init2__()
        Solver.set_solver_timeout_safety_store(solver, timeout, safety, store)
        ############################################################
        # This section mainly deals with the logging settings.
        log_level = 25 - 5 * verbose
        if logfile:
            logging.basicConfig(filename=logfile, level=log_level,
                                format='%(asctime)s  %(name)s\t%(levelname)s\t %(message)s',
                                datefmt='%m/%d/%Y %I:%M:%S %p')
        elif logfile == '':
            logging.basicConfig(level=logging.CRITICAL+1)
        else:
            logging.basicConfig(level=log_level,# stream=sys.stdout,
                                format='  %(name)s\t%(levelname)s\t %(message)s')
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

    def explore(self, modpath, init_vars=[], *, root='.', funcname=None, max_iterations=200, timeout=15, check_return=True, include_exception=False, deadcode=None, lib=None):
        self.modpath, self.funcname, self.timeout, self.check_return, self.include_exception, self.deadcode, self.lib = modpath, funcname, timeout, check_return, include_exception, deadcode, lib
        if self.funcname is None: self.funcname = self.modpath.split('.')[-1]
        self.__init2__(); self.root = os.path.abspath(root); self.target_file = self.root + '/' + self.modpath.replace('.', '/') + '.py'
        if self.root.startswith(os.path.abspath(os.path.dirname(os.path.dirname(__file__)))):
            self.coverage = coverage.Coverage(data_file=None, branch=True, include=[self.target_file])
        else:
            self.coverage = coverage.Coverage(data_file=None, branch=True, include=[self.root + '/**'])
        iterations = 1
        cont = self._one_execution(iterations, init_vars) # the 1st execution
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
                cont = self._one_execution(iterations, args) # other consecutive executions following the 1st execution
        return iterations - 1

    def _one_execution(self, iterations, init_vars):
        parent, child = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            if self.lib: sys.path.insert(0, os.path.abspath(self.lib))
            sys.path.insert(0, self.root)
            prepare(); self.path.__init__(); log.info("Inputs: " + str(init_vars))
            import conbyte.wrapper; execute = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)
            result = self.Exception()
            try:
                conc_args = self._get_concolic_parameters(execute, init_vars) # may cause errors if function parameters contain something like **kwargs.
                init_vars = list(map(unwrap, conc_args)) # "init_vars" may be set at the above line if it is not given initially.
                result = conbyte.utils.unwrap(func_timeout.func_timeout(self.timeout, execute, args=conc_args))
                log.info(f"Return: {result}")
            except func_timeout.FunctionTimedOut as e:
                log.error(f"Execution Timeout: {init_vars}")
                print('Timeout Input Vector:', init_vars); print(e) #; traceback.print_exc(); sys.exit(1)
            except Exception as e:
                log.error(f"Execution Exception for: {init_vars}")
                print('Exception Input Vector:', init_vars); print(e); traceback.print_exc()
        ###################################### Communication Section ######################################
            if self.check_return: child.send(result)
            child.send((init_vars, self.constraints_to_solve, self.path, self.var_to_types)); child.close()
            os._exit(os.EX_OK)
        if self.check_return: result = parent.recv()
        init_vars, self.constraints_to_solve, self.path, self.var_to_types = parent.recv(); parent.close()
        ###################################################################################################
        parent, child = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            if self.lib: sys.path.insert(0, os.path.abspath(self.lib))
            sys.path.insert(0, self.root)
            self.coverage.start(); answer = self.Exception()
            try:
                answer = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)(*init_vars)
                self.inputs.append(init_vars); self.results.append(answer)
            except:
                self.errors.append(init_vars)
            self.coverage.stop()
            self.coverage_data.update(self.coverage.get_data())
            for file in self.coverage_data.measured_files():
                _, _, missing_lines, _ = self.coverage.analysis(file)
                if file not in self.coverage_accumulated_missing_lines:
                    self.coverage_accumulated_missing_lines[file] = set(missing_lines)
                else:
                    self.coverage_accumulated_missing_lines[file] = self.coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
        ###################################### Communication Section ######################################
            if self.check_return: child.send(answer); child.send(self.results)
            child.send((self.inputs, self.errors, self.coverage_data, self.coverage_accumulated_missing_lines)); child.close()
            os._exit(os.EX_OK)
        if self.check_return: answer = parent.recv(); self.results = parent.recv()
        self.inputs, self.errors, a, b = parent.recv(); parent.close()
        ###################################################################################################
        if self.include_exception or not isinstance(answer, self.Exception):
            self.coverage_data, self.coverage_accumulated_missing_lines = a, b
        if self.check_return and not isinstance(result, self.Exception) and not isinstance(answer, self.Exception):
            if result != answer: print('Input:', init_vars, '／My answer:', result, '／Correct answer:', answer)
            assert result == answer
        for file in self.coverage_data.measured_files(): # "file" is absolute here.
            missing_lines = self.coverage_accumulated_missing_lines[file]
            if missing_lines:
                if not (file == self.target_file and self.deadcode == missing_lines):
                    log.info(f"Not Covered Yet: {file} {missing_lines}"); return True
        return False

    def _get_concolic_parameters(self, func, init_vars):
        para = inspect.signature(func).parameters.copy() # 要加 copy，否則 para 不給修改
        if len(init_vars) > 0:
            for a, b in zip(para.values(), init_vars):
                para[a.name] = a.replace(default=b)
        else:
            for a in para.values():
                para[a.name] = a.replace(default='')
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
        missing_lines = {}
        for file in self.coverage_data.measured_files():
            _, executable_lines, _, _ = self.coverage.analysis(file)
            m_lines = self.coverage_accumulated_missing_lines[file]
            total_lines += len(set(executable_lines))
            executed_lines += len(set(executable_lines)) - len(m_lines) # Do not use "len(set(self.coverage_data.lines(file)))" here!!!
            if m_lines: missing_lines[file] = m_lines
        return total_lines, executed_lines, missing_lines

    def print_coverage(self):
        total_lines, executed_lines, missing_lines = self.coverage_statistics()
        print("\nLine coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        if missing_lines and self.root.startswith(os.path.abspath(os.path.dirname(os.path.dirname(__file__)))):
            print("Missing lines:") # only print this info when the scope of coverage is a single file.
            for file, lines in missing_lines.items():
                print(f"  {file}: {sorted(lines)}")
        print("")
