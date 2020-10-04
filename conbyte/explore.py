import builtins, coverage, func_timeout, inspect, json, logging, multiprocessing, os, pickle, re, sys, traceback
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
    class Exception: pass # indicate occurrence of Exception during execution
    class Unpicklable: pass # indicate that an object is unpicklable
    class LazyLoading(metaclass=type("MC", (type,), {"__repr__": lambda self: '<DEFAULT>'})): pass # lazily loading default values of primitive arguments

    def __init__(self, *, solver='cvc4', timeout=10, safety=0, store=None, verbose=1, logfile=None, statsdir=None):
        self.__init2__(); self.statsdir = statsdir
        if self.statsdir: os.system(f"rm -rf '{statsdir}'"); os.system(f"mkdir -p '{statsdir}'")
        Solver.set_basic_configurations(solver, timeout, safety, store, statsdir)
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

    def explore(self, modpath, all_args={}, /, *, root='.', funcname=None, max_iterations=200, timeout=15, deadcode=None, include_exception=False, lib=None):
        self.modpath = modpath; self.funcname = funcname; self.timeout = timeout; self.include_exception = include_exception; self.deadcode = deadcode; self.lib = lib
        if self.funcname is None: self.funcname = self.modpath.split('.')[-1]
        self.__init2__(); self.root = os.path.abspath(root); self.target_file = self.root + '/' + self.modpath.replace('.', '/') + '.py'
        self.single_coverage = self.root.startswith(os.path.abspath(os.path.dirname(os.path.dirname(__file__))))
        self.coverage = coverage.Coverage(data_file=None, include=[self.target_file if self.single_coverage else self.root + '/**'])
        if self.lib: sys.path.insert(0, os.path.abspath(self.lib))
        sys.path.insert(0, self.root)
        iterations = 1; cont = self._one_execution(all_args) # the 1st execution
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
                all_args.update(model) # from model to argument
                cont = self._one_execution(all_args) # other consecutive executions following the 1st execution
        sys.path.remove(self.root)
        if self.lib: sys.path.remove(os.path.abspath(self.lib))
        if self.statsdir:
            with open(self.statsdir + '/inputs.pkl', 'wb') as f:
                pickle.dump(self.inputs + self.errors, f)
            with open(self.statsdir + '/smt.csv', 'w') as f:
                f.write(',number,time\n')
                f.write(f'sat,{Solver.stats["sat_number"]},{Solver.stats["sat_time"]}\n')
                f.write(f'unsat,{Solver.stats["unsat_number"]},{Solver.stats["unsat_time"]}\n')
                f.write(f'otherwise,{Solver.stats["otherwise_number"]},{Solver.stats["otherwise_time"]}\n')
        return iterations - 1

    def _one_execution(self, all_args):
        parent, child = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            sys.dont_write_bytecode = True # very important to prevent the later primitive environment from using concolic objects imported here...
            prepare(); self.path.__init__(); log.info("Inputs: " + str(all_args))
            import conbyte.wrapper; execute = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)
            result = self.Exception; ccc_args, ccc_kwargs = self._get_concolic_arguments(execute, all_args) # primitive input arguments "all_args" may be modified here.
            try:
                result = conbyte.utils.unwrap(func_timeout.func_timeout(self.timeout, execute, args=ccc_args, kwargs=ccc_kwargs))
                log.info(f"Return: {result}")
            except func_timeout.FunctionTimedOut as e:
                log.error(f"Execution Timeout: {all_args}")
                print('Timeout Input Vector:', all_args); print(e) #; traceback.print_exc(); sys.exit(1)
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print('Timeout Input Vector:', all_args, file=f); print(e, file=f)
            except Exception as e:
                log.error(f"Execution Exception for: {all_args}")
                print('Exception Input Vector:', all_args); print(e); traceback.print_exc()
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print('Exception Input Vector:', all_args, file=f); print(e, file=f)
        ###################################### Communication Section ######################################
            try: child.send((self.constraints_to_solve, self.path))
            except: child.send(self.Exception)
            try: child.send(result)
            except: child.send(self.Unpicklable)
            child.send((all_args, self.var_to_types)); child.close()
            os._exit(os.EX_OK)
        if (t:=parent.recv()) is not self.Exception: (self.constraints_to_solve, self.path) = t
        result = parent.recv(); (all_args, self.var_to_types) = parent.recv(); parent.close()
        ###################################################################################################
        parent, child = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            sys.dont_write_bytecode = True # same reason mentioned in the concolic environment
            self.coverage.start(); execute = get_funcobj_from_modpath_and_funcname(self.modpath, self.funcname)
            pri_args, pri_kwargs = self._complete_primitive_arguments(execute, all_args)
            try: answer = func_timeout.func_timeout(self.timeout, execute, args=pri_args, kwargs=pri_kwargs); success = True
            except: answer = self.Exception; success = False
            self.coverage.stop()
            self.coverage_data.update(self.coverage.get_data())
            for file in self.coverage_data.measured_files(): # "file" is absolute here.
                _, _, missing_lines, _ = self.coverage.analysis(file)
                if file not in self.coverage_accumulated_missing_lines:
                    self.coverage_accumulated_missing_lines[file] = set(missing_lines)
                else:
                    self.coverage_accumulated_missing_lines[file] = self.coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
        ###################################### Communication Section ######################################
            try: child.send(answer)
            except: answer = self.Unpicklable; child.send(answer)
            self.results.append(answer)
            child.send(self.results)
            child.send((success, self.coverage_data, self.coverage_accumulated_missing_lines)); child.close()
            os._exit(os.EX_OK)
        answer = parent.recv()
        self.results = parent.recv()
        success, a, b = parent.recv(); parent.close()
        ###################################################################################################
        (self.inputs if success else self.errors).append(all_args)
        if self.include_exception or (answer is not self.Exception):
            self.coverage_data, self.coverage_accumulated_missing_lines = a, b
        if (not self.statsdir) and not ((result is answer is self.Exception) or (result is answer is self.Unpicklable)):
            if result != answer: print('Input:', all_args, '／My answer:', result, '／Correct answer:', answer)
            assert result == answer
        for file in self.coverage_data.measured_files(): # "file" is absolute here.
            missing_lines = self.coverage_accumulated_missing_lines[file]
            if missing_lines:
                if not self.single_coverage: return True # continue iteration
                if not (file == self.target_file and self.deadcode == missing_lines):
                    if not self.statsdir: log.info(f"Not Covered Yet: {file} {missing_lines}")
                    return True # continue iteration
        return False # stop iteration

    @classmethod
    def _complete_primitive_arguments(cls, func, all_args):
        prim_args = []; prim_kwargs = {}
        for v in inspect.signature(func).parameters.values():
            if v.kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD): continue # ignore *args, **kwargs at last
            value = v.default if (t:=all_args[v.name]) is cls.LazyLoading else t
            if v.kind is inspect.Parameter.KEYWORD_ONLY:
                prim_kwargs[v.name] = value
            else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                prim_args.append(value)
        return prim_args, prim_kwargs

    def _get_concolic_arguments(self, func, prim_args):
        ccc_args = []; ccc_kwargs = {}
        for v in inspect.signature(func).parameters.values():
            if v.kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD):
                prim_args.pop(v.name, None); continue # do not support *args, **kwargs currently
            if v.name in prim_args:
                value = prim_args[v.name]
            else:
                has_value = False
                if (t:=v.annotation) is not inspect._empty:
                    try: value = t(); has_value = True # may raise TypeError: Cannot instantiate ...
                    except: pass
                if not has_value:
                    if (t:=v.default) is not inspect._empty: value = unwrap(t) # default values may also be wrapped
                    else: value = ''
                prim_args[v.name] = value if type(value) in (bool, float, int, str) else self.LazyLoading
            if type(value) in (bool, float, int, str): value = ConcolicObject(value, v.name, self)
            if v.kind is inspect.Parameter.KEYWORD_ONLY:
                ccc_kwargs[v.name] = value
            else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                ccc_args.append(value)
        if not self.var_to_types: # remain unchanged once determined
            for (k, v) in prim_args.items():
                if type(v) is bool: self.var_to_types[k] = 'Bool'
                elif type(v) is float: self.var_to_types[k] = 'Real'
                elif type(v) is int: self.var_to_types[k] = 'Int'
                elif type(v) is str: self.var_to_types[k] = 'String'
                else: pass # for some default values that cannot be concolic-ized
        return ccc_args, ccc_kwargs

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
            # print(file, executed_lines, total_lines)
        if self.statsdir:
            with open(self.statsdir + '/coverage.txt', 'w') as f:
                f.write("{}/{} ({:.2%})\n".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        return total_lines, executed_lines, missing_lines

    def print_coverage(self):
        total_lines, executed_lines, missing_lines = self.coverage_statistics()
        print("\nLine coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        if missing_lines and self.single_coverage:
            print("Missing lines:") # only print this info when the scope of coverage is a single file.
            for file, lines in missing_lines.items():
                print(f"  {file}: {sorted(lines)}")
        print("")
