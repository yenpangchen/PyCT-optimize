import builtins, func_timeout, inspect, logging, multiprocessing, os, pickle, sys, traceback,json
from libct.constraint import Constraint
from libct.path import PathToConstraint
from libct.solver import Solver
from libct.utils import ConcolicObject, unwrap, get_module_from_rootdir_and_modpath, get_function_from_module_and_funcname

log = logging.getLogger('ct.explore')
sys.setrecursionlimit(1000000) # The original limit is not enough in some special cases.
module = None
execute = None

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
    class Exception(metaclass=type('', (type,), {"__repr__": lambda self: '<EXCEPTION>'})): pass # indicate occurrence of Exception during execution
    class Timeout(metaclass=type('', (type,), {"__repr__": lambda self: '<TIMEOUT>'})): pass # indicate timeout after either a concolic or a primitive execution
    class Unpicklable(metaclass=type('', (type,), {"__repr__": lambda self: '<UNPICKLABLE>'})): pass # indicate that an object is unpicklable
    class LazyLoading(metaclass=type('', (type,), {"__repr__": lambda self: '<DEFAULT>'})): pass # lazily loading default values of primitive arguments

    def __init__(self, *, solver='cvc4', timeout=10, safety=0, store=None, verbose=1, logfile=None, statsdir=False,smtdir=""
                 ,save_dir="",input_name="",only_first_forward=True,
                 module_, execute_):
        global module, execute

        module = module_
        execute = execute_
        
        self.__init2__(); self.statsdir = statsdir
        
        if self.statsdir:
            os.system(f"mkdir -p '{statsdir}'")
            
        Solver.set_basic_configurations(solver, timeout, safety, store, smtdir=False)
        ############################################################
        # This section mainly deals with the logging settings.
        log_level = 25 - 5 * verbose
        # if logfile:
        #     logging.basicConfig(filename=logfile, level=log_level,
        #                         format='%(asctime)s  %(name)s\t%(levelname)s\t %(message)s',
        #                         datefmt='%m/%d/%Y %I:%M:%S %p')
        # elif logfile == '':
        #     logging.basicConfig(level=logging.CRITICAL+1)
        # else:
        #     logging.basicConfig(level=log_level,# stream=sys.stdout,
        #                         format='  %(name)s\t%(levelname)s\t %(message)s')
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
        self.constraints_to_solve = [] # consists of the constraints that are going to be solved by the solver
        self.concolic_name_list = [] ##NOTE for DNN testing

        self.path = PathToConstraint()
        self.in_out = []
        self.var_to_types = {}

    def _execution_loop(self, max_iterations, all_args):
        tried_input_args = [all_args.copy()] # .copy() is important!!
        log.info(f"[{self.funcname}][first execution]")
        log.debug(f"[using arg:]: {tried_input_args}")
        iterations = 1; cont = self._one_execution(all_args) # the 1st execution
        
        # After First execution, no constr to solve
        if not len(self.constraints_to_solve) > 0:
            print('[FIRST_NO_CONSTR]: After First execution, no constr to solve')
            log.info(f'[{self.funcname}][FIRST_NO_CONSTR]: After First execution, no constr to solve')
            return 0
        if not cont:
            log.info(f'[{self.funcname}][FIRST]: After First execution, cont==False')
        while cont and (max_iterations==0 or iterations<max_iterations) and len(self.constraints_to_solve) > 0:
            print('[PyCT_HAS_CONSTRAINT]: After First execution, start trying new input args')
            log.info(f'[{self.funcname}][PyCT_HAS_CONSTRAINT]: After First execution, start trying new input args')
            ##############################################################
            # In each iteration, we take one constraint out of the queue
            # and try to solve for it. After that we'll obtain a model as
            # a list of arguments and continue the next iteration with it.
            constraint = self.constraints_to_solve.pop(0)
            # print(f"[constraint being solved]: {constraint}")

            #---------------------印出constraint-----------------------------
            log.debug(f"[constraint being solved]: {constraint}")
            
            model = Solver.find_model_from_constraint(self, constraint, self.original_args)

            #---------------------印出args-----------------------------
            log.debug(f"[using arg:]: {all_args}")        
            # 
            #     
            ##############################################################
            if model is not None: #sat, model is none->unsat
                all_args.update(model) # from model to argument
                if all_args not in tried_input_args:
                    tried_input_args.append(all_args.copy()) # .copy() is important!!
                    log.info(f"=== [{self.funcname}] find new arg Iterations: {iterations} ===")
                    iterations += 1
                    # print(f"===find new arg Iterations: {iterations} ===")
                    cont = self._one_execution(all_args) # other consecutive executions following the 1st execution
            else:
                log.info(f"[{self.funcname}][model is none,unsat]")
        return iterations

    def _can_use_concolic_wrapper(self, root, modpath):
        r, s = multiprocessing.Pipe()
        if os.fork() == 0: # child process
            try:
                import libct.wrapper
                # module = get_module_from_rootdir_and_modpath(root, modpath)
                s.send(1)
            except:
                s.send(0)
            os._exit(os.EX_OK)
        os.wait()
        ans = r.recv(); r.close(); s.close()
        return ans

    def explore(self, modpath, all_args={}, /, *, root='.', funcname=None, max_iterations=0, single_timeout=15, total_timeout=900
                , deadcode=set(), include_exception=False, lib=None, single_coverage=True, file_as_total=False,concolic_dict={}
                ,norm=True):
        self.modpath = modpath; self.funcname = funcname; self.single_timeout = single_timeout; self.total_timeout = total_timeout; self.include_exception = include_exception; self.deadcode = deadcode; self.lib = lib; self.file_as_total = file_as_total
        self.original_args = all_args.copy()

        if self.funcname is None: self.funcname = self.modpath.split('.')[-1]
        self.__init2__(); self.root = os.path.abspath(root); self.target_file = self.root + '/' + self.modpath.replace('.', '/') + '.py'
        self.single_coverage = single_coverage

        if self.lib: sys.path.insert(0, os.path.abspath(self.lib))
        sys.path.insert(0, self.root)#; sys.path.insert(0, file_dir)
        file_dir = os.path.abspath(os.path.dirname(os.path.join(self.root, self.modpath.replace('.', '/') + '.py')))
        now_dir = os.getcwd()
        self.can_use_concolic_wrapper = self._can_use_concolic_wrapper(self.root, self.modpath)
        # os.chdir(file_dir)
        try:
            iterations = func_timeout.func_timeout(self.total_timeout, self._execution_loop, args=(max_iterations, all_args))
            # iterations = self._execution_loop(max_iterations, all_args)
        except BaseException as e: # importantly note that func_timeout.FunctionTimedOut is NOT inherited from the (general) Exception class.
            print('Was this exception triggered by total_timeout? ' + str(e))
            iterations = 0 # usually catches timeout exceptions
            traceback.print_exc()
            
        os.chdir(now_dir); del sys.path[0]
        if self.lib: del sys.path[0]
        if self.statsdir:
            with open(self.statsdir + '/inputs.pkl', 'wb') as f:
                pickle.dump([e[0] for e in self.in_out], f) # store only inputs
                log.debug(f'in_out:{self.in_out}')
                #print("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",[e[0] for e in self.in_out], f) # store only inputs

            with open(self.statsdir + '/smt.csv', 'w') as f:
                f.write(',number,time\n')
                f.write(f'sat,{Solver.stats["sat_number"]},{Solver.stats["sat_time"]}\n')
                f.write(f'unsat,{Solver.stats["unsat_number"]},{Solver.stats["unsat_time"]}\n')
                f.write(f'otherwise,{Solver.stats["otherwise_number"]},{Solver.stats["otherwise_time"]}\n')
                f.close()
        return (iterations, Solver.stats["sat_number"], Solver.stats["sat_time"], Solver.stats["unsat_number"], Solver.stats["unsat_time"], Solver.stats["otherwise_number"], Solver.stats["otherwise_time"])

    def _one_execution(self, all_args):
        result = self._one_execution_concolic(all_args) # primitive input arguments "all_args" may be modified here.
        if not self.single_coverage: # We don't measure coverage in the primitive mode under the non-single coverage setting.
            self.in_out.append((all_args.copy(), result)) # .copy() is important! Think why.
            return True # continue iteration
        answer = self._one_execution_primitive(all_args) # we must measure the coverage in the primitive mode since self.constraints_to_solve would become unpicklable if measured in the concolic mode
        # if self.Timeout not in (result, answer):
        if result is not self.Timeout and answer is not self.Timeout:
            # if result != answer:
            diff = result != answer
            # if (type(diff) is bool and diff) or (type(diff) is not bool and diff.any()):
            #     print('Input:', all_args, '／My result:', result, '／Correct answer:', answer)
            # else:
            #     print('Input:', all_args, '／My result:', result,"  result=answer")
            # assert result == answer
            # if type(diff) is bool:
            #     assert not diff
            # else:
            #     assert (result == answer).all()
        else:
            log.info(f"[{self.funcname}] result is timeout: {result is self.Timeout} or answer is timeout {answer is self.Timeout}")
            print(f"result is timeout: {result is self.Timeout} or answer is timeout {answer is self.Timeout}")
            
        return True # continue iteration only if the target file / function coverage is not full yet.

    def _one_execution_concolic(self, all_args):
        r1, s1 = multiprocessing.Pipe(); r2, s2 = multiprocessing.Pipe(); r3, s3 = multiprocessing.Pipe(); r0, s0 = multiprocessing.Pipe()
        def child_process():
            sys.dont_write_bytecode = True # very important to prevent the later primitive mode from using concolic objects imported here...
            prepare(); self.path.__init__(); 
            log.debug("Inputs: " + str(all_args)) ; 
            #print("Inputs: " + str(all_args))
            if self.can_use_concolic_wrapper:
                import libct.wrapper
            else:
                import libct
            ccc_args, ccc_kwargs = self._get_concolic_arguments(execute, all_args) # primitive input arguments "all_args" may be modified here.
            # print("ccc_args: ",ccc_args)
            # print("ccc_kwargs: ",ccc_kwargs)
            try:
                s1.send((all_args, self.var_to_types, self.concolic_name_list))
            except Exception as e:
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        # print(f"Exception for: {all_args} , exception: {e}>> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception", file=f)
                        traceback.print_exc(file=f)
                        
                s1.send(({}, self.var_to_types))
            
            result = self.Exception
            try:
                # result = libct.utils.unwrap(func_timeout.func_timeout(self.single_timeout, execute, args=ccc_args, kwargs=ccc_kwargs))
                result = libct.utils.unwrap(execute(*ccc_args, **ccc_kwargs))
                log.debug(f"Return: {result}")
                #print(f"Return: {result}")
            except func_timeout.FunctionTimedOut:
                result = self.Timeout
                # ----------------------------error log
                # log.error(f"Timeout (soft) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception")#; traceback.print_exc()
                log.error(f'[{self.funcname}] Time_out_exception') 
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print(f"Timeout (soft) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception", file=f)
            except Exception as e:
                # traceback.print_exc()
                # ----------------------------error log
                # log.error(f"function name:{self.funcname} Exception for: {all_args} , exception: {e} >> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception")#; log.error(e)
                log.error(f'[{self.funcname}] some exception --concolic :{e}') 
                if self.statsdir:
                    with open(self.statsdir + '/exception.txt', 'a') as f:
                        print(f"Exception for: {all_args} , exception: {e}>> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception", file=f)
                        # print(e, file=f)
                        traceback.print_exc(file=f)
            ###################################### Communication Section ######################################
            s0.send(0) # just a notification to the parent process that we're going to send data
            try: s2.send(result)
            except: s2.send(self.Unpicklable)
            try: s3.send((Constraint.global_constraints, self.constraints_to_solve, self.path))
            except: s3.send(self.Unpicklable) # may fail if they contain some unpicklable objects
        process = multiprocessing.Process(target=child_process); process.start()
        (all_args2, self.var_to_types, self.concolic_name_list) = r1.recv(); r1.close(); s1.close(); all_args.clear(); all_args.update(all_args2) # update the parameter directly
        if not r0.poll(self.single_timeout + 5):
            result = self.Timeout
            # ----------------------------error log
            # log.error(f"Timeout (hard) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception")
            log.error(f'[{self.funcname}] Time_out_exception') 
            if self.statsdir:
                with open(self.statsdir + '/exception.txt', 'a') as f:
                    print(f"Timeout (hard) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception", file=f)
        else:
            result = r2.recv()
            if (t:=r3.recv()) is not self.Unpicklable:
                (Constraint.global_constraints, self.constraints_to_solve, self.path) = t
                
        r2.close(); s2.close(); r3.close(); s3.close(); r0.close(); s0.close()
        if process.is_alive(): process.kill()
        return result
    
    # def _one_execution_concolic(self, all_args):
    #     def child_process():
    #         # sys.dont_write_bytecode = True # very important to prevent the later primitive mode from using concolic objects imported here...
    #         prepare(); self.path.__init__(); log.info("Inputs: " + str(all_args))
    #         if self.can_use_concolic_wrapper:
    #             import libct.wrapper
    #         else:
    #             import libct
    #         ccc_args, ccc_kwargs = self._get_concolic_arguments(execute, all_args) # primitive input arguments "all_args" may be modified here.

    #         all_args2 = all_args.copy()
                
    #         all_args.clear()
    #         all_args.update(all_args2) # update the parameter directly
            
    #         result = self.Exception
    #         try:
    #             # result = libct.utils.unwrap(func_timeout.func_timeout(self.single_timeout, execute, args=ccc_args, kwargs=ccc_kwargs))
    #             result = libct.utils.unwrap(execute(*ccc_args, **ccc_kwargs))
    #             log.info(f"Return: {result}")
    #             print(f"Return: {result}")
    #         except func_timeout.FunctionTimedOut:
    #             result = self.Timeout
    #             log.error(f"Timeout (soft) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception")#; traceback.print_exc()
    #             if self.statsdir:
    #                 with open(self.statsdir + '/exception.txt', 'a') as f:
    #                     print(f"Timeout (soft) for: {all_args} >> ./pyct.py -r '{self.root}' '{self.modpath}' -s {self.funcname} {{}} --lib '{self.lib}' --include_exception", file=f)
    #         except Exception as e:
    #             traceback.print_exc()
    #             log.error(f"Exception for: {all_args} >> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception")#; log.error(e)
    #             if self.statsdir:
    #                 with open(self.statsdir + '/exception.txt', 'a') as f:
    #                     print(f"Exception for: {all_args} >> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception", file=f)
    #                     # print(e, file=f)
    #                     traceback.print_exc(file=f)
    #         ###################################### Communication Section ######################################
            
    #         return result

    #     result = child_process()
    #     # (Constraint.global_constraints, self.constraints_to_solve, self.path)
        
    #     return result

    def _one_execution_primitive(self, all_args):
        r1, s1 = multiprocessing.Pipe(); r0, s0 = multiprocessing.Pipe()
        def child_process():
            sys.dont_write_bytecode = True # same reason mentioned in the concolic mode
            
            pri_args, pri_kwargs = self._complete_primitive_arguments(execute, all_args)
            answer = self.Exception
            import coverage
            cov = coverage.Coverage() # Create a coverage instance
            cov.load()
            cov.start() # Start measuring coverage
            
            try:
                # answer = func_timeout.func_timeout(self.single_timeout, execute, args=pri_args, kwargs=pri_kwargs)                
                answer = execute(*pri_args, **pri_kwargs)
                
            except func_timeout.FunctionTimedOut:
                answer = self.Timeout
            except Exception as e:
                # traceback.print_exc()
                log.error(f'[{self.funcname}] some exception --primitive :{e}')
                with open(self.statsdir + '/exception.txt', 'a') as f:
                    print(f"Exception for: {all_args} , one_execution_primitive exception >> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}' --include_exception", file=f)
                    traceback.print_exc(file=f)
                                
            cov.stop() # Stop measuring coverage
            cov.save() # 合并子进程的覆盖率数据到共享对象
                # cov.report(file=open(f'/home/jack/coverage_report_manual/in_pyct.txt', 'w'))
                # cov.report(file=open(f'coverage_report_manual/in_pyct.txt', 'w'))
            
            ###################################### Communication Section ######################################
            s0.send(0) # just a notification to the parent process that we're going to send data
            try:
                s1.send(answer)
            except:
                answer = self.Unpicklable
                s1.send(answer)

        process = multiprocessing.Process(target=child_process); process.start()
        
        if not r0.poll(self.single_timeout + 5):
            answer = self.Timeout
        else:
            answer = r1.recv()
            
        self.in_out.append((all_args.copy(), answer))
        
        r1.close(); s1.close(); r0.close(); s0.close()
        if process.is_alive(): process.kill()
        return answer

    @classmethod
    def _complete_primitive_arguments(cls, func, all_args):
        prim_args = []; prim_kwargs = {}
        already_put_in = []
        for v in inspect.signature(func).parameters.values():
            # if v.kind in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD): continue # ignore *args, **kwargs at last
            
            if v.kind == inspect.Parameter.VAR_POSITIONAL:
                if "*args" in all_args:
                    prim_args.extend(all_args["*args"])
                    
            elif v.kind == inspect.Parameter.VAR_KEYWORD:
                continue
            else:
                already_put_in.append(v.name)
                value = v.default if (t:=all_args[v.name]) is cls.LazyLoading else t
                if v.kind is inspect.Parameter.KEYWORD_ONLY:
                    prim_kwargs[v.name] = value
                else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                    prim_args.append(value)
                    
        # 將有傳入的keyword參數但上面沒有處理到的，補上去
        for k, v in all_args.items():
            if k not in already_put_in and k not in ("*args", ):
                prim_kwargs[k] = v
                
        return prim_args, prim_kwargs

    def _get_concolic_arguments(self, func, prim_args):
        ccc_args = []; ccc_kwargs = {}
        self.concolic_name_list = []
        already_put_in = []
        for v in inspect.signature(func).parameters.values():
            if v.kind == inspect.Parameter.VAR_POSITIONAL:
                if "*args" in prim_args:
                    for pi, value in enumerate(prim_args["*args"]):
                        if type(value) in (bool, float, int, str):
                            value = ConcolicObject(value, f"VAR_POSITIONAL_{pi}", self) # '_VAR' is used to avoid name collision
                        ccc_args.append(value)
                    
            elif v.kind == inspect.Parameter.VAR_KEYWORD:
                continue
            else:
                already_put_in.append(v.name)
                if v.name in prim_args:
                    value = prim_args[v.name]
                else:
                    has_value = False
                    if (t:=v.annotation) is not inspect._empty:
                        try: 
                            value = t()
                            has_value = True # may raise TypeError: Cannot instantiate ...
                        except:
                            # traceback.print_exc()
                            with open(self.statsdir + '/exception.txt', 'a') as f:
                                print(f"Exception for: _get_concolic_arguments() >> ./pyct '{self.root}' '{self.modpath}' -s {self.funcname} {{}} -m 20 --lib '{self.lib}'", file=f)
                                traceback.print_exc(file=f)
                    if not has_value:
                        if (t:=v.default) is not inspect._empty: value = unwrap(t) # default values may also be wrapped
                        else: value = ''
                    prim_args[v.name] = value if type(value) in (bool, float, int, str) else self.LazyLoading
                    
                if type(value) in (bool, float, int, str):
                    ccc_obj_name = v.name + '_VAR'  # '_VAR' is used to avoid name collision
                    self.concolic_name_list.append(ccc_obj_name)
                    value = ConcolicObject(value, v.name + '_VAR', self) # '_VAR' is used to avoid name collision
                
                if v.kind is inspect.Parameter.KEYWORD_ONLY:
                    ccc_kwargs[v.name] = value
                else: # v.kind in (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD):
                    ccc_args.append(value)
        
        # 將有傳入的keyword參數但上面沒有處理到的，補上去
        for k, value in prim_args.items():
            if k not in already_put_in and k not in ("*args", ):
                if type(value) in (bool, float, int, str):
                    ccc_obj_name = k + '_VAR'  # '_VAR' is used to avoid name collision
                    self.concolic_name_list.append(ccc_obj_name)
                    value = ConcolicObject(value, k + '_VAR', self) # '_VAR' is used to avoid name collision
                ccc_kwargs[k] = value
 
        if not self.var_to_types: # remain unchanged once determined
            for (k, v) in prim_args.items():
                k += '_VAR' # '_VAR' is used to avoid name collision
                if type(v) is bool: self.var_to_types[k] = 'Bool'
                elif type(v) is float: self.var_to_types[k] = 'Real'
                elif type(v) is int: self.var_to_types[k] = 'Int'
                elif type(v) is str: self.var_to_types[k] = 'String'
                else: pass # for some default values that cannot be concolic-ized
                
        return ccc_args, ccc_kwargs
