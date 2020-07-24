import builtins, coverage, func_timeout, inspect, json, logging, multiprocessing, os, sys, traceback
import conbyte.global_utils, conbyte.path_to_constraint, conbyte.solver
from conbyte.concolic_types.concolic_int import ConcolicInt
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.concolic_types.concolic_list import ConcolicList

log = logging.getLogger("ct.explore")
coverage_omit = ['py-conbyte.py', 'conbyte/**', '**/_virtualenv.py']

class ExplorationEngine:
    def __init__(self, module, entry, query_store, solver, ss):
        self.module_name = module # 先只單純記下字串，等到要真正 import 的時候再去做 # __import__(module)
        self.entry = module if entry is None else entry
        self.constraints_to_solve = [] # 指的是還沒、但即將被 solver 解出 model 的 constraint
        self.path = conbyte.path_to_constraint.PathToConstraint()
        self.solver = conbyte.solver.Solver(query_store, solver, ss)
        self.input_sets = []
        self.error_sets = []
        self.result_sets = []
        self.total_execution_coverage = coverage.CoverageData()
        self.coverage = coverage.Coverage(branch=True, omit=coverage_omit)

    def explore(self, ini_vars, max_iterations, timeout=None):
        cont = self._one_execution(ini_vars) # the 1st execution
        iterations = 1
        while cont and iterations < max_iterations and len(self.constraints_to_solve) > 0:
            ##############################################################
            # In each iteration, we take one constraint out of the queue
            # and try to solve for it. After that we'll obtain a model as
            # a list of arguments and continue the next iteration with it.
            constraint = self.constraints_to_solve.pop(0)
            model = self.solver.find_constraint_model(constraint, timeout)
            log.debug("Solving: %s" % constraint)
            ##############################################################
            if model is not None:
                log.info("=== Iterations: %s ===" % iterations); iterations += 1
                args = list(model.values()) # from model to argument
                cont = self._one_execution(args) # other consecutive executions following the 1st execution
        self.execute_coverage()
        return iterations - 1

    def _one_execution(self, init_vars):
        parent, child = multiprocessing.Pipe()
        pid = os.fork()
        if pid == 0: # child process
            log.info("Inputs: " + str(init_vars))
            builtins.len = lambda x: x.__len__()
            self.path.current_constraint = self.path.root_constraint
            import conbyte.concolic_downcaster
            execute = getattr(__import__(self.module_name), self.entry)
            args = self._get_concolic_parameters(execute, init_vars)
            input_sets = result = None
            try:
                result = conbyte.global_utils.downgrade(func_timeout.func_timeout(5, execute, args=args))
                log.info("Return: %s" % result)
                input_sets = init_vars # preserve this argument set for the later use if successful
            except func_timeout.FunctionTimedOut:
                traceback.print_exc()
                log.error("Execution Timeout: %s" % args)
                sys.exit(1)
            except Exception as e:
                self.error_sets.append(args)
                print(e)
                # traceback.print_exc()
                log.error("Execution exception for: %s" % args)
            child.send([result, input_sets, self.error_sets, self.constraints_to_solve, self.path, self.solver.variables])
            child.close()
            os._exit(os.EX_OK)
        else: # parent process
            result, input_sets, self.error_sets, self.constraints_to_solve, self.path, self.solver.variables = parent.recv()
            parent.close()
            if input_sets is not None and result is not None:
                self.input_sets.append(input_sets); self.result_sets.append(result)
                execute = getattr(__import__(self.module_name), self.entry) # TODO: 把 import 放進下一行的 coverage section 好像會算錯
                self.coverage.start(); res = execute(*input_sets); self.coverage.stop()
                if res != result: print('Input:', input_sets, 'My answer:', result, 'Correct answer:', res)
                assert res == result
                self.total_execution_coverage.update(self.coverage.get_data())
            # for file in self.total_execution_coverage.measured_files():
            #     _, _, missing_lines, _ = self.coverage.analysis(file)
            #     if len(missing_lines) > 0: print(missing_lines); return True
            return len(self.coverage_statistics()[2]) > 0
            # return False

    def _get_concolic_parameters(self, func, init_vars):
        para = inspect.signature(func).parameters.copy() # 要加 copy，否則 para 不給修改
        for a, b in zip(para.values(), init_vars):
            para[a.name] = a.replace(default=b)
        copy_vars = []
        self.solver.variables = dict()
        for v in para.values():
            if isinstance(v.default, int):
                copy_vars.append(ConcolicInt(v.default, v.name))
                self.solver.variables[v.name] = 'Int'
            elif isinstance(v.default, str):
                copy_vars.append(ConcolicStr(v.default, v.name))
                self.solver.variables[v.name] = 'String'
            elif isinstance(v.default, list):
                for i in range(len(v.default)):
                    v.default[i] = conbyte.global_utils.upgrade(v.default[i])
                copy_vars.append(ConcolicList(v.default, v.name))
                if len(v.default) == 0 or isinstance(v.default[0], ConcolicInt):
                    self.solver.variables[v.name] = 'ListOfInt'
                elif isinstance(v.default[0], ConcolicStr):
                    self.solver.variables[v.name] = 'ListOfStr'
                else:
                    raise NotImplementedError
            elif v.default is not None:
                raise NotImplementedError
        return copy_vars

    def execute_coverage(self):
        execute = getattr(__import__(self.module_name), self.entry)
        cov = coverage.Coverage(branch=True, omit=coverage_omit)
        for args, res in zip(self.input_sets, self.result_sets):
            cov.start()
            result = execute(*args)
            cov.stop()
            if res != result:
                print('Input:', args, 'My answer:', res, 'Correct answer:', result)
            assert res == result
            self.total_execution_coverage.update(cov.get_data())

    def print_coverage(self):
        total_lines, executed_lines, missing_lines, executed_branches = self.coverage_statistics()
        print("\nLine coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        print("Branch coverage {}".format(executed_branches))
        if len(missing_lines) > 0:
            print("Missing lines:")
            for file, lines in missing_lines.items():
                print("  {}: {}".format(file, lines))
        print("")

    def coverage_statistics(self):
        cov = coverage.Coverage(branch=True, omit=coverage_omit)
        total_lines = 0
        executed_lines = 0
        executed_branches = 0
        missing_lines = {}
        for file in self.total_execution_coverage.measured_files():
            _, executable_lines, _, _ = cov.analysis(file)

            total_lines += len(set(executable_lines)) - 1
            executed_lines += len(set(self.total_execution_coverage.lines(file)))
            executed_branches += len(set(self.total_execution_coverage.arcs(file)))

            # executable_lines starting from 1 do discard the 'def xx():' line
            m_lines = []
            for line in set(executable_lines[1:]):
                if line not in self.total_execution_coverage.lines(file):
                    m_lines.append(line)
            if len(m_lines) > 0:
                missing_lines[file] = m_lines
        return total_lines, executed_lines, missing_lines, executed_branches

    def result_to_json(self):
        res = dict()
        res["inputs"] = self.input_sets
        res["error_inputs"] = self.error_sets
        res["total_lines"], res["executed_lines"], _, res["executed_branches"] = self.coverage_statistics()
        return json.dumps(res)
