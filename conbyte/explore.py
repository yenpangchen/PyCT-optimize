import coverage, func_timeout, inspect, json, logging, multiprocessing, os, queue, traceback
import conbyte.global_utils
import conbyte.path_to_constraint
import conbyte.solver

log = logging.getLogger("ct.explore")
coverage_omit = ['py-conbyte.py', 'conbyte/**']

class ExplorationEngine:
    def __init__(self, module, entry, query_store, solver, ss):
        # Set up import environment
        self.t_module = module # 先用字串替代，等到要真正 import 的時候再去做 # __import__(module)
        self.entry = module if entry is None else entry
        self.constraints_to_solve = queue.Queue() # 指的是還沒、但即將被 solver 解出 model 的 constraint
        self.input_sets = []
        self.error_sets = []
        self.in_ret_sets = dict()
        self.total_execution_coverage = coverage.CoverageData()
        self.path = conbyte.path_to_constraint.PathToConstraint()
        self.solver = conbyte.solver.Solver(query_store, solver, ss)

    def explore(self, ini_vars, max_iterations, timeout=None):
        p1, p2 = multiprocessing.Pipe()
        pid = os.fork()
        if pid == 0: # child process
            # from conbyte.concolic_types.concolic_bool import ConcolicBool
            # global_utils.engine.path.which_branch(ConcolicBool(False, ['=', 1, 1]))
            # The case of 0 constraints should have produced a trivial solution, however our program
            # here doesn't do this, so we need one additional branch to achieve this goal.

            import builtins
            builtins.len = lambda x: x.__len__()
            import conbyte.concolic_downcaster
            assert isinstance(self.t_module, str)
            self.t_module = __import__(self.t_module)
            # First Execution
            self._one_execution(ini_vars)
            # self.executor.extend_prune()
            iterations = 1

            # TODO: Currently single thread
            while iterations < max_iterations and not self.constraints_to_solve.empty():
                constraint = self.constraints_to_solve.get()
                model = self.solver.find_constraint_model(constraint, timeout)
                log.debug("Solving: %s" % constraint)

                if model is not None:
                    log.info("=== Iterations: %s ===" % iterations)
                    iterations += 1
                    args = self._model_to_arguments(model)
                    try:
                        result = func_timeout.func_timeout(5, self._one_execution, args=(args, constraint))
                    except func_timeout.FunctionTimedOut:
                        log.error("Execution Timeout: %s" % args)
                        sys.exit(1)
                    except Exception as e:
                        log.error("Execution exception for: %s" % args)
                        print(e)
                        # traceback.print_exc()
                    # self.executor.extend_prune()
                    if args not in self.input_sets:
                        self.error_sets.append(args)

            p1.send(self.in_ret_sets)
            p1.send(self.input_sets)
            p1.send(self.error_sets)
            os._exit(os.EX_OK)

        else: # parent process
            os.waitpid(pid, 0)
            self.in_ret_sets = p2.recv()
            self.input_sets = p2.recv()
            self.error_sets = p2.recv()

        self.execute_coverage()

    def _model_to_arguments(self, model):
        args = []
        for name, value in model.items():
            args.append(value)
        # args.reverse()
        return args

    def _one_execution(self, init_vars, expected_path=None):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        from conbyte.concolic_types.concolic_str import ConcolicStr
        from conbyte.concolic_types.concolic_list import ConcolicList
        conbyte.global_utils.extend_vars = dict()
        conbyte.global_utils.extend_queries = []
        conbyte.global_utils.num_of_extend_vars = 0
        log.info("Inputs: " + str(init_vars))
        self.path.reset(expected_path)
        execute = getattr(self.t_module, self.entry)
        ###################################################
        para = inspect.signature(execute).parameters.copy()
        for a, b in zip(para.values(), init_vars):
            para[a.name] = a.replace(default=b)
        copy_vars = []
        symbolic_inputs = dict()
        for v in para.values():
            if type(v.default) == int:
                copy_vars.append(ConcolicInt(v.default, v.name))
                symbolic_inputs[v.name] = 'Int'
            elif type(v.default) == str:
                copy_vars.append(ConcolicStr(v.default, v.name))
                symbolic_inputs[v.name] = 'String'
            elif type(v.default) == list:
                for i in range(len(v.default)):
                    v.default[i] = conbyte.global_utils.upgrade(v.default[i])
                copy_vars.append(ConcolicList(v.default, v.name))
                if len(v.default) == 0 or isinstance(v.default[0], ConcolicInt):
                    symbolic_inputs[v.name] = 'ListOfInt'
                elif isinstance(v.default[0], ConcolicStr):
                    symbolic_inputs[v.name] = 'ListOfStr'
                else:
                    raise NotImplementedError
            elif v.default != None:
                raise NotImplementedError
        self.solver.variables = symbolic_inputs
        ###################################################
        result = execute(*copy_vars)
        log.info("Return: %s" % result)

        self.input_sets.append(init_vars)
        for i in range(len(init_vars)):
            if type(init_vars[i]) is list:
                init_vars[i] = tuple(init_vars[i])
        if hasattr(result, 'parent'):
            self.in_ret_sets[tuple(init_vars)] = result.parent()
        else:
            self.in_ret_sets[tuple(init_vars)] = result

    def execute_coverage(self):
        assert isinstance(self.t_module, str)
        self.t_module = __import__(self.t_module)
        execute = getattr(self.t_module, self.entry)
        cov = coverage.Coverage(branch=True, omit=coverage_omit)
        for args in self.input_sets:
            cov.start()
            for i in range(len(args)):
                if type(args[i]) is tuple:
                    args[i] = list(args[i])
            result = execute(*args)
            cov.stop()
            if self.in_ret_sets[tuple(args)] != result:
                print('Input:', args, 'My answer:', self.in_ret_sets[tuple(args)], 'Correct answer:', result)
            assert self.in_ret_sets[tuple(args)] == result
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

            # total_lines -1 to discard the 'def xx():' line
            total_lines += (len(set(executable_lines)) - 1)
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
        total_lines, executed_lines, executed_branches = self.coverage_statistics()
        res["total_lines"] = total_lines
        res["executed_lines"] = executed_lines
        res["executed_branches"] = executed_branches

        return json.dumps(res)
