import sys
import os
import logging
import inspect
import traceback
import json
import copy
import coverage
import multiprocessing
from func_timeout import func_timeout, FunctionTimedOut

from conbyte.concolic_types.concolic_int import ConcolicInt
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.concolic_types.concolic_list import ConcolicList

from .utils import Queue
from .path_to_constraint import PathToConstraint
from .solver import Solver

from global_var import upgrade

log = logging.getLogger("ct.explore")

class ExplorationEngine:

    def __init__(self, path, filename, module, entry, ini_vars, query_store, solver_type, ss):
        # Set up import environment
        sys.path.append(path)
        self.t_module = module # 先用字串替代，等到要真正 import 的時候再去做 # __import__(module)
        if entry == None:
            self.entry = module
        else:
            self.entry = entry

        self.ini_vars = ini_vars
        self.symbolic_inputs = None
        self.new_constraints = []
        self.constraints_to_solve = Queue()
        self.solved_constraints = Queue()
        self.finished_constraints = []
        self.input_sets = []
        self.error_sets = []
        self.in_ret_sets = dict()
        self.global_execution_coverage = coverage.CoverageData()

        self.path = PathToConstraint()

        if query_store is not None:
            if not os.path.isdir(query_store):
                raise IOError("Query folder {} not found".format(query_store))

        self.solver = Solver(query_store, solver_type, ss)
        self.coverage_omit = ['py-conbyte.py', 'conbyte/**']

    def add_constraint(self, constraint):
        self.new_constraints.append(constraint)

    def _is_exploration_complete(self):
        num_constr = self.constraints_to_solve.q_size()
        if num_constr == 0 and self.solved_constraints.is_empty():
            return True
        else:
            return False

    def explore(self, max_iterations, timeout=None):
        p1, p2 = multiprocessing.Pipe()
        pid = os.fork()
        if pid == 0: # child process
            import global_var
            from conbyte.concolic_types.concolic_bool import ConcolicBool
            global_var.global_engine.path.which_branch(ConcolicBool(['=', 1, 1], False))
            # The case of 0 constraints should have produced a trivial solution, however our program
            # here doesn't do this, so we need one additional branch to achieve this goal.

            import concolic_upgrader
            assert isinstance(self.t_module, str)
            self.t_module = __import__(self.t_module)
            # First Execution
            self._one_execution(self.ini_vars)
            # self.executor.extend_prune()
            iterations = 1

            # TODO: Currently single thread
            while not self._is_exploration_complete():
                if iterations >= max_iterations:
                    break

                if not self.solved_constraints.is_empty():
                    selected_id, result, model = self.solved_constraints.pop()

                    if selected_id in self.finished_constraints:
                        continue

                    selected_constraint = self.path.find_constraint(selected_id)
                else:
                    cnt = 0
                    while not self.constraints_to_solve.is_empty():
                        target, extend_var, extend_queries = self.constraints_to_solve.pop()
                        log.debug("Solving: %s" % target)
                        asserts, query = target.get_asserts_and_query()

                        ret, model = self.solver.find_counter_example(asserts, query, extend_var, extend_queries, timeout)

                        self.solved_constraints.push((target.id, ret, model))
                        # Every 4 solve check if any new inputs
                        cnt += 1
                        if cnt == 4:
                            break
                    continue

                if model is not None:
                    log.info("=== Iterations: %s ===" % iterations)
                    iterations += 1
                    args = self._recordInputs(model)
                    try:
                        ret = func_timeout(5, self._one_execution, args=(args, selected_constraint))
                    except FunctionTimedOut:
                        log.error("Execution Timeout: %s" % args)
                    except Exception as e:
                        log.error("Execution exception for: %s" % args)
                        traceback.print_exc()
                    # self.executor.extend_prune()
                    if args not in self.input_sets:
                        self.error_sets.append(args)
                    # self.num_processed_constraints += 1
                self.finished_constraints.append(selected_id)

            p1.send(self.in_ret_sets)
            p1.send(self.input_sets)
            p1.send(self.error_sets)
            sys.exit(0)

        else: # parent process
            os.waitpid(pid, 0)
            self.in_ret_sets = p2.recv()
            self.input_sets = p2.recv()
            self.error_sets = p2.recv()

        self.execute_coverage()

    def _getInputs(self):
        return self.symbolic_inputs.copy()

    def _recordInputs(self, model):
        args = []
        for name, value in model.items():
            args.append(value)
        # args.reverse()
        return args


    def _one_execution(self, init_vars, expected_path=None):
        log.info("Inputs: " + str(init_vars))
        copy_vars = copy.deepcopy(init_vars)
        self.path.reset(expected_path)
        execute = getattr(self.t_module, self.entry)
        ###################################################
        para = inspect.signature(execute).parameters.copy()
        for a, b in zip(para.values(), init_vars):
            para[a.name] = a.replace(default=b)
        copy_vars = []
        self.symbolic_inputs = dict()
        for v in para.values():
            if type(v.default) == int:
                copy_vars.append(ConcolicInt(v.name, v.default))
                self.symbolic_inputs[v.name] = 'Int'
            elif type(v.default) == str:
                copy_vars.append(ConcolicStr(v.name, v.default))
                self.symbolic_inputs[v.name] = 'String'
            elif type(v.default) == list:
                for i in range(len(v.default)):
                    v.default[i] = upgrade(v.default[i])
                copy_vars.append(ConcolicList(v.default))
                self.symbolic_inputs[v.name] = 'List'
            elif v.default != None:
                raise NotImplementedError
        self.solver.set_variables(self.symbolic_inputs)
        ###################################################
        ret = execute(*copy_vars)
        log.info("Return: %s" % ret)

        while len(self.new_constraints) > 0:
            constraint = self.new_constraints.pop()
            constraint.inputs = self._getInputs()
            extend_var, extend_queries = dict(), []
            self.constraints_to_solve.push((constraint, extend_var, extend_queries))

        self.input_sets.append(init_vars)
        for i in range(len(init_vars)):
            if type(init_vars[i]) is list:
                init_vars[i] = tuple(init_vars[i])
        if hasattr(ret, 'parent'):
            self.in_ret_sets[tuple(init_vars)] = ret.parent()
        else:
            self.in_ret_sets[tuple(init_vars)] = ret

    def execute_coverage(self):
        assert isinstance(self.t_module, str)
        self.t_module = __import__(self.t_module)
        execute = getattr(self.t_module, self.entry)
        cov = coverage.Coverage(branch=True, omit=self.coverage_omit)
        for args in self.input_sets:
            cov.start()
            copy_args = copy.deepcopy(args)
            ret = execute(*copy_args)
            cov.stop()
            if self.in_ret_sets[tuple(args)] != ret:
                print('Input:', args, 'My answer:', self.in_ret_sets[tuple(args)], 'Correct answer:', ret)
            assert self.in_ret_sets[tuple(args)] == ret
            self.global_execution_coverage.update(cov.get_data())


    def print_coverage(self):
        total_lines, executed_lines, missing_lines, executed_branches = self.coverage_statistics()
        print("Line coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
        print("Branch coverage {}".format(executed_branches))
        if len(missing_lines) > 0:
            print("Missing lines:")
            for file, lines in missing_lines.items():
                print("  {}: {}".format(file, lines))
        print("")


    def coverage_statistics(self):
        cov = coverage.Coverage(branch=True, omit=self.coverage_omit)
        total_lines = 0
        executed_lines = 0
        executed_branches = 0
        missing_lines = {}
        for file in self.global_execution_coverage.measured_files():
            _, executable_lines, _, _ = cov.analysis(file)

            # total_lines -1 to discard the 'def xx():' line
            total_lines += (len(set(executable_lines)) - 1)
            executed_lines += len(set(self.global_execution_coverage.lines(file)))
            executed_branches += len(set(self.global_execution_coverage.arcs(file)))

            # executable_lines starting from 1 do discard the 'def xx():' line
            m_lines = []
            for line in set(executable_lines[1:]):
                if line not in self.global_execution_coverage.lines(file):
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
