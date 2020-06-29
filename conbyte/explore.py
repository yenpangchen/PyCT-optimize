import sys
import os
import logging
# import dis
import inspect
import traceback
import json
import copy

import coverage
from func_timeout import func_timeout, FunctionTimedOut

from .utils import * 
from .function import *
from .frame import *
# from .executor import *
from .path_to_constraint import *

from .concolic_types import concolic_type
from .solver import Solver 
import global_var

log = logging.getLogger("ct.explore")

# def print_inst(obj):
#     lines = dis.get_instructions(obj)
#     for line in lines:
#         log.debug(line)

class ExplorationEngine:
    mem_stack = Stack()
    call_stack = Stack()

    def __init__(self, path, filename, module, entry, ini_vars, query_store, solver_type, ss):
        # Set up import environment
        sys.path.append(path)
        self.t_module = __import__(module)
        if entry == None:
            self.entry = module
        else:
            self.entry = entry

        self.trace_into = []
        self.functions = dict()

        self.ini_vars = ini_vars
        self.symbolic_inputs = None 
        self.new_constraints = []
        self.constraints_to_solve = Queue()
        self.solved_constraints = Queue()
        self.finished_constraints = []
        self.num_processed_constraints = 0
        self.input_sets = []
        self.error_sets = []
        self.in_ret_sets = []

        # self.cov = coverage.Coverage(branch=True)#,
#                                     omit=['/mnt/d/ALAN_FOLDER/2020_研究工作/1_CODE_py-conbyte/conbyte/**',
#                                           '/mnt/d/ALAN_FOLDER/2020_研究工作/1_CODE_py-conbyte/py-conbyte.py'])
        self.global_execution_coverage = coverage.CoverageData()

        
        self.path = PathToConstraint() #lambda c: self.add_constraint(c))
        # self.executor = Executor() #self.path)

        """
        # Append builtin in trace_into
        """
        self.trace_into.append("__init__")
        self.trace_into.append("__str__")

        self.query_store = query_store
        if self.query_store is not None:
            if not os.path.isdir(self.query_store):
                raise IOError("Query folder {} not found".format(self.query_store))

        self.solver = Solver(query_store, solver_type, ss)

    # def extract(self):
    #     dis.dis(self.t_module)

    def add_constraint(self, constraint):
        self.new_constraints.append(constraint)

    def execute_instructs(self, frame):
        # Handle previous jump first
        re = None
        while frame.next_offset != None:
            instruct = frame.get_instruct(frame.next_offset)

            if frame.instructions_store.contains(instruct):
                frame.next_offset = None
                log.debug("** Back to instructions queue")
                while instruct != frame.instructions_store.top():
                    frame.instructions_store.pop()
            else:
                log.debug("** Pure counter control")
                log.debug("- instr %s %s %s %s" % (instruct.offset, instruct.opname, instruct.argval, instruct.argrepr))
                re = self.executor.execute_instr(instruct)
                if re:
                    return re

        while not frame.instructions_store.is_empty():
            frame.instructions.push(frame.instructions_store.pop())
        instructs = frame.instructions
        re = None

        while not instructs.is_empty():
            instruct = instructs.pop()
            log.debug("- instr %s %s %s %s" % (instruct.offset, instruct.opname, instruct.argval, instruct.argrepr))
            if instruct.opname == "CALL_FUNCTION":
                re = self.executor.execute_instr(instruct)
                if re is None:
                    return
            elif instruct.opname == "CALL_METHOD":
                re = self.executor.execute_instr(instruct)
                if re is None:
                    return
            else:
                re = self.executor.execute_instr(instruct)
        return re

    def get_line_instructions(self, lineno, instructions):
        instructs = []
        start_record = False
        i = 0
        for instruct in instructions:
            if start_record:
                if instruct.starts_line == None:
                    instructs.append(instruct)
                else:
                    break
            else:
                if instruct.starts_line != None:
                    if instruct.starts_line == lineno:
                        start_record = True
                        instructs.append(instruct)
            i += 1
        return instructs

    def _is_exploration_complete(self):
        num_constr = self.constraints_to_solve.q_size()
        if num_constr == 0 and self.solved_constraints.is_empty():
            return True
        else:
            return False

    def explore(self, max_iterations, timeout=None):
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
                self.num_processed_constraints += 1
            self.finished_constraints.append(selected_id)

        # self.execute_coverage()

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

        # ExplorationEngine.call_stack.sanitize()
        # ExplorationEngine.mem_stack.sanitize()
        self.path.reset(expected_path)

        execute = getattr(self.t_module, self.entry)
        # sys.settrace(self.trace_calls)
        # global_var.inputs_processed = True #False
        ###################################################
        para = inspect.signature(execute).parameters.copy()
        for a, b in zip(para.values(), init_vars):
            para[a.name] = a.replace(default=b)
        copy_vars = []
        self.symbolic_inputs = dict()
        for v in para.values():
            if isinstance(v.default, int):
                copy_vars.append(ConcolicInteger(v.name, v.default))
                self.symbolic_inputs[v.name] = 'Int'
            elif isinstance(v.default, str):
                copy_vars.append(ConcolicStr(v.name, v.default))
                self.symbolic_inputs[v.name] = 'String'
            else:
                raise NotImplementedError
        self.solver.set_variables(self.symbolic_inputs)
        ###################################################
        # self.cov = coverage.Coverage(branch=True)
        # self.cov.start()
        ret = execute(*copy_vars)
        # self.cov.stop()
        # self.global_execution_coverage.update(self.cov.get_data())
        log.info("Return: %s" % ret)
        # log.info("Return: %s" % ret.expr)

        while len(self.new_constraints) > 0:
            constraint = self.new_constraints.pop()
            constraint.inputs = self._getInputs()
            extend_var, extend_queries = dict(), [] # self.executor.get_extend()
            self.constraints_to_solve.push((constraint, extend_var, extend_queries))

        self.input_sets.append(init_vars)
        self.in_ret_sets.append({"input": init_vars, "result": ret})

        # with open('global_exploration_engine.pkl', 'wb') as w:
        #     dill.dump(self.__dict__, w)
        # sys.exit(0)

        # else: # parent process
        #     os.waitpid(pid, 0)
        #     with open('global_exploration_engine.pkl', 'rb') as r:
        #         self.__dict__.update(dill.load(r))
        #     os.remove('global_exploration_engine.pkl')

    # def execute_coverage(self):
    #     execute = getattr(self.t_module, self.entry)
    #     cov = coverage.Coverage(branch=True)
    #     for args in self.input_sets:
    #         cov.start()
    #         copy_args = copy.deepcopy(args)
    #         ret = execute(*copy_args)
    #         cov.stop()
    #         self.global_execution_coverage.update(cov.get_data())


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
        # cov = coverage.Coverage(branch=True)
        total_lines = 0
        executed_lines = 0
        executed_branches = 0
        missing_lines = {}
        # for file in self.global_execution_coverage.measured_files():
        #     _, executable_lines, _, _ = cov.analysis(file)

        #     # total_lines -1 to discard the 'def xx():' line
        #     total_lines += (len(set(executable_lines)) - 1)
        #     executed_lines += len(set(self.global_execution_coverage.lines(file)))
        #     executed_branches += len(set(self.global_execution_coverage.arcs(file)))

        #     # executable_lines starting from 1 do discard the 'def xx():' line
        #     m_lines = []
        #     for line in set(executable_lines[1:]):
        #         if line not in self.global_execution_coverage.lines(file):
        #             m_lines.append(line)
        #     if len(m_lines) > 0:
        #         missing_lines[file] = m_lines
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

    # def trace_lines(self, frame, event, arg):
    #     # frame.f_trace_opcodes = True
    #     if event != 'opcode': # 'line':
    #         return
    #     # print('>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>')
    #     import gc
    #     # print(gc.get_referents(frame))
    #     # print('TOS (python)', gc.get_referents(frame)[-1])
    #     stack = get_stack(frame)
    #     # try:
    #     #     print('TOS (C)', stack[-1])
    #     # except ValueError:
    #     #     pass
    #     # print(opname[frame.f_code.co_code[frame.f_lasti]])
    #     # print(gc.get_objects())
    #     gc.collect()
    #     # print(gc.get_referrers(frame))
    #     if gc.get_referents(frame)[-1] == 15: #isinstance(gc.get_referents(frame)[-1], list): # == 40:
    #         assert gc.get_referents(frame)[-1] == stack[-1]

    #         # print('YES!!!')
    #         # print(sizeof(stack[-1]))
    #         # print(sizeof('乾' * 100))
    #         # x = ConcolicList() # ConcolicList([60])
    #         # print('XXX', x.expr)
    #         # print('XXX', type(x))
    #         print('before', stack[-1])

    #         # bc = compile('z=0; -z', '<string>', 'exec')
    #         # from types import CodeType
    #         # bc = CodeType(bc.co_argcount,bc.co_posonlyargcount,bc.co_kwonlyargcount,bc.co_nlocals,bc.co_stacksize,bc.co_flags,b'b\x00',bc.co_consts,bc.co_names,bc.co_varnames,bc.co_filename,bc.co_name,bc.co_firstlineno,bc.co_lnotab)
    #         # bc = CodeType(0,0,0,0,1,64,b'b\x00',(None,),(),(),'<string>','<module>',1,b'\x04\x00')
    #         # exec(bc)

    #         # sub = ConcolicList(stack[-1][0])
    #         # print('sub', sub)
    #         # stack[-1].pop() # = sub # ConcolicStr('乾乾乾') #gc.get_referents(frame)[-1] #[0:2] #[10000] #ConcolicList([60]) #ConcolicList([60]) #stack[-1]) #60 #ConcolicStr('123') #ConcolicInteger(10)
    #         # for i in range(100):
    #             # stack[-1].append(i)
    #         stack[-1] = [ConcolicInteger(stack[-1])] # // (-1) #stack[-1]) #stack[-1] // (-1)
    #         # print(ConcolicList(stack[-1]).value)
    #         # stack[-1].append(ConcolicList(stack[-1]).value)
    #         # print(type(stack[-1][0]))
    #         # print(type(stack[-1][1]))
    #         print('after', stack[-1])
    #         # print('RRR', type(stack[-1]))
    #         # print(gc.get_referents(frame)[-1])
    #     # print('<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<')
    #     # return

    #     # code_object = frame.f_code
    #     # line_no = frame.f_lineno
    #     # print('     line', code_object.co_names)

    #     # c_frame = ExplorationEngine.call_stack.top()
    #     # log.debug('+ %s line %s' % (c_frame.func_name, line_no))
    #     # for instruct in self.get_line_instructions(line_no, dis.get_instructions(code_object)):
    #     #     c_frame.instructions_store.push(instruct)

    #     # is_return = self.execute_instructs(c_frame)
    #     # while is_return:
    #     #     ExplorationEngine.call_stack.pop()
    #     #     if not ExplorationEngine.call_stack.is_empty():
    #     #         c_frame = ExplorationEngine.call_stack.top()
    #     #         is_return = self.execute_instructs(c_frame)
    #     #     else:
    #     #         break

    # def trace_calls(self, frame, event, arg):
    #     # frame.f_trace_opcodes = True
    #     # return self.trace_lines
    #     if event != 'call':
    #         return
    #     code_object = frame.f_code

    #     # import inspect
    #     # if inspect.getmodule(frame.f_back) is None:
    #         # return
    #     # print('module', inspect.getmodule(frame))
    #     # print('module code', inspect.getmodule(frame).co_code)
    #     # print('source of module', inspect.getsource(inspect.getmodule(frame)))

    #     #############################################################
    #     # spec = importlib.util.find_spec(module_name, package)
    #     # source = spec.loader.get_source(module_name)
    #     # new_source = modification_func(source)
    #     module = inspect.getmodule(frame) # importlib.util.module_from_spec(spec)
    #     # print('module name', module.__name__)
    #     # sys.exit(0)
    #     #############################################################

    #     # https://stackoverflow.com/questions/52715425/get-function-signature-from-frameinfo-or-frame-in-python
    #     function_reference = [obj for obj in gc.get_referrers(code_object) if hasattr(obj, '__code__') and obj.__code__ is code_object][0]
    #     print('function:', function_reference, function_reference.__qualname__)
    #     print('filename:', code_object.co_filename)

    #     # if "/python3." in code_object.co_filename and (code_object.co_filename != '/usr/lib/python3.8/pydoc.py'
    #     # or code_object.co_filename != '/usr/lib/python3.8/sre_parse.py'):
    #         # return
    #     # print('function reference:', )
    #     # if function_reference.__qualname__ != 'ConcolicStr.__radd__':
    #     # function_id = hex(id(function_reference))
    #     # print(function_id, global_var.functions)
    #     # print(function_id in global_var.functions)
    #     # if function_id not in global_var.functions:
    #         # global_var.functions[function_id] = function_reference.__dict__ #.co_code
    #         # print(inspect.getsource(function_reference))
    #     # print('媽九', )
    #     # if len(function_reference.__qualname__.split('.')) > 1: #[0] in ['TCPServer', 'SimpleXMLRPCDispatcher', 'SimpleXMLRPCServer', 'DocXMLRPCServer', 'ConcolicStr', 'Logger']: #function_reference.__name__ in ['__new__', '__init__', '__str__', 'debug', 'isEnabledFor']:
    #         # print(inspect.ismethod(code_object))
    #         # import textwrap
    #         # print(inspect.getsource(function_reference))
    #         # b = textwrap.dedent(inspect.getsource(function_reference))
    #         # print(b)
    #         # tree = ast.parse(b)
    #     # else:
    #         # if function_reference.__name__ == '_compile':
    #         # print(inspect.getsource(function_reference))
    #     tree = ast.parse(inspect.getsource(module)) #function_reference))
    #     # print('>>>', ast.dump(tree))
    #     # sys.exit(0)
    #     tree.body.insert(0, ast.ImportFrom(module='conbyte.concolic_types.concolic_int', names=[ast.alias(name='ConcolicInteger', asname=None)], level=0))
    #     tree.body.insert(0, ast.ImportFrom(module='conbyte.concolic_types.concolic_str', names=[ast.alias(name='ConcolicStr', asname=None)], level=0))
    #     # print('>>>', ast.dump(tree))
    #     # sys.exit(0)
    #     tree = ConcolicUpgrader().visit(tree)
    #     ast.fix_missing_locations(tree)
    #     # if len(function_reference.__qualname__.split('.')) > 1: #[0] in ['TCPServer', 'SimpleXMLRPCDispatcher', 'SimpleXMLRPCServer', 'DocXMLRPCServer', 'ConcolicInteger', 'ConcolicStr', 'Logger']: #function_reference.__name__ in ['__new__', '__init__', '__str__', 'debug', 'isEnabledFor']:
    #     # code = compile(tree, "<ast>", "exec")
    #     # import types
    #     # if isinstance(code, types.CodeType):
    #     # function_reference.__code__ = compile(tree, "<ast>", "exec")
    #     codeobj = compile(tree, module.__spec__.origin, 'exec')
    #     exec(codeobj, module.__dict__)
    #     sys.modules[module.__name__] = module
    #     # else:
    #         # print('before', inspect.getsource(function_reference))
    #         # function_reference.__code__ = compile(tree, "<ast>", "exec").co_consts[0] # https://stackoverflow.com/questions/57480368/python-transforming-ast-through-function-decorators
    #         # print('after', inspect.getsource(function_reference))
    #     # else:
    #     #     function_reference.__dict__ = global_var.functions[function_id]
    #     #     del global_var.functions[function_id]
    #     # global_var.functions.append(function_reference)
    #     # func_name = code_object.co_name
    #     # print(code_object)
    #     # global_var.functions.append(frame.)
    #     # current_frame = Frame(frame, func_name)
    #     # if not ExplorationEngine.call_stack.is_empty():
    #     #     if func_name == "__init__":
    #     #         current_frame.set_locals(True)
    #     #     else:
    #     #         current_frame.set_locals(False)
    #     # else:
    #     # self.symbolic_inputs = current_frame.init_locals()

    #     # print(dir(frame))
    #     # for attr in dir(frame):
    #         # print(attr, getattr(frame, attr))
    #     # for attr in dir(code_object):
    #         # print(attr, getattr(code_object, attr))

    #     # if not global_var.inputs_processed:
    #     #     global_var.inputs_processed = True
    #     #     self.symbolic_inputs = dict() #{'a': 'Int', 'b': 'Int'}
    #     #     import ctypes
    #     #     for (k,v) in frame.f_locals.items():
    #     #         if isinstance(v, int):
    #     #             self.symbolic_inputs[k] = 'Int'
    #     #             frame.f_locals.update({k: ConcolicInteger(k, v)})
    #     #         elif isinstance(v, str):
    #     #             self.symbolic_inputs[k] = 'String'
    #     #             frame.f_locals.update({k: ConcolicStr(k, v)})
    #     #         else:
    #     #             raise NotImplementedError
    #     #         ctypes.pythonapi.PyFrame_LocalsToFast(ctypes.py_object(frame), ctypes.c_int(0))
    #     #         # Magic: https://stackoverflow.com/questions/34650744/modify-existing-variable-in-locals-or-frame-f-locals
    #     #     self.solver.set_variables(self.symbolic_inputs)

    #     # print('XX', code_object.co_consts)
    #     # current_frame.set_local()
    #     # ExplorationEngine.call_stack.push(current_frame)
    #     # return self.trace_lines
