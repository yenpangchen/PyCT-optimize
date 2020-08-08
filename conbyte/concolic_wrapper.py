##########################################################################################
# http://stupidpythonideas.blogspot.com/2015/06/hacking-python-without-hacking-python.html
# https://github.com/abarnert/floatliteralhack
##########################################################################################

import _ast, importlib, sys
from ast import NodeTransformer, Num, Call, Name, Load, Constant, parse, ImportFrom, alias, \
                fix_missing_locations, Attribute, List
import inspect
import traceback

class ConcolicWrapper(NodeTransformer):
    def visit_Constant(self, node: Constant):
        if type(node.value) == int:
            return Call(func=Name(id='ConcolicInt', ctx=Load()),
                        args=[Constant(value=node.value, kind=None)],
                        keywords=[])
        if type(node.value) == str:
            return Call(func=Name(id='ConcolicStr', ctx=Load()),
                        args=[Constant(value=node.value, kind=None)],
                        keywords=[])
        return node

class ConcolicWrapper2(NodeTransformer):
    def visit_Call(self, node: Call):
        for i in range(len(node.args)):
            node.args[i] = ConcolicWrapper2().visit(node.args[i])
        if type(node.func) == Name:
            if node.func.id == 'int':
                #############################################################
                # TODO: We've not considered the case int('...', base=N) yet.
                #############################################################
                if len(node.args) == 1:
                    return Call(func=Attribute(value=node.args[0], attr='__int__', ctx=Load()),
                                args=[],
                                keywords=[])
                return node
            if node.func.id == 'str':
                return Call(func=Attribute(value=node.args[0], attr='__str__', ctx=Load()),
                            args=[],
                            keywords=[])
            if node.func.id == 'range':
                node.func.id = 'ConcolicRange'
        return node
    # def visit_List(self, node: List):
    #     for i in range(len(node.elts)):
    #         node.elts[i] = ConcolicWrapper2().visit(node.elts[i])
    #     return Call(func=Name(id='ConcolicList', ctx=Load()),
    #                 args=[node],
    #                 keywords=[])
    def visit_Assign(self, node):
        node.value = ConcolicWrapper2().visit(node.value)
        return node

def _call_with_frames_removed(f, *args, **kwargs):
    return f(*args, **kwargs)

class ConcolicLoader(importlib.machinery.SourceFileLoader):
    def source_to_code(self, data, path):
        source = importlib.util.decode_source(data)
        tree = _call_with_frames_removed(parse, source)
        i = 0
        while len(tree.body) > i and isinstance(tree.body[i], _ast.ImportFrom) and tree.body[i].module == '__future__':
            i += 1
        tree.body.insert(i, ImportFrom(module='conbyte.concolic_types.concolic_int',
                                    names=[alias(name='ConcolicInt', asname=None)],
                                    level=0))
        tree.body.insert(i, ImportFrom(module='conbyte.concolic_types.concolic_str',
                                    names=[alias(name='ConcolicStr', asname=None)],
                                    level=0))
        tree.body.insert(i, ImportFrom(module='conbyte.concolic_types.concolic_list',
                                    names=[alias(name='ConcolicList', asname=None)],
                                    level=0))
        tree.body.insert(i, ImportFrom(module='conbyte.concolic_types.concolic_range',
                                    names=[alias(name='ConcolicRange', asname=None)],
                                    level=0))
        tree = ConcolicWrapper().visit(tree)
        tree = ConcolicWrapper2().visit(tree)
        fix_missing_locations(tree)
        return _call_with_frames_removed(compile, tree, path, 'exec')

_real_pathfinder = sys.meta_path[-1]

class ConcolicFinder(type(_real_pathfinder)):
    @classmethod
    def find_module(cls, fullname, path=None):
        spec = _real_pathfinder.find_spec(fullname, path)
        # print(fullname, path)
        # print(fullname, path, spec, sep='\n'); print()
        if not spec: return spec
        loader = spec.loader
        if not (fullname.startswith('conbyte') or fullname == 'rpyc.core.brine'):
            try:
                module = importlib.util.module_from_spec(spec)
                inspect.getsource(module) # this line is used to check if the source is available
                loader.__class__ = ConcolicLoader # if the source is available, replace it with our own
            except Exception as exception:
                msg = str(exception)
                if not (isinstance(exception, OSError) and msg in ['could not get source code',
                                                                'source code not available']) \
                and not (isinstance(exception, TypeError) and msg.endswith('is a built-in module')):
                    traceback.print_exc()
                    sys.exit(0)
        return loader

sys.meta_path[-1] = ConcolicFinder
