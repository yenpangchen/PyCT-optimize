##########################################################################################
# http://stupidpythonideas.blogspot.com/2015/06/hacking-python-without-hacking-python.html
# https://github.com/abarnert/floatliteralhack
##########################################################################################

from ast import Attribute, Call, Constant, Import, ImportFrom, Load, Name, NodeTransformer, alias, fix_missing_locations, parse
import importlib, inspect, sys, traceback
from conbyte.concolic.concolic import Concolic
from conbyte.concolic.int import ConcolicInt
from conbyte.concolic.str import ConcolicStr

#################################################################
# It is extremely important to note that node.args[i] may contain
# subroutines! That is to say, if we want to replace the original
# statement with another one, we must ensure each of node.args[i]
# appears only once in our new statement.
#################################################################

# def _type(obj):
#     res = type(obj)
#     if res is ConcolicInt: return int
#     if res is ConcolicStr: return str
#     return res

def _int(obj):
    if isinstance(obj, Concolic) and hasattr(obj, '__int2__'): return obj.__int2__()
    return int(obj)

class ConcolicWrapper(NodeTransformer):
    def visit_Constant(self, node: Constant):
        if isinstance(node.value, bool): # Note this type must be placed before "int."
            return Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='bool', ctx=Load()), attr='ConcolicBool', ctx=Load()), args=[node], keywords=[])
        if isinstance(node.value, float):
            return Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='float', ctx=Load()), attr='ConcolicFloat', ctx=Load()), args=[node], keywords=[])
        if isinstance(node.value, int):
            return Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='int', ctx=Load()), attr='ConcolicInt', ctx=Load()), args=[node], keywords=[])
        if isinstance(node.value, str):
            return Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='str', ctx=Load()), attr='ConcolicStr', ctx=Load()), args=[node], keywords=[])
        return node

class ConcolicWrapper2(NodeTransformer):
    def visit_Call(self, node: Call):
        for i in range(len(node.args)):
            node.args[i] = ConcolicWrapper2().visit(node.args[i])
        if isinstance(node.func, Name):
            if node.func.id == 'int':
                if len(node.args) == 1: # TODO: We've not considered the case int('...', base=N) yet.
                    return Call(func=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='wrapper', ctx=Load()), attr='_int', ctx=Load()), args=node.args, keywords=[])
            if node.func.id == 'str':
                return Call(func=Attribute(value=node.args[0], attr='__str__', ctx=Load()), args=[], keywords=[])
            if node.func.id == 'range':
                return Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='range', ctx=Load()), attr='ConcolicRange', ctx=Load()), args=node.args, keywords=[])
            # if node.func.id == 'type' and len(node.args) == 1:
            #     return Call(func=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='wrapper', ctx=Load()), attr='_type', ctx=Load()), args=node.args, keywords=[])
        return node
    def visit_Assign(self, node):
        node.value = ConcolicWrapper2().visit(node.value)
        return node

class ConcolicWrapper3(NodeTransformer):
    def visit_Call(self, node: Call):
        for i in range(len(node.args)):
            node.args[i] = ConcolicWrapper3().visit(node.args[i])
        if isinstance(node.func, Name): # precompute type(u"") -> str in our RPyC example
            if node.func.id == 'type' and len(node.args) == 1:
                if isinstance(node.args[0], Constant) and isinstance(node.args[0].value, str):
                    return Name(id='str', ctx=Load())
        return node

def _call_with_frames_removed(func, *args, **kwargs):
    return func(*args, **kwargs)

class ConcolicLoader(importlib.machinery.SourceFileLoader):
    def source_to_code(self, data, path):
        source = importlib.util.decode_source(data)
        tree = _call_with_frames_removed(parse, source)
        ####################################################################
        # special treatment for statements like "from __future__ import ..."
        tree.body = tree.body[next((i for i, x in enumerate(tree.body) if isinstance(x, ImportFrom) and x.module == '__future__'), 0):]
        i = 0
        while i < len(tree.body) and isinstance(tree.body[i], ImportFrom) and tree.body[i].module == '__future__':
            i += 1
        ####################################################################
        tree.body.insert(i, Import(names=[alias(name='conbyte.concolic.bool', asname=None)]))
        tree.body.insert(i, Import(names=[alias(name='conbyte.concolic.float', asname=None)]))
        tree.body.insert(i, Import(names=[alias(name='conbyte.concolic.int', asname=None)]))
        tree.body.insert(i, Import(names=[alias(name='conbyte.concolic.str', asname=None)]))
        tree.body.insert(i, Import(names=[alias(name='conbyte.concolic.range', asname=None)]))
        tree.body.insert(i, Import(names=[alias(name='conbyte.wrapper', asname=None)]))
        tree = ConcolicWrapper3().visit(tree)
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
        if not fullname.startswith('conbyte'):
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
