##########################################################################################
# References:
# http://stupidpythonideas.blogspot.com/2015/06/hacking-python-without-hacking-python.html
# https://github.com/abarnert/floatliteralhack
##########################################################################################

##########################################################################################
# To see the AST structure of a statement, one can use the following command. For example:
# "import ast; ast.dump(ast.parse('x = 3'))" will output:
# "Module(body=[Assign(targets=[Name(id='x', ctx=Store())], value=Constant(value=3, kind=None), type_comment=None)], type_ignores=[])"
##########################################################################################

from ast import Call, Constant, Import, ImportFrom, Name, NamedExpr, NodeTransformer, Store, alias, fix_missing_locations, parse
import importlib, inspect, sys, traceback

#########################################################################################
# ⚠ Warning: It is extremely important to note that node.args[i] may contain subroutines!
# That is to say, if we want to replace the original statement with another one, we must
# ensure each of node.args[i] appears only once in our new statement.
#########################################################################################
class ConcolicWrapperCall(NodeTransformer):
    # @staticmethod # (x) -> (x:=conbyte.utils.unwrap(x))
    # def _unwrap_name_with_named_expr(x):
    #     assert isinstance(x, Name)
    #     named_expr = parse('(x:=conbyte.utils.unwrap(x))').body[0].value
    #     named_expr.target = Name(id=x.id, ctx=Store())
    #     named_expr.value.args = [x]
    #     return named_expr

    # @staticmethod # (z:=(y:=x)) -> (z:=(y:=(x:=conbyte.utils.unwrap(x)))) or (z:=(y:=f(x))) -> (z:=(y:=conbyte.utils.unwrap(f(x))))
    # def _unwrap_rightest_in_named_expr(named_expr):
    #     while isinstance(named_expr.value, NamedExpr):
    #         named_expr = named_expr.value
    #     assert isinstance(named_expr, NamedExpr)
    #     if isinstance(named_expr.value, Name):
    #         named_expr.value = ConcolicWrapperCall._unwrap_name_with_named_expr(named_expr.value)
    #     else:
    #         call = parse('conbyte.utils.unwrap()').body[0].value; call.args = [named_expr.value]; named_expr.value = call

    def visit_Call(self, node: Call):
        for i in range(len(node.args)): # Each argument may also be a "Call"!
            node.args[i] = ConcolicWrapperCall().visit(node.args[i])
        if isinstance(node.func, Name):
            #####################################################################################
            # >>> ast.dump(ast.parse('conbyte.utils._int()'))
            # "Module(body=[Expr(value=Call(func=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='utils', ctx=Load()), attr='_int', ctx=Load()), args=[], keywords=[]))], type_ignores=[])"
            #####################################################################################
            if node.func.id == 'int':
                if len(node.args) == 1: # TODO: We've not considered the case int('...', base=N) yet.
                    call = parse('conbyte.utils._int()').body[0].value; call.args = node.args; return call
            if node.func.id == 'str':
                if len(node.args) == 1: # TODO: We've not considered the case str('...', encoding='...', errors='...') yet.
                    call = parse('conbyte.utils._str()').body[0].value; call.args = node.args; return call
            if node.func.id == 'range':
                call = parse('conbyte.concolic.range.ConcolicRange()').body[0].value; call.args = node.args; return call
            ###########################################################################
            # We want to automatically unwrap concolic objects when examining its type!
            # That is, (1) type(x) -> type(x:=conbyte.utils.unwrap(x))
            #          (2-1) type(f(x)) -> type(conbyte.utils.unwrap(f(x)))
            #          (2-2) type(5) -> type(conbyte.utils.unwrap(5))
            #          (3) type(z:=(y:=x)) -> type(z:=(y:=(x:=conbyte.utils.unwrap(x))))
            #          (4-1) type(z:=(y:=f(x))) -> type(z:=(y:=conbyte.utils.unwrap(f(x))))
            #          (4-2) type(z:=(y:=5)) -> type(z:=(y:=conbyte.utils.unwrap(5)))
            #
            # >>> ast.dump(ast.parse('type(x)'))
            # "Module(body=[Expr(value=Call(func=Name(id='type', ctx=Load()), args=[Name(id='x', ctx=Load())], keywords=[]))], type_ignores=[])"
            #
            # >>> ast.dump(ast.parse('(x:=conbyte.utils.unwrap(x))'))
            # "Module(body=[Expr(value=NamedExpr(target=Name(id='x', ctx=Store()), value=Call(func=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='utils', ctx=Load()), attr='unwrap', ctx=Load()), args=[Name(id='x', ctx=Load())], keywords=[])))], type_ignores=[])"
            #
            # >>> ast.dump(ast.parse('type(z:=(y:=x))'))
            # "Module(body=[Expr(value=Call(func=Name(id='type', ctx=Load()), args=[NamedExpr(target=Name(id='z', ctx=Store()), value=NamedExpr(target=Name(id='y', ctx=Store()), value=Name(id='x', ctx=Load())))], keywords=[]))], type_ignores=[])"
            ###############################################################################
            # if node.func.id == 'type':
            #     if len(node.args) == 1:
            #         if isinstance(node.args[0], NamedExpr):
            #             self._unwrap_rightest_in_named_expr(node.args[0])
            #         elif isinstance(node.args[0], Name):
            #             node.args = [self._unwrap_name_with_named_expr(node.args[0])]
            #         else: # may be a constant or a function call, etc. (no variable reassignment)
            #             call = parse('conbyte.utils.unwrap()').body[0].value; call.args = node.args; node.args = [call]
        return node

class ConcolicWrapperConstant(NodeTransformer):
    #####################################################################################
    # >>> ast.dump(ast.parse('conbyte.concolic.bool.ConcolicBool()'))
    # "Module(body=[Expr(value=Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='conbyte', ctx=Load()), attr='concolic', ctx=Load()), attr='bool', ctx=Load()), attr='ConcolicBool', ctx=Load()), args=[], keywords=[]))], type_ignores=[])"
    #####################################################################################
    def visit_Constant(self, node: Constant):
        if isinstance(node.value, bool): # Note this type must be placed before "int."
            call = parse('conbyte.concolic.bool.ConcolicBool()').body[0].value; call.args = [node]; return call
        if isinstance(node.value, float):
            call = parse('conbyte.concolic.float.ConcolicFloat()').body[0].value; call.args = [node]; return call
        if isinstance(node.value, int):
            call = parse('conbyte.concolic.int.ConcolicInt()').body[0].value; call.args = [node]; return call
        if isinstance(node.value, str):
            call = parse('conbyte.concolic.str.ConcolicStr()').body[0].value; call.args = [node]; return call
        return node

class ConcolicWrapperAssign(NodeTransformer):
    #####################################################
    # 1. (x = value) -> (x = ConcolicObject(value))
    # 2. (x, y = value) -> (x, y = ConcolicObject(value))
    #####################################################
    def visit_Assign(self, node):
        call = parse('conbyte.utils.ConcolicObject()').body[0].value; call.args = [node.value]; node.value = call
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
        tree.body.insert(i, Import(names=[alias(name='conbyte.utils', asname=None)]))
        tree = ConcolicWrapperCall().visit(tree)
        tree = ConcolicWrapperConstant().visit(tree)
        tree = ConcolicWrapperAssign().visit(tree)
        fix_missing_locations(tree)
        return _call_with_frames_removed(compile, tree, path, 'exec')

_real_pathfinder = sys.meta_path[-1]

class ConcolicFinder(type(_real_pathfinder)):
    @classmethod
    def find_module(cls, fullname, path=None):
        # print(fullname, path)
        spec = _real_pathfinder.find_spec(fullname, path)
        if not spec: return spec
        loader = spec.loader
        if not fullname.startswith('conbyte') and fullname not in ['rpyc.core.brine']:
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
                    sys.exit(1)
        return loader

sys.meta_path[-1] = ConcolicFinder
