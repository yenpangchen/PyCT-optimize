##############################################################################################
# Although there is no simple "post import hook" mechanism in Python 3, I've eventually found
# the very useful solution (workaround) given by the following link, and it really works!
# https://stackoverflow.com/questions/40623889/post-import-hooks-in-python-3/40624403#40624403
##############################################################################################

if 'added' not in locals():
    added = []

    from ast import NodeTransformer, Num, Call, Name, Load, Constant, parse, ImportFrom, alias, \
                    fix_missing_locations, Attribute, List
    import builtins
    import inspect
    import traceback

    class ConcolicUpgrader(NodeTransformer):
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
    class ConcolicUpgrader2(NodeTransformer):
        def visit_Call(self, node: Call):
            for i in range(len(node.args)):
                node.args[i] = ConcolicUpgrader2().visit(node.args[i])
            if type(node.func) == Name:
                if node.func.id == 'int':
                    #############################################################
                    # TODO: We've not considered the case int('...', base=N) yet.
                    #############################################################
                    if len(node.args) == 1:
                        return Call(func=Attribute(value=node.args[0], attr='__int__', ctx=Load()),
                                    args=[],
                                    keywords=[])
                    else:
                        return node
                if node.func.id == 'str':
                    return Call(func=Attribute(value=node.args[0], attr='__str__', ctx=Load()),
                                args=[],
                                keywords=[])
                if node.func.id == 'range':
                    node.func.id = '_custom_range'
                #if node.func.id == 'type':
                #    node.func.id = '_custom_type'
            return node
        def visit_List(self, node: List):
            for i in range(len(node.elts)):
                node.elts[i] = ConcolicUpgrader2().visit(node.elts[i])
            return Call(func=Name(id='ConcolicList', ctx=Load()),
                        args=[node],
                        keywords=[])
        def visit_Assign(self, node):
            node.value = ConcolicUpgrader2().visit(node.value)
            return node

    ###############################################################
    # To wrap the builtin import function, we store it into another
    # variable first so that it can still be used later.
    ###############################################################
    _builtin_import = builtins.__import__

    def _wrap_import(name, globals=None, locals=None, fromlist=(), level=0):
        #####################################################################
        # We import modules with the builtin mechanism in this first section,
        # and obtain the pre-fetched module here for the later modification.
        #
        # Please note that, the module has been executed here and never runs
        # again if we don't trigger it manually! Nevertheless, for an unknown
        # reason, this function should still return the (non-modified) module
        # object. If there is some exception thrown by the builtin mechanism,
        # simply throw it out and let it be handled outside.
        #####################################################################
        try:
            module = _builtin_import(
                name,
                globals=globals,
                locals=locals,
                fromlist=fromlist,
                level=level)
        except Exception as exception:
            raise exception
        #####################################################################

        #######################################################################
        # This section aims to replace all primitive "constants" in this loaded
        # module with their corresponding "concolic" types. We should also note
        # that, this method still cannot handle:
        # 1) default arguments of a function call
        # 2) explicit type casting from any object
        # 3) primitive variables read from outside of this program via I/O
        # It currently supports only "integers" and "strings."
        #######################################################################
        if module not in added and \
            not module.__name__ in ['global_var'] and \
            not module.__name__.startswith('conbyte') and \
            not module.__name__.startswith('importlib'):
            added.append(module)
            try:
                tree = parse(inspect.getsource(module))
                # print('外建嘻嘻', module.__spec__.origin, module.__name__)
                tree.body.insert(0, ImportFrom(module='conbyte.concolic_types.concolic_int',
                                               names=[alias(name='ConcolicInt', asname=None)],
                                               level=0))
                tree.body.insert(0, ImportFrom(module='conbyte.concolic_types.concolic_str',
                                               names=[alias(name='ConcolicStr', asname=None)],
                                               level=0))
                tree.body.insert(0, ImportFrom(module='conbyte.concolic_types.concolic_list',
                                               names=[alias(name='ConcolicList', asname=None)],
                                               level=0))
                tree.body.insert(0, ImportFrom(module='global_var',
                                               names=[alias(name='_custom_range', asname=None)],
                                               level=0))
                tree = ConcolicUpgrader().visit(tree)
                tree = ConcolicUpgrader2().visit(tree)
                fix_missing_locations(tree)
                exec(compile(tree, module.__spec__.origin, 'exec'), vars(module))
            except Exception as exception:
                ##############################################################################
                # Here we deal with the case where source codes of a module are not available.
                # The solution here may not be very complete and is just temporary.
                ##############################################################################
                # print('內建嘻嘻', module.__spec__.origin, module.__name__)
                msg = str(exception)
                if not (isinstance(exception, OSError) and msg in ['could not get source code',
                                                                   'source code not available']) \
                and not (isinstance(exception, TypeError) and msg.endswith('is a built-in module')):
                    traceback.print_exc()
                    import sys; sys.exit(0)
                ##############################################################################

        #######################################################################
        # As explained in the first section, this function should always return
        # the non-modified version of module.
        #######################################################################
        return module

    #############################################################################
    # After wrapping the builtin function, we simply plug it back to the original
    # variable so that the builtin mechanism will simply use our implementation.
    #############################################################################
    builtins.__import__ = _wrap_import
