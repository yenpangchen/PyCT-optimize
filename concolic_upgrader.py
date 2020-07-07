##############################################################################################
# Although there is no simple "post import hook" mechanism in Python 3, I've eventually found
# the very useful solution (workaround) given by the following link, and it really works!
# https://stackoverflow.com/questions/40623889/post-import-hooks-in-python-3/40624403#40624403
##############################################################################################

if 'added' not in locals():
    added = []

    from ast import NodeTransformer, Num, Call, Name, Load, Constant, parse, ImportFrom, alias, \
                    fix_missing_locations, Attribute
    import builtins
    import inspect
    import traceback

    class ConcolicUpgrader(NodeTransformer):
        def visit_Constant(self, node: Constant):
            if type(node.value) == int:
                return Call(func=Name(id='ConcolicInteger', ctx=Load()),
                            args=[Constant(value=node.value, kind=None)],
                            keywords=[])
            if type(node.value) == str:
                return Call(func=Name(id='ConcolicStr', ctx=Load()),
                            args=[Constant(value=node.value, kind=None)],
                            keywords=[])
            return node
    class ConcolicUpgrader2(NodeTransformer):
        def visit_Call(self, node: Call):
            #############################################################
            # TODO: We've not considered the case int('...', base=N) yet.
            #############################################################
            if type(node.func) == Name:
                if node.func.id == 'int':
                    node.args[0] = ConcolicUpgrader2().visit(node.args[0])
                    return Call(func=Attribute(value=node.args[0], attr='__int__', ctx=Load()),
                                args=[],
                                keywords=[])
                if node.func.id == 'str':
                    node.args[0] = ConcolicUpgrader2().visit(node.args[0])
                    return Call(func=Attribute(value=node.args[0], attr='__str__', ctx=Load()),
                                args=[],
                                keywords=[])
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
        # if module not in added and \
            # module.__name__ in ['make_server', 'pydoc']: # in XSS testing
        if module not in added and \
            not (module.__spec__.origin and module.__spec__.origin.startswith('/usr/lib/python3.8/')) and \
            module.__name__ not in ['conbyte.concolic_types.concolic_int',
                                    'conbyte.concolic_types.concolic_str']: # in simple testing
            added.append(module)
            try:
                tree = parse(inspect.getsource(module))
                tree.body.insert(0, ImportFrom(module='conbyte.concolic_types.concolic_int',
                                               names=[alias(name='ConcolicInteger', asname=None)],
                                               level=0))
                tree.body.insert(0, ImportFrom(module='conbyte.concolic_types.concolic_str',
                                               names=[alias(name='ConcolicStr', asname=None)],
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

    ###################################################################################
    # The following code snippet is just a mess when I debugged in the XSS environment.
    # Maybe it is useful in the future work.
    ###################################################################################
    # if not (hasattr(module, '__file__') and os.path.abspath(module.__file__).endswith('cpython-38-x86_64-linux-gnu.so')) and \
    # (module.__name__ in ['pydoc', 'make_server']):
    # (module.__name__ not in ['unicodedata', 'posixpath', 'genericpath', 'stat', 'zlib', 'bz2', 'lzma', '_lzma', '_compression', 'pwd', 'grp', 'posix', 'urllib', 'contextlib', 'fcntl', 'traceback', '_sysconfigdata__x86_64-linux-gnu', 'urllib.parse', 'conbyte.concolic_types.concolic_str', 'conbyte.concolic_types.concolic_int', 'inspect', 'dis', 'importlib', 'token', 'tokenize', 'html', 'http', 'socketserver', 'socket', 'selectors', 'collections.abc', 'math', 'select', 'threading', '_weakrefset', 'time', 're', 'enum', 'types', 'sre_compile', 'errno', 'warnings', 'codecs', 'encodings', 'os', 'sre_constants', 'sre_parse', 'abc', 'collections', 'operator', 'keyword', 'sys', 'heapq', '_weakref', '_collections', 'reprlib', 'builtins', 'itertools', '_thread', 'functools', '_locale', 'copyreg', 'struct', '_struct', 'quopri', 'binascii', 'email', 'io', 'string']):
