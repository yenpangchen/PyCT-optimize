import functools, importlib, inspect

def _int(obj):
    from conbyte.concolic import Concolic
    if isinstance(obj, Concolic) and hasattr(obj, '__int2__'): return obj.__int2__()
    return int(obj)

def _str(obj):
    from conbyte.concolic import Concolic
    if isinstance(obj, Concolic) and hasattr(obj, '__str2__'): return obj.__str2__()
    return str(obj)

def _is(obj1, obj2):
    from conbyte.concolic import Concolic
    from conbyte.utils import unwrap
    if obj1 is obj2: return True
    if isinstance(obj1, Concolic): obj1 = unwrap(obj1)
    if isinstance(obj2, Concolic): obj2 = unwrap(obj2)
    return obj1 is obj2

def ConcolicObject(value, expr=None, engine=None):
    from conbyte.concolic.bool import ConcolicBool
    from conbyte.concolic.float import ConcolicFloat
    from conbyte.concolic.int import ConcolicInt
    from conbyte.concolic.str import ConcolicStr
    if type(value) is bool: return ConcolicBool(value, expr, engine)
    if type(value) is float: return ConcolicFloat(value, expr, engine)
    if type(value) is int: return ConcolicInt(value, expr, engine)
    if type(value) is str: return ConcolicStr(value, expr, engine)
    if isinstance(value, list): # TODO: Are there other types of mutable sequences? What about "slice"?
        return list(map(ConcolicObject, value))
    return value

def unwrap(x): # call primitive's casting function to avoid getting stuck when the concolic's function is modified.
    from conbyte.concolic.bool import ConcolicBool
    from conbyte.concolic.float import ConcolicFloat
    from conbyte.concolic.int import ConcolicInt
    from conbyte.concolic.str import ConcolicStr
    if type(x) is ConcolicBool: return bool.__bool__(x)
    if type(x) is ConcolicFloat: return float.__float__(x)
    if type(x) is ConcolicInt: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    if isinstance(x, list): # TODO: Are there other types of mutable sequences? What about "slice"?
        return list(map(unwrap, x))
    return x

def py2smt(x): # convert the Python object into the smtlib2 string constant
    if type(x) is bool: return 'true' if x else 'false'
    if type(x) in (float, int): return '(- ' + str(-x) + ')' if x < 0 else str(x)
    if type(x) is str:
        x = x.replace("\\", "\\\\").replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t").replace('"', '""')
        x_new = ""
        for ch in x:
            if ord(ch) > 127: # unicode characters
                x_new += '\\u{' + str(hex(ord(ch)))[2:] + '}'
            else:
                x_new += ch
        x = '"' + x_new + '"' # 這一步很重要，因為 SMT solver 分不清楚 var name 和 string const 的差別，所以必須藉由在兩側加上雙引號的方式去區別兩者！
        return x
    raise NotImplementedError

def get_funcobj_from_modpath_and_funcname(modpath, funcname):
    try:
        class_object = importlib.import_module(modpath)
        while '.' in funcname:
            class_object = getattr(class_object, funcname.split('.')[0])
            funcname = funcname.split('.')[1]
        func = getattr(class_object, funcname)
        if len(list(inspect.signature(func).parameters)) > 0:
            if list(inspect.signature(func).parameters)[0] == 'cls':
                func = functools.partial(func, class_object)
            elif list(inspect.signature(func).parameters)[0] == 'self':
                try: func = functools.partial(func, class_object())
                except: pass # class_object() requires some arguments we don't know
        return func
    except Exception as e:
        print(e); import traceback; traceback.print_exc()#; raise e
        return None
