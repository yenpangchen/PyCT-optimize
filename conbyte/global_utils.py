
from conbyte.predicate import Predicate

def upgrade(x):
    from conbyte.concolic_types.concolic_bool import ConcolicBool
    from conbyte.concolic_types.concolic_int import ConcolicInt
    from conbyte.concolic_types.concolic_str import ConcolicStr
    if type(x) is bool: return ConcolicBool(x)
    if type(x) is int: return ConcolicInt(x)
    if type(x) is str: return ConcolicStr(x)
    return x

def unwrap(x):
    from conbyte.concolic_types.concolic_bool import ConcolicBool
    from conbyte.concolic_types.concolic_int import ConcolicInt
    from conbyte.concolic_types.concolic_str import ConcolicStr
    if type(x) is ConcolicBool: return bool.__bool__(x)
    if type(x) is ConcolicInt: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    if type(x) is list: x = list(map(unwrap, x))
    return x

def add_extended_vars_and_queries(typename, expr, engine):
    name = 'extend_vars_' + str(engine.num_of_extend_vars)
    engine.extend_vars[name] = typename
    engine.num_of_extend_vars += 1
    engine.extend_queries.append('(assert ' + Predicate._get_formula(['=', name, expr]) + ')')
    return name

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