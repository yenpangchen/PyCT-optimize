from conbyte.concolic_types.concolic_bool import ConcolicBool
from conbyte.concolic_types.concolic_int import ConcolicInt
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.predicate import Predicate

def upgrade(x):
    if type(x) is bool: return ConcolicBool(x)
    if type(x) is int: return ConcolicInt(x)
    if type(x) is str: return ConcolicStr(x)
    return x

def downgrade(x):
    if type(x) is ConcolicBool: return x.parent()
    if type(x) is ConcolicInt: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    if type(x) is list: x = list(map(downgrade, x))
    return x

def add_extended_vars_and_queries(typename, expr, engine):
    name = 'extend_vars_' + str(engine.num_of_extend_vars)
    engine.extend_vars[name] = typename
    engine.num_of_extend_vars += 1
    engine.extend_queries.append('(assert ' + Predicate._get_formula(['=', name, expr]) + ')')
    return name
