from conbyte.predicate import Predicate
from conbyte.concolic_types.concolic_range import ConcolicRange
from conbyte.concolic_types.concolic_int import ConcolicInt
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.concolic_types.concolic_list import ConcolicList

engine = None
extend_vars = dict()
extend_queries = []
num_of_extend_vars = 0

def upgrade(x):
    if type(x) is int: return ConcolicInt(x)
    if type(x) is str: return ConcolicStr(x)
    if type(x) in [ConcolicInt, ConcolicStr]: return x
    return x
    raise NotImplementedError

def downgrade(x):
    if type(x) is ConcolicInt: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    if type(x) in [int, str]: return x
    raise NotImplementedError

def add_extended_vars_and_queries(typename, expr):
    global num_of_extend_vars, extend_vars, extend_queries
    name = 'extend_vars_' + str(num_of_extend_vars)
    extend_vars[name] = typename
    num_of_extend_vars += 1
    extend_queries.append('(assert ' + Predicate._get_formula(['=', name, expr]) + ')')
    return name
