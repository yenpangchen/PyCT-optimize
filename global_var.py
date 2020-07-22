global_engine = None
extend_vars = dict()
extend_queries = []
num_of_extend_vars = 0

from conbyte.concolic_types.concolic_int import ConcolicInt, ConcolicRange
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.concolic_types.concolic_list import ConcolicList
def upgrade(x):
    if type(x) is int: return ConcolicInt(x)
    if type(x) is str: return ConcolicStr(x)
    raise NotImplementedError
def downgrade(x):
    if type(x) is ConcolicInt: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    if type(x) in [int, str]: return x
    raise NotImplementedError
