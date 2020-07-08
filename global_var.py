global_engine = None

from conbyte.concolic_types.concolic_int import ConcolicInteger
from conbyte.concolic_types.concolic_str import ConcolicStr
from conbyte.concolic_types.concolic_list import ConcolicList
def upgrade(x):
    if type(x) is int: return ConcolicInteger(x)
    if type(x) is str: return ConcolicStr(x)
    raise NotImplementedError
def downgrade(x):
    if type(x) is ConcolicInteger: return int.__int__(x)
    if type(x) is ConcolicStr: return str.__str__(x)
    raise NotImplementedError
def _custom_range(*args, **kwargs):
    args = list(map(downgrade, args))
    return ConcolicList(list(map(upgrade, range(*args, **kwargs))))
