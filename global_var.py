global_engine = None
constraints = dict()

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
    if type(x) in [int, str]: return x
    raise NotImplementedError
def _custom_range(*args, **kwargs):
    args = list(map(downgrade, args))
    if args[0] > (1<<31): return range(*args, **kwargs) # 為了效率，太多元素的 range list 我們就不做了，罪魁禍首是 _collections_abc.py
    return ConcolicList(list(map(upgrade, range(*args, **kwargs))))
# def _custom_type(*args, **kwargs):
#     res = type(*args, **kwargs)
#     print('type', res)
#     if res == ConcolicInteger: return int
#     if res == ConcolicStr:
#         # import traceback
#         # traceback.print_stack()
#         return str
#     return res
