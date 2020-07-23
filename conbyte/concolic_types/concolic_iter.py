# from ..utils import *
# from .concolic_int import *
# from .concolic_str import *
# from .concolic_list import *
# from .concolic_map import *


# class ConcolicIter():
#     def __init__(self, target):
#         self.target = target
#         if isinstance(target, ConcolicRange):
#             self.index = None
#         else:
#             self.index = ConcolicInt(0)

#     def next_iter(self):
#         target = self.target
#         if isinstance(target, ConcolicRange):
#             return target.next_iter()
#         else:
#             ret = None
#             if isinstance(target, ConcolicStr):
#                 length = target.len()
#                 cond_val = self.index.value < length.value
#                 cond_expr = ["<", self.index.expr, length.expr]
#                 condition = ConcolicBool(cond_val, cond_expr)
#                 if cond_val:
#                     ret = target.get_index(self.index)
#             elif isinstance(target, ConcolicList):
#                 length = target.len().value
#                 cond_val = self.index.value < length
#                 condition = ConcolicBool(cond_val, "nil")
#                 if cond_val:
#                     ret = target.get_index(self.index)

#             elif isinstance(target, ConcolicMap):
#                 length = target.len().value
#                 cond_val = self.index.value < length
#                 condition = ConcolicBool(cond_val, "nil")
#                 if cond_val:
#                     ret = target.get_iter_at(self.index)
            
#             self.index += ConcolicInt(1)
#             return condition, ret
