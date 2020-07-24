# Copyright: copyright.txt
import conbyte.global_utils
# import logging

# log = logging.getLogger("ct.con.float")

"""
Classes:
    ConcolicFloat
"""

class ConcolicFloat(float):
    def __new__(cls, value, expr=None):
        return float.__new__(cls, value)

    def __init__(self, value, expr=None):
        self.hasvar = expr is not None
        if expr is None:
            self.expr = value
        else:
            self.expr = expr
            # if isinstance(self.expr, list):
            #     self.expr = global_utils.add_extended_vars_and_queries('Real', self.expr)
        # log.debug("  ConFloat, value: %s, expr: %s" % (self, self.expr)) # not fixed yet

    def __int__(self):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        value = float.__int__(self)
        if self.hasvar:
            return ConcolicInt(value, ['to_int', self.expr])
        else:
            return ConcolicInt(value)

    def __truediv__(self, other):
        if not isinstance(other, ConcolicFloat): other = ConcolicFloat(other)
        value = float.__float__(self) / float.__float__(other)
        if self.hasvar or other.hasvar:
            expr = ['/', self.expr, other.expr]
            return ConcolicFloat(value, expr)
        else:
            return ConcolicFloat(value)
