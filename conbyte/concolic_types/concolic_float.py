# Copyright: copyright.txt
# import logging

# log = logging.getLogger("ct.con.float")

"""
Classes:
    ConcolicFloat
"""

class ConcolicFloat(float):
    def __new__(cls, expr, value=None): # maybe decorator required?
        if value is not None:
            return float.__new__(cls, value)
        else:
            return float.__new__(cls, float(expr))

    def __init__(self, expr, value=None): # maybe decorator required?
        self.expr = expr
        self.hasvar = (value is not None)
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
            return ConcolicFloat(expr, value)
        else:
            return ConcolicFloat(value)
