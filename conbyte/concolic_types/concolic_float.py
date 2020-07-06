# Copyright: copyright.txt
import logging

log = logging.getLogger("ct.con.float")

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
        # log.debug("  ConFloat, value: %s, expr: %s" % (self, self.expr)) # not fixed yet

    def __int__(self):
        return ConcolicInteger(['to_int', self.expr], float.__int__(self))

    def __truediv__(self, other):
        assert isinstance(other, ConcolicFloat)
        expr = ['/', self.expr, other.expr]
        value = float.__float__(self) / float.__float__(other)
        return ConcolicFloat(expr, value)
