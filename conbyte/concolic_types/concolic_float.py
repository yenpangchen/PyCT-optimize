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
        value = float.__int__(self)
        if True: # :
            return ConcolicInteger(['to_int', self.expr], value)
        else:
            return ConcolicInteger(value)

    def __truediv__(self, other):
        assert isinstance(other, ConcolicFloat)
        value = float.__float__(self) / float.__float__(other)
        if True: #  or other.hasvar:
            expr = ['/', self.expr, other.expr]
            return ConcolicFloat(expr, value)
        else:
            return ConcolicFloat(value)
