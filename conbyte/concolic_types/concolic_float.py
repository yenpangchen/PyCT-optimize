# Copyright: copyright.txt

from conbyte.expression import Expression
# import conbyte.global_utils
# import logging

# log = logging.getLogger("ct.con.float")

"""
Classes:
    ConcolicFloat
"""

class ConcolicFloat(float):
    def __new__(cls, value: float, expr_engine: Expression=None):
        return float.__new__(cls, value)

    def __init__(self, value: float, expr_engine: Expression=None):
        self.engine = None
        if expr_engine:
            self.expr = expr_engine.expr
            self.engine = expr_engine.engine
        else:
            self.expr = value
        # if isinstance(self.expr, list):
        #     self.expr = global_utils.add_extended_vars_and_queries('Real', self.expr)
        # log.debug("  ConFloat, value: %s, expr: %s" % (self, self.expr))

    def __int__(self):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        value = float.__int__(self)
        if self.engine:
            return ConcolicInt(value, Expression(['to_int', self.expr], self.engine))
        else:
            return ConcolicInt(value)

    def __truediv__(self, other):
        if not isinstance(other, ConcolicFloat): other = ConcolicFloat(other)
        value = float.__float__(self) / float.__float__(other)
        if self.engine:
            expr = ['/', self.expr, other.expr]
            return ConcolicFloat(value, Expression(expr, self.engine))
        elif other.engine:
            expr = ['/', self.expr, other.expr]
            return ConcolicFloat(value, Expression(expr, other.engine))
        else:
            return ConcolicFloat(value)
