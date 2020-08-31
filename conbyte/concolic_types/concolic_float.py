# Copyright: copyright.txt

import logging
from conbyte.concolic_types.concolic import Concolic, MetaFinal
from conbyte.global_utils import py2smt, unwrap

# log = logging.getLogger("ct.con.float")

"""
Classes:
    ConcolicFloat
"""

class ConcolicFloat(float, Concolic, metaclass=MetaFinal):
    def __new__(cls, value, expr=None, engine=None):
        assert type(value) is float
        obj = super().__new__(cls, value)
        obj.expr = expr if expr is not None else py2smt(value)
        obj.engine = engine if engine is not None else Concolic._find_engine_in_expression(expr)
        # if isinstance(obj.expr, list):
        #     obj.expr = global_utils.add_extended_vars_and_queries('Real', obj.expr)
        # log.debug("  ConFloat, value: %s, expr: %s" % (obj, obj.expr))
        return obj

    def __int__(self):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        value = float.__int__(self)
        return ConcolicInt(value, ['to_int', self])

    def __truediv__(self, other):
        if not isinstance(other, ConcolicFloat): other = ConcolicFloat(other)
        value = float.__float__(self) / float.__float__(other)
        expr = ['/', self, other]
        return ConcolicFloat(value, expr)
