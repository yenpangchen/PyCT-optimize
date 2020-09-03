# Copyright: see copyright.txt

import logging
from conbyte.concolic.concolic import Concolic, MetaFinal
from conbyte.utils import ConcolicObject, py2smt, unwrap
from conbyte.solver import Solver

log = logging.getLogger("ct.con.float")

class ConcolicFloat(float, Concolic, metaclass=MetaFinal):
    def __new__(cls, value, expr=None, engine=None):
        assert type(value) is float
        obj = super().__new__(cls, value)
        obj.engine = engine if engine is not None else Solver._expr_has_engines_and_equals_value(expr, value)
        obj.value = py2smt(value)
        obj.expr = expr if expr is not None and obj.engine is not None else obj.value
        log.debug(f"  ConFloat, value: {value}, expr: {obj.expr}")
        return obj

    def __truediv__(self, other): # <slot wrapper '__truediv__' of 'float' objects>
        log.debug("  ConFloat, __truediv__ is called")
        value = super().__truediv__(unwrap(other))
        if isinstance(other, Concolic):
            if hasattr(other, '__float2__'): other = other.__float2__()
        else:
            try: other = float(other)
            except: other = 1.0
            other = self.__class__(other)
        expr = ['/', self, other]
        return ConcolicObject(value, expr)

    ################################################################
    # Other helper methods are implemented in the following section.
    ################################################################

    def __float2__(self):
        log.debug("  ConFloat, __float2__ is called")
        return self

    def __int2__(self):
        log.debug("  ConFloat, __int2__ is called")
        value = super().__int__()
        expr = ['+', ['to_int', self], ['ite', ['and', ['<', self, '0'], ['not', ['is_int', self]]], '1', '0']]
        # Please note that ['to_int', -2.5] evaluates to -3 in smtlib2, but int(-2.5) evaluates to -2 in Python!
        return ConcolicObject(value, expr)
