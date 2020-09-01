# Copyright: see copyright.txt

import logging
from conbyte.concolic_types.concolic import Concolic, MetaFinal
from conbyte.global_utils import ConcolicObject, py2smt, unwrap

log = logging.getLogger("ct.con.bool")

class ConcolicBool(int, Concolic, metaclass=MetaFinal):
    def __new__(cls, value, expr=None, engine=None):
        if value == 0: value = False # special handling for pickling
        if value == 1: value = True # special handling for pickling
        assert type(value) is bool
        obj = super().__new__(cls, value)
        obj.expr = expr if expr is not None else py2smt(value)
        obj.engine = engine if engine is not None else Concolic._find_engine_in_expression(expr)
        # if isinstance(self.expr, list):
        #     self.expr = conbyte.global_utils.add_extended_vars_and_queries('Bool', self.expr)
        log.debug(f"  ConBool, value: {value}, expr: {obj.expr}")
        return obj

    def __bool__(self): # <slot wrapper '__bool__' of 'int' objects>
        log.debug("  ConBool, __bool__ is called")
        if self.engine: # Please note that this is the only place where branches are generated.
            self.engine.path.which_branch(self)
        return super().__bool__()

    def __xor__(self, other): # <slot wrapper '__xor__' of 'bool' objects>
        log.debug("  ConBool, __xor__ is called")
        value = unwrap(self).__xor__(unwrap(other))
        # Note that our concolic bool in fact inherits from 'int' class, so calling super().__xor__(...)
        # is actually calling int's implementation and may not be what we want.
        if isinstance(other, Concolic):
            if hasattr(other, '__bool2__'): other = other.__bool2__()
        else:
            try: other = bool(other)
            except: other = False
            other = self.__class__(other)
        expr = ['xor', self, other]
        return ConcolicObject(value, expr)

    ################################################################
    # Other helper methods are implemented in the following section.
    ################################################################

    def __bool2__(self):
        log.debug("  ConBool, __bool2__ is called")
        return self

    def __float2__(self):
        log.debug("  ConBool, __float2__ is called")
        value = super().__float__()
        expr = ["ite", self, "1.0", "0.0"]
        return ConcolicObject(value, expr)

    def __int2__(self):
        log.debug("  ConBool, __int2__ is called")
        value = super().__int__()
        expr = ["ite", self, "1", "0"]
        return ConcolicObject(value, expr)
