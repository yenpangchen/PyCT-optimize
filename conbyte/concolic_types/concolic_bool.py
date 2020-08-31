# Copyright: see copyright.txt

import logging
from conbyte.concolic_types.concolic import Concolic, MetaFinal
from conbyte.global_utils import py2smt, unwrap

log = logging.getLogger("ct.con.bool")

class ConcolicBool(int, Concolic, metaclass=MetaFinal):
    def __new__(cls, value, expr=None, engine=None):
        assert type(value) is bool
        obj = super().__new__(cls, value)
        obj.expr = expr if expr is not None else py2smt(value)
        obj.engine = engine if engine is not None else Concolic._find_engine_in_expression(expr)
        # if isinstance(self.expr, list):
        #     self.expr = conbyte.global_utils.add_extended_vars_and_queries('Bool', self.expr)
        # log.debug("  ConBool, value %s, expr: %s" % (self.value, self.expr))
        return obj

    def __bool__(self):
        if self.engine:
            self.engine.path.which_branch(self)
        return unwrap(self)

    def __index__(self):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        value = int.__int__(unwrap(self))
        return ConcolicInt(value, ["ite", ["=", self, "true"], 1, 0])

    # TODO
    def __xor__(self, other):
        value = self.value ^ other.value
        expr = ["xor", self, other]
        return ConcolicBool(value, expr)
