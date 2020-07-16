# Copyright: see copyright.txt

import logging
import global_var

log = logging.getLogger("ct.con.bool")

class ConcolicBool:
    def __init__(self, expr, value=None):
        self.expr = expr
        if value is not None:
            self.value = value
            self.hasvar = True
        else:
            self.value = self.expr
            self.hasvar = False
        log.debug("  ConBool, value %s, expr: %s" % (value, expr))

    def to_formula(self):
        expr = self.expr
        formula = self._to_formula(expr)
        return formula

    def _to_formula(self, expr):
        if isinstance(expr, list):
            formula = "( "
            for exp in expr:
                formula += self._to_formula(exp) + " "
            return formula + " )"
        else:
            if isinstance(expr, int):
                if expr < 0:
                    ret = "(- %s)" % -expr
                else:
                    ret = str(expr)
                return ret
            else:
                return str(expr)

    def get_concrete(self):
        return self.value
    
    # def compare_op(self, operator, other):
    #     val_l = self.value
    #     val_r = other.value
    #     if operator == "==":
    #         value = val_l == val_r
    #         expr = ["=", self.expr, other.expr]
    #     elif operator == "!=":
    #         value = val_l != val_r
    #         expr = ['not', ["=", self.expr, other.expr]]
    #     elif operator == ">":
    #         value = val_l > val_r
    #         expr = [operator, self.expr, other.expr]
    #     elif operator == "<":
    #         value = val_l < val_r
    #         expr = [operator, self.expr, other.expr]
    #     elif operator == ">=":
    #         value = val_l >= val_r
    #         expr = [operator, self.expr, other.expr]
    #     elif operator == "<=":
    #         value = val_l <= val_r
    #         expr = [operator, self.expr, other.expr]
    #     else:
    #         return None

    #     return ConcolicBool(expr, value)

    def symbolic_eq(self, other):
        return self._eq_worker(self.expr, other.expr)

    def _eq_worker(self, expr1, expr2):
        if isinstance(expr1, list):
            if not isinstance(expr2, list):
                return False
            else:
                if len(expr1) != len(expr2):
                    return False
                for i in range(len(expr1)):
                    if not self._eq_worker(expr1[i], expr2[i]):
                        return False
                return True
        else:
            return expr1 == expr2

    # def __eq__(self, other):
    #     if self.value != other.value:
    #         return False
    #     else:
    #         return self._eq_worker(self.expr, other.expr)

    # # TODO
    # def __or__(self, other):
    #     value = self.value | other.value
    #     expr = ["and", self.expr, other.expr]
    #     return ConcolicBool(expr, value)

    # # TODO
    # def __xor__(self, other):
    #     value = self.value ^ other.value
    #     expr = ["xor", self.expr, other.expr]
    #     return ConcolicBool(expr, value)

    # # TODO
    # def __and__(self, other):
    #     value = self.value & other.value
    #     expr = ["and", self.expr, other.expr]
    #     return ConcolicBool(expr, value)

    # For bool type
    def negate(self):
        raise NotImplementedError
        self.value = not self.value
        if True: # :
            self.expr = ['not', self.expr]
        else:
            self.expr = self.value

    def __str__(self):
        return "{ConType, value: %s, expr: %s)" % (self.value, self.expr)

    def __bool__(self):
        if self.hasvar:
            global_var.global_engine.path.which_branch(self)
        return self.value

    def __index__(self):
        from conbyte.concolic_types.concolic_int import ConcolicInt
        return ConcolicInt(int.__int__(self.value))

    # custom method to get the primitive value
    def parent(self):
        return self.value
