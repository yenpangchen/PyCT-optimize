# Copyright - see copyright.txt

class Predicate:
    def __init__(self, expr, value):
        self.expr = expr
        self.value = value

    def __eq__(self, other): # 簡單來說就是 "布林值" 和 "expression" 都要一樣！
        if isinstance(other, Predicate):
            res = self.value == other.value and self._eq_worker(self.expr, other.expr)
            return res
        else:
            return False

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

    def get_formula(self):
        formula =  self._get_formula(self.expr)
        if self.value:
            return "(assert " + formula + ")\n"
        else:
            return "(assert (not " + formula + "))\n"

    def _get_formula(self, expr):
        if isinstance(expr, list):
            formula = "( "
            for exp in expr:
                formula += self._get_formula(exp) + " "
            return formula + " )"
        else:
            if isinstance(expr, int):
                if expr < 0:
                    ret = "(- %s)" % -expr
                else:
                    ret = str(int.__int__(expr))
                return ret
            else:
                return str(expr)

    def __str__(self):
        return "Result: %s\tExpr: %s" % (self.value, self.expr)
