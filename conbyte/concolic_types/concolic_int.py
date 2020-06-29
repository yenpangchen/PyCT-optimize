# Copyright: copyright.txt
from .concolic_type import *
import global_var

log = logging.getLogger("ct.con.int")

"""
Classes:
    ConcolicInteger
    Concolic_range
"""

class ConcolicInteger(int):
    def __new__(cls, expr, value=None):
        if value is not None:
            return int.__new__(cls, value)
        else:
            return int.__new__(cls, int(expr))

    def __init__(self, expr, value=None):
        self.expr = expr
        log.debug("  ConInt, value: %s, expr: %s" % (self, self.expr))

    def __ge__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = [">=", self.expr, other.expr]
        value = int(self) >= int(other)
        return ConcolicType(expr, value)

    def __gt__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = [">", self.expr, other.expr]
        value = int(self) > int(other)
        return ConcolicType(expr, value)

    def __lt__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = ["<", self.expr, other.expr]
        value = int(self) < int(other)
        return ConcolicType(expr, value)

    def __eq__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = ["=", self.expr, other.expr]
        value = int(self) == int(other)
        return ConcolicType(expr, value)

    def __hash__(self):
        return hash(int.__int__(self))

    # def __index__(self):
    #     return int.__int__(self) #.value

    # def __int__(self):
    #     return self.value

    # def __str__(self):
        # return "{ConInt, value: %s, expr: %s)" % (int(self), self.expr)

    # def negate(self):
    #     self.value = -self.value
    #     self.expr = ["-", 0, self.expr]

    # def get_str(self):
    #     value = str(self.value)
    #     expr = ["int.to.str", self.expr]
    #     return expr, value

    def __abs__(self):
        value = abs(int(self))
        expr = ["ite", [">=", self.expr, 0], self.expr, ["-", 0, self.expr]]
        return ConcolicInteger(expr, value)

    # def int(self):
    #     return self.value

    # def is_number(self):
    #     value = True
    #     expr = ["=", 1, 1]
    #     #return ConcolicType(expr, value)
    #     return ConcolicType(True, "true")

ops = [("add", "+", "+"),
       ("sub", "-", "-"),
       ("mul", "*", "*"),
       ("mod", "%", "mod"),
       ("truediv", "/", "div"),
       ("floordiv", "//", "div"),
       ("and", "&", "&"),
       ("or", "|", "|"),
       ("xor", "^", "^"),
       ("lshift", "<<", "bvshl"),
       ("rshift", ">>", "bcshr")]

def make_method(method, op, op_smt):
    code = "def %s(self, other):\n" % method
    # code += "   if not isinstance(other, ConcolicInteger):\n"
    # code += "      other = ConcolicInteger(other)\n"
    code += "   assert isinstance(other, ConcolicInteger)\n"
    code += "   value = int(self) %s int(other)\n" % op
    code += "   expr = [\"%s\", self.expr, other.expr]\n" % op_smt
    code += "   return ConcolicInteger(expr, value)"
    locals_dict = {}
    exec(code, globals(), locals_dict)
    setattr(ConcolicInteger, method, locals_dict[method])

for (name, op, op_smt) in ops:
    method = "__%s__" % name
    make_method(method, op, op_smt)
    # rmethod = "__r%s__" % name
    # make_method(rmethod, op, op_smt)

rops = [("radd", "+", "+"),
       ("rsub", "-", "-"),
       ("rmul", "*", "*"),
       ("rmod", "%", "mod"),
       ("rtruediv", "/", "div")]

def make_rmethod(method, op, op_smt):
    code = "def %s(self, other):\n" % method
    code += "   return NotImplemented\n"
    # code += "   raise NotImplementedError\n"
    # code += "   if not isinstance(other, ConcolicInteger):\n"
    # code += "      other = ConcolicInteger(other)\n"
    # code += "   value = int(other) %s int(self)\n" % op
    # code += "   expr = [\"%s\", other.expr, self.expr]\n" % op_smt
    # code += "   return ConcolicInteger(expr, value)"
    locals_dict = {}
    exec(code, globals(), locals_dict)
    setattr(ConcolicInteger, method, locals_dict[method])

for (name, op, op_smt) in rops:
    method = "__%s__" % name
    make_rmethod(method, op, op_smt)

class Concolic_range():
    def __init__(self, start, end=None, step=None):
        if end is None:
            self.start = ConcolicInteger(0)
            self.end = start
        else:
            self.start = start
            self.end = end

        if step is None:
            self.step = ConcolicInteger(1)
        else:
            self.step = step
            # See if the args violates range()
            range(start.value, end.value, step.value)

        self.cur = self.start

    def next_iter(self):
        if self.step.value > 0:
            cond_val = self.cur.value < self.end.value
            cond_exp = "nil"
        else:
            cond_val = self.cur.value > self.end.value
            cond_exp = "nil"

        if cond_val:
            ret = self.cur
            self.cur += self.step
        else:
            ret = None
        return ConcolicType(cond_exp, cond_val), ret

    def __str__(self):
        return "(Inter s: %s, e: %s, c: %s, step: %s)" % (self.start, self.end, self.cur, self.step)

    def reverse(self):
        self.step.negate()
        tmp = self.end + self.step
        self.end  = self.start + self.step
        self.start = tmp
        self.cur = self.start
