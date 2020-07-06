# Copyright: copyright.txt
from .concolic_type import *

log = logging.getLogger("ct.con.int")

"""
Classes:
    ConcolicInteger
    Concolic_range
"""

class ConcolicInteger(int):
    def __new__(cls, expr, value=None): # maybe decorator required?
        if value is not None:
            return int.__new__(cls, value)
        else:
            return int.__new__(cls, expr.__int__())

    def __init__(self, expr, value=None): # maybe decorator required?
        self.expr = expr
        log.debug("  ConInt, value: %s, expr: %s" % (self, self.expr))

    def __abs__(self):
        value = int.__int__(self).__abs__()
        expr = ["ite", [">=", self.expr, 0], self.expr, ["-", 0, self.expr]]
        return ConcolicInteger(expr, value)

    def __bool__(self):
        raise NotImplementedError

    def __ceil__(self):
        return self

    def __divmod__(self, value):
        raise NotImplementedError

    def __eq__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = ["=", self.expr, other.expr]
        value = int.__int__(self) == int.__int__(other)
        return ConcolicType(expr, value)

    def __float__(self):
        from .concolic_float import ConcolicFloat
        return ConcolicFloat(['to_real', self.expr], int.__float__(self))

    def __floor__(self):
        return self

    def __format__(self, format_spec):
        raise NotImplementedError

    def __ge__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = [">=", self.expr, other.expr]
        value = int.__int__(self) >= int.__int__(other)
        return ConcolicType(expr, value)

    def __gt__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = [">", self.expr, other.expr]
        value = int.__int__(self) > int.__int__(other)
        return ConcolicType(expr, value)

    def __hash__(self):
        return hash(int.__int__(self))

    def __index__(self):
        raise NotImplementedError
        # return int.__int__(self) #.value

    def __int__(self):
        return self

    def __invert__(self):
        raise NotImplementedError

    def __le__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = ["<=", self.expr, other.expr]
        value = int.__int__(self) <= int.__int__(other)
        return ConcolicType(expr, value)

    def __lt__(self, other):
        # if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
        assert isinstance(other, ConcolicInteger)
        expr = ["<", self.expr, other.expr]
        value = int.__int__(self) < int.__int__(other)
        return ConcolicType(expr, value)

    def __ne__(self, other):
        assert isinstance(other, ConcolicInteger)
        expr = ["not", ["=", self.expr, other.expr]]
        value = int.__int__(self) != int.__int__(other)
        return ConcolicType(expr, value)

    def __neg__(self):
        expr = ["-", 0, self.expr]
        value = -int.__int__(self)
        return ConcolicInteger(expr, value)

    def __pos__(self):
        raise NotImplementedError

    def __pow__(self, value, mod=None):
        raise NotImplementedError

    def __rand__(self, value):
        raise NotImplementedError

    def __rdivmod__(self, value):
        raise NotImplementedError

    def __rfloordiv__(self, value):
        raise NotImplementedError

    def __rlshift__(self, value):
        raise NotImplementedError

    def __ror__(self, value):
        raise NotImplementedError

    def __round__(self):
        raise NotImplementedError

    def __rpow__(self, value, mod=None):
        raise NotImplementedError

    def __rrshift__(self, value):
        raise NotImplementedError

    def __rxor__(self, value):
        raise NotImplementedError

    def __sizeof__(self):
        return NotImplemented

    # def __str__(self): # 還沒解決 circular import ConcolicStr 的問題 ...
    #     expr = ["int.to.str", self.expr]
    #     value = str(int.__int__(self))
    #     return ConcolicStr(expr, value)

    def __truediv__(self, other):
        x = self.__float__()
        assert isinstance(other, ConcolicInteger)
        y = other.__float__()
        return x / y # operation between two concolic floats

    def __trunc__(self):
        raise NotImplementedError

    def as_integer_ratio(self):
        raise NotImplementedError

    def bit_length(self):
        raise NotImplementedError

    def conjugate(self):
        raise NotImplementedError

    @classmethod
    def from_bytes(cls, bytes, byteorder, signed=False):
        raise NotImplementedError

    def to_bytes(self, length, byteorder, signed=False):
        raise NotImplementedError

    # custom method to get the primitive value
    def parent(self):
        return int.__int__(self)

    # def is_number(self):
    #     value = True
    #     expr = ["=", 1, 1]
    #     #return ConcolicType(expr, value)
    #     return ConcolicType(True, "true")

ops = [("add", "+", "+"),
       ("sub", "-", "-"),
       ("mul", "*", "*"),
       ("mod", "%", "mod"),
    #    ("truediv", "/", "div"),
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
    code += "   value = int.__int__(self) %s int.__int__(other)\n" % op
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
    # code += "   return NotImplemented\n"
    code += "   raise NotImplementedError\n"
    # code += "   assert not isinstance(other, ConcolicInteger)\n"
    code += "   other = ConcolicInteger(other)\n"
    code += "   value = int.__int__(other) %s int.__int__(self)\n" % op
    code += "   expr = [\"%s\", other.expr, self.expr]\n" % op_smt
    code += "   return ConcolicInteger(expr, value)"
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
