# Copyright: copyright.txt
from .concolic_bool import *

log = logging.getLogger("ct.con.int")

"""
Classes:
    ConcolicInt
    ConcolicRange
"""

class ConcolicInt(int):
    def __new__(cls, expr, value=None): # maybe decorator required?
        if value is not None:
            return int.__new__(cls, value)
        else:
            return int.__new__(cls, expr.__int__())

    def __init__(self, expr, value=None): # maybe decorator required?
        self.expr = expr
        self.hasvar = (value is not None)
        # log.debug("  ConInt, value: %s, expr: %s" % (self, self.expr))

    def __abs__(self):
        value = int.__int__(self).__abs__()
        if self.hasvar:
            expr = ["ite", [">=", self.expr, 0], self.expr, ["-", 0, self.expr]]
            return ConcolicInt(expr, value)
        else:
            return ConcolicInt(value)

    def __bool__(self):
        return int.__bool__(self)
        raise NotImplementedError

    def __ceil__(self):
        if self.hasvar:
            return self
        else:
            return ConcolicInt(int.__int__(self))

    def __divmod__(self, value):
        return int.__int__(self).__divmod__(value)
        raise NotImplementedError

    def __eq__(self, other):
        value = int.__int__(self).__eq__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = ["=", self.expr, other.expr]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __float__(self):
        from .concolic_float import ConcolicFloat
        value = int.__float__(self)
        if self.hasvar:
            return ConcolicFloat(['to_real', self.expr], value)
        else:
            return ConcolicFloat(value)

    def __floor__(self):
        if self.hasvar:
            return self
        else:
            return ConcolicInt(int.__int__(self).__floor__())

    def __format__(self, format_spec):
        raise NotImplementedError

    def __ge__(self, other):
        value = int.__int__(self).__ge__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = [">=", self.expr, other.expr]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __gt__(self, other):
        value = int.__int__(self).__gt__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = [">", self.expr, other.expr]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __hash__(self):
        return hash(int.__int__(self))

    def __index__(self):
        raise NotImplementedError
        # return int.__int__(self) #.value

    def __int__(self):
        if self.hasvar:
            return self
        else:
            return ConcolicInt(int.__int__(self))

    def __invert__(self):
        return ConcolicInt(int.__int__(self).__invert__())
        raise NotImplementedError

    def __le__(self, other):
        value = int.__int__(self).__le__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = ["<=", self.expr, other.expr]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __lt__(self, other):
        value = int.__int__(self).__lt__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = ["<", self.expr, other.expr]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __ne__(self, other):
        value = int.__int__(self).__ne__(int.__int__(other))
        if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):
            if not isinstance(other, ConcolicInt): other = ConcolicInt(other)
            expr = ["not", ["=", self.expr, other.expr]]
            return ConcolicBool(expr, value)
        else:
            return ConcolicBool(value)

    def __neg__(self):
        value = -int.__int__(self)
        if self.hasvar:
            expr = ["-", 0, self.expr]
            return ConcolicInt(expr, value)
        else:
            return ConcolicInt(value)

    def __pos__(self):
        raise NotImplementedError

    def __pow__(self, value, mod=None):
        return int.__int__(self).__pow__(value, mod)
        raise NotImplementedError

    def __rand__(self, value):
        return int.__int__(self).__rand__(value)
        raise NotImplementedError

    def __rdivmod__(self, value):
        return int.__int__(self).__rdivmod__(value)
        raise NotImplementedError

    def __rfloordiv__(self, value):
        raise NotImplementedError

    def __rlshift__(self, value):
        return int.__int__(self).__rlshift__(value)
        raise NotImplementedError

    def __ror__(self, value):
        return int.__int__(self).__ror__(value)
        raise NotImplementedError

    def __round__(self):
        raise NotImplementedError

    def __rpow__(self, value, mod=None):
        raise NotImplementedError

    def __rrshift__(self, value):
        raise NotImplementedError

    def __rxor__(self, value):
        raise NotImplementedError

    # def __sizeof__(self):
        # raise NotImplementedError

    def __str__(self):
        from conbyte.concolic_types.concolic_str import ConcolicStr # put here to avoid circular import
        value = str(int.__int__(self))
        if self.hasvar:
            expr = ["int.to.str", self.expr]
            return ConcolicStr(expr, value)
        else:
            return ConcolicStr(value)

    def __truediv__(self, other):
        x = self.__float__()
        if isinstance(other, ConcolicInt):
            y = other.__float__()
        elif type(other) is float:
            from .concolic_float import ConcolicFloat
            y = ConcolicFloat(other)
        else:
            raise NotImplementedError
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

    # def to_bytes(self, length, byteorder, signed=False):
        # raise NotImplementedError

    # custom method to get the primitive value
    def parent(self):
        return int.__int__(self)

    def __lshift__(self, value):
        return ConcolicInt(int.__int__(self).__lshift__(value))
        raise NotImplementedError

    def __rshift__(self, value):
        raise NotImplementedError

    # def is_number(self):
    #     value = True
    #     expr = ["=", 1, 1]
    #     #return ConcolicBool(expr, value)
    #     return ConcolicBool(True, "true")

ops = [("add", "+", "+"),
       ("sub", "-", "-"),
       ("mul", "*", "*"),
       ("mod", "%", "mod"),
    #    ("truediv", "/", "div"),
       ("floordiv", "//", "div"),
       ("and", "&", "&"),
       ("or", "|", "|"),
       ("xor", "^", "^")] #,
    #    ("lshift", "<<", "bvshl"),
    #    ("rshift", ">>", "bcshr")]

def make_method(method, op, op_smt):
    code = "def %s(self, other):\n" % method
    code += "   value = int.__int__(self) %s int(other)\n" % op
    code += "   if self.hasvar or ((type(other) is ConcolicInt) and other.hasvar):\n"
    code += "      if not isinstance(other, ConcolicInt):\n"
    code += "         other = ConcolicInt(other)\n"
    code += "      expr = [\"%s\", self.expr, other.expr]\n" % op_smt
    code += "      return ConcolicInt(expr, value)\n"
    code += "   else:\n"
    code += "      return ConcolicInt(value)\n"
    locals_dict = {}
    exec(code, globals(), locals_dict)
    setattr(ConcolicInt, method, locals_dict[method])

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
    code += "   if type(other) is int:\n"
    code += "      other = ConcolicInt(other)\n"
    code += "      value = int.__int__(other) %s int.__int__(self)\n" % op
    code += "      expr = [\"%s\", other.expr, self.expr]\n" % op_smt
    code += "      if self.hasvar:\n"
    code += "         return ConcolicInt(expr, value)\n"
    code += "      else:\n"
    code += "         return ConcolicInt(value)\n"
    code += "   else:\n"
    code += "      value = other %s int.__int__(self)\n" % op
    code += "      if type(value) is int:\n"
    code += "         return ConcolicInt(value)\n"
    code += "      else:\n"
    code += "         return value\n"
    locals_dict = {}
    exec(code, globals(), locals_dict)
    setattr(ConcolicInt, method, locals_dict[method])

for (name, op, op_smt) in rops:
    method = "__%s__" % name
    make_rmethod(method, op, op_smt)

class ConcolicRange: #():
    def __init__(self, start, end=None, step=None):
        if end is None:
            self.start = 0 #ConcolicInt(0)
            self.end = start
        else:
            self.start = start
            self.end = end
        if step is None:
            self.step = 1 #ConcolicInt(1)
        else:
            self.step = step
        # See if the args violates range()
        range(self.start, self.end, self.step)
        if not isinstance(self.start, ConcolicInt): self.start = ConcolicInt(self.start)
        if not isinstance(self.end, ConcolicInt): self.end = ConcolicInt(self.end)
        if not isinstance(self.step, ConcolicInt): self.step = ConcolicInt(self.step)
        self.current = self.start

    def __iter__(self):
        while True:
            if self.step > 0:
                if self.current < self.end:
                    result = self.current
                    self.current += self.step
                    yield result
                else:
                    break
            else: # self.step < 0
                if self.current > self.end:
                    result = self.current
                    self.current += self.step
                    yield result
                else:
                    break

    # def next_iter(self):
    #     if self.step.value > 0:
    #         cond_val = self.current.value < self.end.value
    #         cond_exp = "nil"
    #     else:
    #         cond_val = self.current.value > self.end.value
    #         cond_exp = "nil"

    #     if cond_val:
    #         ret = self.current
    #         self.current += self.step
    #     else:
    #         ret = None
    #     return ConcolicBool(cond_exp, cond_val), ret

    # def __str__(self):
    #     return "(Inter s: %s, e: %s, c: %s, step: %s)" % (self.start, self.end, self.current, self.step)

    # def reverse(self):
    #     self.step.negate()
    #     tmp = self.end + self.step
    #     self.end  = self.start + self.step
    #     self.start = tmp
    #     self.current = self.start
