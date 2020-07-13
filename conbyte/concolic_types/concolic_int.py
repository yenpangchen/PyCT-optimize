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
        self.hasvar = (value is not None)
        # log.debug("  ConInt, value: %s, expr: %s" % (self, self.expr))

    def __abs__(self):
        value = int.__int__(self).__abs__()
        if True: # 
            expr = ["ite", [">=", self.expr, 0], self.expr, ["-", 0, self.expr]]
            return ConcolicInteger(expr, value)
        else:
            return ConcolicInteger(value)

    def __bool__(self):
        return int.__bool__(self)
        raise NotImplementedError

    def __ceil__(self):
        if True: # 
            return self
        else:
            return ConcolicInteger(int.__int__(self))

    def __divmod__(self, value):
        return int.__int__(self).__divmod__(value)
        raise NotImplementedError

    def __eq__(self, other):
        value = int.__int__(self).__eq__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = ["=", self.expr, other.expr]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __float__(self):
        from .concolic_float import ConcolicFloat
        value = int.__float__(self)
        if True: # 
            return ConcolicFloat(['to_real', self.expr], value)
        else:
            return ConcolicFloat(value)

    def __floor__(self):
        if True: # 
            return self
        else:
            return ConcolicInteger(int.__int__(self).__floor__())

    def __format__(self, format_spec):
        raise NotImplementedError

    def __ge__(self, other):
        value = int.__int__(self).__ge__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = [">=", self.expr, other.expr]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __gt__(self, other):
        value = int.__int__(self).__gt__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = [">", self.expr, other.expr]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __hash__(self):
        return hash(int.__int__(self))

    def __index__(self):
        raise NotImplementedError
        # return int.__int__(self) #.value

    def __int__(self):
        if True: # 
            return self
        else:
            return ConcolicInteger(int.__int__(self))

    def __invert__(self):
        return ConcolicInteger(int.__int__(self).__invert__())
        raise NotImplementedError

    def __le__(self, other):
        value = int.__int__(self).__le__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = ["<=", self.expr, other.expr]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __lt__(self, other):
        value = int.__int__(self).__lt__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = ["<", self.expr, other.expr]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __ne__(self, other):
        value = int.__int__(self).__ne__(int.__int__(other))
        if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):
            if not isinstance(other, ConcolicInteger): other = ConcolicInteger(other)
            expr = ["not", ["=", self.expr, other.expr]]
            return ConcolicType(expr, value)
        else:
            return ConcolicType(value)

    def __neg__(self):
        value = -int.__int__(self)
        if True: # 
            expr = ["-", 0, self.expr]
            return ConcolicInteger(expr, value)
        else:
            return ConcolicInteger(value)

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
        value = str(int.__int__(self))
        if True: # 
            expr = ["int.to.str", self.expr]
            from conbyte.concolic_types.concolic_str import ConcolicStr # put here to avoid circular import
            return ConcolicStr(expr, value)
        else:
            return ConcolicStr(value)

    def __truediv__(self, other):
        x = self.__float__()
        if isinstance(other, ConcolicInteger):
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
        return ConcolicInteger(int.__int__(self) << value)
        raise NotImplementedError

    def __rshift__(self, value):
        raise NotImplementedError

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
       ("xor", "^", "^")] #,
    #    ("lshift", "<<", "bvshl"),
    #    ("rshift", ">>", "bcshr")]

def make_method(method, op, op_smt):
    code = "def %s(self, other):\n" % method
    code += "   value = int.__int__(self) %s int(other)\n" % op
    code += "   if True: #  or ((type(other) is ConcolicInteger) and other.hasvar):\n"
    code += "      if not isinstance(other, ConcolicInteger):\n"
    code += "         other = ConcolicInteger(other)\n"
    code += "      expr = [\"%s\", self.expr, other.expr]\n" % op_smt
    code += "      return ConcolicInteger(expr, value)\n"
    code += "   else:\n"
    code += "      return ConcolicInteger(value)\n"
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
    code += "   if type(other) is int: # and self.hasvar:\n"
    code += "      other = ConcolicInteger(other)\n"
    code += "      value = int.__int__(other) %s int.__int__(self)\n" % op
    code += "      expr = [\"%s\", other.expr, self.expr]\n" % op_smt
    code += "      return ConcolicInteger(expr, value)\n"
    code += "   else:\n"
    code += "      value = other %s int.__int__(self)\n" % op
    code += "      if type(value) is int:\n"
    code += "         return ConcolicInteger(value)\n"
    code += "      else:\n"
    code += "         return value\n"
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
