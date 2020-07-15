from ..utils import *
from .concolic_type import *
from .concolic_int import *

log = logging.getLogger("ct.con.list")

"""
Classes:
    ConcolicList
    Concolic_tuple
"""

class ConcolicList(list):
    def __init__(self, *args):
        self.expr = "LIST"
        super().__init__(*args)
        # if value is None:
        #     super().__init__()
        #     # self.value = []
        #     # self.size = 0
        #     log.debug("  List: empty")
        #     return
        # elif isinstance(value, ConcolicList):
        #     raise NotImplementedError
        #     # self.value = value.value
        #     # self.size = value.size
        # else:
        #     super().__init__(value)
            # self.value = value
            # self.size = len(value)
        # log.debug("  List: %s" % ",".join(val.__str__() for val in list(self)))


    def append(self, element):
        super().append(element)
        # self.size += 1
        # log.debug("  List append: %s" % element)

    def get_index(self, index=0):
        if isinstance(index, ConcolicInteger):
            index = index.value
        return self.value[index]

    def get_slice(self, start=None, stop=None):
        if isinstance(start, ConcolicInteger):
            start = start.value
        if isinstance(stop, ConcolicInteger):
            stop = stop.value
        return ConcolicList(self.value[start:stop])

    def contains(self, other):
        expr = None
        value = False
        for val in self.value:
            if type(val) == type(other):
                value = value or (val.value == other.value)
                if expr is None:
                    expr = ["=", val.expr, other.expr]
                else:
                    expr = ["or", expr, ["=", val.expr, other.expr]]
        return ConcolicType(expr, value)

    def not_contains(self, other):
        expr = None
        value = False
        for val in self.value:
            value = value or (val.value == other.value)
            if type(val) == type(other):
                if expr is None:
                    expr = ["=", val.expr, other.expr]
                else:
                    expr = ["or", expr, ["=", val.expr, other.expr]]
        expr = ["not", expr]
        value = not value
        return ConcolicType(expr, value)

    # def __str__(self):
    #     if self.size == 0:
    #         return "  List: nil"
    #     return "  List: %s" % ",".join(val.__str__() for val in self.value)

    def __add__(self, other):
        if type(other) == list:
            super().__iadd__(other)
        else:
            super().__iadd__(list(other))
            # self.value += other.value
        # self.size += other .size
        log.debug(self)
        return self

    def __radd__(self, other):
        self.value += other.value
        # self.size += other .size
        return self

    def __len__(self):
        return ConcolicInteger(super().__len__())

    def __iter__(self):
        return super().__iter__() #iter(self.value)

    def __getitem__(self, key):
        return super().__getitem__(key)
        # return self.value[key]

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        # self.value[key] = value

    # def __delitem__(self, key):
    #     del self.value[key]

    def __mul__(self, mul):
        array = []
        for i in range(mul):
            for value in list(self): #.value:
                array.append(value)
        return ConcolicList(array)

    def store(self, index, value):
        if isinstance(index, ConcolicInteger):
            index = index.value

        self.value[index] = value

    def reverse(self):
        self.value = reversed(self.value)

    # def insert(self, index, value):
    #     # self.size += 1
    #     # if isinstance(index, ConcolicInteger):
    #         # index = index.value
    #     self.value.insert(index, value)

    def do_del(self, index):
        value = index.value
        del self.value[value]
        # self.size -= 1

    def index(self, target):
        return ConcolicInteger(super().index(target))
        # index = 0
        # for val in self.value:
        #     if val == target:
        #         return ConcolicInteger(index)
        #     index += 1

        # return ConcolicInteger(-1)

    def mul(self, other):
        self.value *= other.value
        return self

    # def add(self, other):
    #     self.value += other.value
    #     # self.size += other.size
    #     return self

    def remove(self, target):
        index = 0
        for val in self.value:
            if val.value == target.value:
                self.value.pop(index)
                # self.size -= 1
                break
            index += 1

    def pop(self, index=None):
        if index is None:
            # self.size -= 1
            return self.value.pop()
        else:
            # if index.value < self.size:
                # self.size -= 1
            return self.value.pop(int.__int__(index)) #.value)
            # else:
                # return None

    def reverse(self):
        self.value.reverse()

    def extend(self, target):
        super().__iadd__(target)
        # self = self.add(target)

    def parent(self):
        from global_var import downgrade
        return list(map(downgrade, list(self)))


class Concolic_tuple(ConcolicType):
    def __init__(self, value):
        self.expr = "Tuple"
        self.value = value
        log.debug("  Tuple: %s" % str(self.value))

    def __str__(self):
        return "  Tuple: %s" % str(self.value)
