from ..utils import *
from .concolic_bool import *
from .concolic_int import *

log = logging.getLogger("ct.con.list")

"""
Classes:
    ConcolicList
    Concolic_tuple
"""

class ConcolicList(list):
    def __init__(self, value, expr=None):
        super().__init__(value)
        if expr is not None:
            self.expr = expr
        else:
            ###########
            # Here are some examples of transforming lists into expressions.
            # 1. [] -> (list ((as const (Array Int Int)) 0) 0)
            # 2. [2] -> (list (store ((as const (Array Int Int)) 0) 0 2) 1)
            # 3. [-2, 4] -> (list (store (store ((as const (Array Int Int)) 0) 0 (- 2)) 1 4) 2)
            ###########
            self.expr = [['as', 'const', ['Array', 'Int', 'Int']], 0]
            for i, val in enumerate(value):
                if val < 0:
                    self.expr = ['store', self.expr, i, ['-', -val]]
                else:
                    self.expr = ['store', self.expr, i, val]
            self.expr = ['list', self.expr, len(value)]
        log.debug("  List: %s" % ",".join(val.__str__() for val in list(self)))

    def append(self, element):
        super().append(element)
        self.expr = ['list', ['store', ['array', self.expr], ['__len__', self.expr], element.expr], ['+', 1, ['__len__', self.expr]]]
        # self.size += 1
        # log.debug("  List append: %s" % element)

    # def get_index(self, index=0):
    #     if isinstance(index, ConcolicInt):
    #         index = index.value
    #     return self.value[index]

    # def get_slice(self, start=None, stop=None):
    #     if isinstance(start, ConcolicInt):
    #         start = start.value
    #     if isinstance(stop, ConcolicInt):
    #         stop = stop.value
    #     return ConcolicList(self.value[start:stop])

    # def contains(self, other):
    #     expr = None
    #     value = False
    #     for val in self.value:
    #         if type(val) == type(other):
    #             value = value or (val.value == other.value)
    #             if expr is None:
    #                 expr = ["=", val.expr, other.expr]
    #             else:
    #                 expr = ["or", expr, ["=", val.expr, other.expr]]
    #     return ConcolicBool(expr, value)

    # def not_contains(self, other):
    #     expr = None
    #     value = False
    #     for val in self.value:
    #         value = value or (val.value == other.value)
    #         if type(val) == type(other):
    #             if expr is None:
    #                 expr = ["=", val.expr, other.expr]
    #             else:
    #                 expr = ["or", expr, ["=", val.expr, other.expr]]
    #     expr = ["not", expr]
    #     value = not value
    #     return ConcolicBool(expr, value)

    # def __str__(self):
    #     if self.size == 0:
    #         return "  List: nil"
    #     return "  List: %s" % ",".join(val.__str__() for val in self.value)

    def __add__(self, other):
        log.debug(self)
        if isinstance(other, list):
            return super().__add__(list(other))
        else:
            raise NotImplementedError

    # def __radd__(self, other):
    #     self.value += other.value
    #     # self.size += other .size
    #     return self

    def __len__(self):
        return ConcolicInt(['__len__', self.expr], super().__len__())

    def __iter__(self):
        return super().__iter__() #iter(self.value)

    def __getitem__(self, key):
        if not isinstance(key, ConcolicInt): key = ConcolicInt(key)
        if key < 0: key += self.__len__()
        return ConcolicInt(['select', ['array', self.expr], key.expr], super().__getitem__(key))

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        if not isinstance(key, ConcolicInt): key = ConcolicInt(key)
        if not isinstance(value, ConcolicInt): value = ConcolicInt(value)
        if key < 0: key += self.__len__()
        self.expr = ['list', ['store', ['array', self.expr], key.expr, value.expr], ['__len__', self.expr]]
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
        if isinstance(index, ConcolicInt):
            index = index.value

        self.value[index] = value

    def reverse(self):
        self.value = reversed(self.value)

    # def insert(self, index, value):
    #     # self.size += 1
    #     # if isinstance(index, ConcolicInt):
    #         # index = index.value
    #     self.value.insert(index, value)

    def do_del(self, index):
        value = index.value
        del self.value[value]
        # self.size -= 1

    def index(self, target):
        return ConcolicInt(super().index(target))
        # index = 0
        # for val in self.value:
        #     if val == target:
        #         return ConcolicInt(index)
        #     index += 1

        # return ConcolicInt(-1)

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
            self.expr = ['list', ['array', self.expr], ['-', ['__len__', self.expr], 1]]
            return super().pop()
        else:
            raise NotImplementedError
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


class Concolic_tuple(ConcolicBool):
    def __init__(self, value):
        self.expr = "Tuple"
        self.value = value
        log.debug("  Tuple: %s" % str(self.value))

    def __str__(self):
        return "  Tuple: %s" % str(self.value)
