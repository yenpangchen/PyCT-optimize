from ..utils import *
from .concolic_bool import *
from .concolic_int import *
from conbyte.predicate import Predicate
from global_var import extend_vars, extend_queries, num_of_extend_vars

log = logging.getLogger("ct.con.list")

"""
Classes:
    ConcolicList
    Concolic_tuple
"""

class ConcolicList(list):
    def __init__(self, value, expr=None, len_expr=None):
        super().__init__(value)
        from .concolic_str import ConcolicStr
        types = ['Int', int, 0, 'String', str, '""']
        if len(value) == 0 or isinstance(value[0], types[1]): t = 0
        elif isinstance(value[0], types[4]): t = 3
        else: raise NotImplementedError
        if expr is not None:
            self.expr = expr
        else:
            ###########
            # Here are some examples of transforming lists into expressions.
            # 1. [] -> (list ((as const (Array Int Int)) 0) 0)
            # 2. [2] -> (list (store ((as const (Array Int Int)) 0) 0 2) 1)
            # 3. [-2, 4] -> (list (store (store ((as const (Array Int Int)) 0) 0 (- 2)) 1 4) 2)
            ###########
            self.expr = [['as', 'const', ['Array', 'Int', types[t]]], types[t+2]]
            for i, val in enumerate(value):
                assert isinstance(val, types[t+1])
                from global_var import upgrade
                val = global_var.upgrade(val)
                self.expr = ['store', self.expr, i, val.expr]
            if len_expr is None:
                self.expr = ['list', self.expr, len(value)]
            else:
                self.expr = ['list', self.expr, len_expr]
        if isinstance(self.expr, list):
            if t == 0:
                self.expr = global_var.add_extended_vars_and_queries('ListOfInt', self.expr)
            else: # t == 3
                self.expr = global_var.add_extended_vars_and_queries('ListOfStr', self.expr)
        log.debug("  List: %s" % ",".join(val.__str__() for val in list(self)))

    def append(self, element):
        element = global_var.upgrade(element)
        super().append(element)
        if not hasattr(element, 'expr'):
            raise NotImplementedError
        else:
            self.expr = ['list', ['store', ['array', self.expr], ['__len__', self.expr], element.expr], ['+', 1, ['__len__', self.expr]]]
            if isinstance(element, int):
                self.expr = global_var.add_extended_vars_and_queries('ListOfInt', self.expr)
            elif isinstance(element, str):
                self.expr = global_var.add_extended_vars_and_queries('ListOfStr', self.expr)
            else:
                raise NotImplementedError
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
    #     return ConcolicBool(value, expr)

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
    #     return ConcolicBool(value, expr)

    # def __str__(self):
    #     if self.size == 0:
    #         return "  List: nil"
    #     return "  List: %s" % ",".join(val.__str__() for val in self.value)

    # def __add__(self, other):
    #     log.debug(self)
    #     if isinstance(other, list):
    #         return super().__add__(list(other))
    #     else:
    #         raise NotImplementedError

    # def __radd__(self, other):
    #     self.value += other.value
    #     # self.size += other .size
    #     return self

    def __len__(self):
        return ConcolicInt(super().__len__(), ['__len__', self.expr])

    def __iter__(self):
        index = ConcolicInt(0)
        while index < self.__len__():
            result = self.__getitem__(index)
            index += ConcolicInt(1)
            yield result

    def __getitem__(self, key):
        from .concolic_str import ConcolicStr
        if not isinstance(key, ConcolicInt):
            if isinstance(key, slice): # TODO: SMT 先暫不處理 slice 的 type
                return ConcolicList(super().__getitem__(key))
            key = ConcolicInt(key)
        if key < 0: key += self.__len__()
        if isinstance(super().__getitem__(key), int):
            return ConcolicInt(int.__int__(super().__getitem__(key)), ['select', ['array', self.expr], key.expr])
        else:
            return ConcolicStr(str.__str__(super().__getitem__(key)), ['select', ['array', self.expr], key.expr])

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


# class Concolic_tuple(ConcolicBool):
#     def __init__(self, value):
#         self.expr = "Tuple"
#         self.value = value
#         log.debug("  Tuple: %s" % str(self.value))

#     def __str__(self):
#         return "  Tuple: %s" % str(self.value)
