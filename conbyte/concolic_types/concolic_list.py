from .concolic_bool import *
from .concolic_int import *
from conbyte.predicate import Predicate

log = logging.getLogger("ct.con.list")

"""
Classes:
    ConcolicList
    Concolic_tuple
"""

class ConcolicList(list):
    def __init__(self, value: list, expr_engine=None): # , len_expr=None):
        from .concolic_str import ConcolicStr
        import conbyte.global_utils
        assert isinstance(value, list)
        super().__init__(value)
        # types = ['Int', int, 0, 'String', str, '""']
        # if len(value) == 0:
        #     if ctype == 'ListOfInt': t = 0
        #     elif ctype == 'ListOfStr': t = 3
        #     else: raise NotImplementedError
        # elif isinstance(value[0], types[1]): t = 0
        # elif isinstance(value[0], types[4]): t = 3
        # else: raise NotImplementedError
        self.expr = self.engine = None
        if expr_engine:
            self.expr = expr_engine.expr
            self.engine = expr_engine.engine
        else:
            ###########
            # Here are some examples of transforming lists into expressions.
            # 1. [] -> (list ((as const (Array Int Int)) 0) 0)
            # 2. [2] -> (list (store ((as const (Array Int Int)) 0) 0 2) 1)
            # 3. [-2, 4] -> (list (store (store ((as const (Array Int Int)) 0) 0 (- 2)) 1 4) 2)
            ###########
            if len(value) > 0: # only construct expressions for non-empty lists
                types = ['Int', ConcolicInt, 0, 'String', ConcolicStr, '""']
                if isinstance(value[0], types[1]): t = 0
                elif isinstance(value[0], types[4]): t = 3
                else: return # raise NotImplementedError
                self.expr = [['as', 'const', ['Array', 'Int', types[t]]], types[t+2]]
                for (i, val) in enumerate(value):
                    assert isinstance(val, types[t+1])
                    val = conbyte.global_utils.upgrade(val)
                    self.expr = ['store', self.expr, i, val.expr]
                if len_expr is None:
                    self.expr = ['list', self.expr, len(value)]
                else:
                    self.expr = ['list', self.expr, len_expr]
        if isinstance(self.expr, list) and self.engine:
            if t == 0:
                self.expr = conbyte.global_utils.add_extended_vars_and_queries('ListOfInt', self.expr, self.engine)
            else: # t == 3
                self.expr = conbyte.global_utils.add_extended_vars_and_queries('ListOfStr', self.expr, self.engine)
        log.debug("  List: %s" % ",".join(val.__str__() for val in list(self)))

    def __add__(self, other):
        raise NotImplementedError
        if isinstance(other, list):
            return super().__add__(list(other))
        else:
            raise NotImplementedError

    # 這個 method 似乎冥冥之中已經被加入 branch 了... 但我不知道原因！！！
    # def __contains__(self, element):
    #     raise NotImplementedError

    def __delitem__(self, key):
        raise NotImplementedError

    # def __eq__(self, other):
    #     raise NotImplementedError

    # def __ge__(self, other):
    #     raise NotImplementedError

    # def __getattribute__(self, name):
    #     raise NotImplementedError

    def __getitem__(self, key):
        if self.expr:
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
        else:
            return super().__getitem__(key)

    # def __gt__(self, other):
    #     raise NotImplementedError

    def __iadd__(self, other):
        raise NotImplementedError

    def __imul__(self, other):
        raise NotImplementedError

    def __iter__(self):
        if self.expr:
            index = ConcolicInt(0)
            while index < self.__len__():
                result = self.__getitem__(index)
                index += ConcolicInt(1)
                yield result
        else:
            index = 0
            while index < super().__len__():
                result = super().__getitem__(index)
                index += 1
                yield result

    # def __le__(self, other):
    #     raise NotImplementedError

    def __len__(self):
        if self.expr:
            return ConcolicInt(super().__len__(), ['__len__', self.expr])
        else:
            return ConcolicInt(super().__len__())

    # def __lt__(self, other):
    #     raise NotImplementedError

    def __mul__(self, mul):
        raise NotImplementedError
        array = []
        for i in range(mul):
            for value in list(self): #.value:
                array.append(value)
        return ConcolicList(array)

    # def __ne__(self, other):
    #     raise NotImplementedError

    # def __repr__(self):
    #     raise NotImplementedError

    # def __reversed__(self):
    #     raise NotImplementedError

    # def __rmul__(self, value):
    #     raise NotImplementedError

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        if self.expr:
            if not isinstance(key, ConcolicInt): key = ConcolicInt(key)
            if isinstance(value, int) and not isinstance(value, ConcolicInt): value = ConcolicInt(value)
            if isinstance(value, str) and not isinstance(value, ConcolicStr): value = ConcolicStr(value)
            if key < 0: key += self.__len__()
            self.expr = ['list', ['store', ['array', self.expr], key.expr, value.expr], ['__len__', self.expr]]

    # def __sizeof__(self):
    #     raise NotImplementedError

    def append(self, element):
        super().append(element)
        if not hasattr(element, 'expr'):
            raise NotImplementedError
        else:
            if self.expr:
                self.expr = ['list', ['store', ['array', self.expr], ['__len__', self.expr], element.expr], ['+', 1, ['__len__', self.expr]]]
                if self.engine:
                    if isinstance(element, int):
                        self.expr = conbyte.global_utils.add_extended_vars_and_queries('ListOfInt', self.expr, self.engine)
                    elif isinstance(element, str):
                        self.expr = conbyte.global_utils.add_extended_vars_and_queries('ListOfStr', self.expr, self.engine)
                    else:
                        raise NotImplementedError
            else: # append to an empty list
                if isinstance(element, int):
                    self.expr = [['as', 'const', ['Array', 'Int', 'Int']], 0]
                elif isinstance(element, str):
                    self.expr = [['as', 'const', ['Array', 'Int', 'String']], '""']
                else:
                    raise NotImplementedError
                self.expr = ['store', self.expr, 0, element.expr]
                self.expr = ['list', self.expr, 1]
        log.debug("  List append: %s" % element)

    def clear(self):
        raise NotImplementedError

    # def copy(self):
    #     raise NotImplementedError

    # def count(self, value):
    #     raise NotImplementedError

    # temporarily disable for passing some testcases
    # def extend(self, iterable):
    #     raise NotImplementedError

    # def index(self, value, start=0, stop=9223372036854775807):
    #     return ConcolicInt(super().index(target))
        # index = 0
        # for val in self.value:
        #     if val == target:
        #         return ConcolicInt(index)
        #     index += 1
        # return ConcolicInt(-1)

    def insert(self, index, value):
        raise NotImplementedError
        super().insert(index, value)

    def pop(self, index=-1):
        if index == -1:
            # self.size -= 1
            self.expr = ['list', ['array', self.expr], ['-', ['__len__', self.expr], 1]]
            return super().pop() # 這裡其實還沒實作完全... (應該要帶 expression)
        else:
            raise NotImplementedError
            # if index.value < self.size:
                # self.size -= 1
            return self.value.pop(int.__int__(index)) #.value)
            # else:
                # return None

    def remove(self, target):
        raise NotImplementedError
        index = 0
        for val in self.value:
            if val.value == target.value:
                self.value.pop(index)
                # self.size -= 1
                break
            index += 1

    def reverse(self):
        raise NotImplementedError
        self.value.reverse()

    def sort(self, key=None, reverse=False):
        raise NotImplementedError

    # custom function to perform downgrading
    def parent(self):
        from conbyte.global_utils import unwrap
        return list(map(unwrap, list(self)))

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

    # def __radd__(self, other):
    #     self.value += other.value
    #     # self.size += other .size
    #     return self

    # def store(self, index, value):
    #     if isinstance(index, ConcolicInt):
    #         index = index.value

    #     self.value[index] = value

    # def reverse(self):
    #     self.value = reversed(self.value)

    # def do_del(self, index):
    #     value = index.value
    #     del self.value[value]
    #     # self.size -= 1

    # def mul(self, other):
    #     self.value *= other.value
    #     return self

    # def add(self, other):
    #     self.value += other.value
    #     # self.size += other.size
    #     return self

# class Concolic_tuple(ConcolicBool):
#     def __init__(self, value):
#         self.expr = "Tuple"
#         self.value = value
#         log.debug("  Tuple: %s" % str(self.value))

#     def __str__(self):
#         return "  Tuple: %s" % str(self.value)
