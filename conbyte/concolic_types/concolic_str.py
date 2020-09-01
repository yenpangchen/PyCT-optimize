import logging
from conbyte.concolic_types.concolic import Concolic, MetaFinal
from conbyte.concolic_types.concolic_int import ConcolicInt
from conbyte.global_utils import ConcolicObject, py2smt, unwrap

log = logging.getLogger("ct.con.str")

class ConcolicStr(str, Concolic, metaclass=MetaFinal):
    def __new__(cls, value, expr=None, engine=None):
        assert type(value) is str
        obj = super().__new__(cls, value)
        obj.expr = expr if expr is not None else py2smt(value)
        obj.engine = engine if engine is not None else Concolic._find_engine_in_expression(expr)
        # if isinstance(obj.expr, list):
        #     obj.expr = global_utils.add_extended_vars_and_queries('String', obj.expr)
        log.debug(f"  ConStr, value: {value}, expr: {obj.expr}")
        return obj

    #########################################################################
    # All methods stated in the url are implemented in the following section.
    # https://docs.python.org/3/library/stdtypes.html#string-methods
    #########################################################################

    def capitalize(self):
        raise NotImplementedError

    def casefold(self):
        raise NotImplementedError

    def center(self, width, fillchar=' '):
        raise NotImplementedError

    # TODO: Concrete value
    def count(self, sub, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        return ConcolicObject(str.__str__(self).count(str.__str__(sub)))

    def encode(self, encoding="utf-8", errors="strict"):
        return str.__str__(self).encode(encoding, errors)
        raise NotImplementedError

    def endswith(self, suffix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        if not isinstance(suffix, ConcolicStr): suffix = ConcolicStr(suffix)
        value = str.__str__(self).endswith(str.__str__(suffix))
        expr = ["str.suffixof", suffix, self]
        return ConcolicObject(value, expr)

    # def expandtabs(self, tabsize=8):
    #     raise NotImplementedError

    def find(self, *args):
        L = len(args)
        if L < 1: raise TypeError('find() takes at least 1 argument (' + L + ' given)')
        sub = args[0]
        if not isinstance(sub, ConcolicStr): sub = ConcolicStr(sub)
        if L < 2: start = ConcolicObject(0)
        else: start = args[1]
        if not isinstance(start, ConcolicInt): start = ConcolicInt(start)
        if L < 3: end = None
        else: end = args[2]
        if L > 3: raise TypeError('find() takes at most 3 arguments (' + L + ' given)')
        if end is not None:
            if not isinstance(end, ConcolicInt): end = ConcolicInt(end)
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start), int.__int__(end))
            expr = ["str.indexof", self.substr(start, end), sub, start]
        else:
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start))
            expr = ["str.indexof", self, sub, start]
        return ConcolicObject(value, expr)

    # def format(self, *args, **kwargs):
    #     raise NotImplementedError

    def format_map(self, mapping):
        raise NotImplementedError

    def index(self, *args):
        res = self.find(args)
        if res == -1: str.__str__(self).index(args) # raise the built-in error
        return res

    def isalnum(self):
        raise NotImplementedError

    def isalpha(self):
        raise NotImplementedError

    def isascii(self):
        raise NotImplementedError

    def isdecimal(self):
        raise NotImplementedError

    def isdigit(self):
        value = str.__str__(self).isdigit()
        expr = ["str.in.re", self, ["re.+", ["re.range", "\"0\"", "\"9\""]]]
        return ConcolicObject(value, expr)

    # def isidentifier(self):
    #     raise NotImplementedError

    def islower(self):
        raise NotImplementedError

    def isnumeric(self):
        raise NotImplementedError

    def isprintable(self):
        raise NotImplementedError

    def isspace(self):
        raise NotImplementedError

    def istitle(self):
        raise NotImplementedError

    def isupper(self):
        raise NotImplementedError

    def join(self, array):
        return ConcolicObject(str.__str__(self).join(array))

    def ljust(self, width, fillchar=' '):
        raise NotImplementedError

    def lower(self):
        return ConcolicObject(str.__str__(self).lower())

    # TODO: Temp
    def lstrip(self, chars=None):
        if chars is None: chars = ConcolicObject(" ") # ConcolicObject("\" \"", " ")
        if int.__int__(len(chars)) == 0: return self
        if int.__int__(len(chars)) > 1: return super().lstrip(chars) # raise NotImplementedError
        assert len(str.__str__(chars)) == 1
        expr = self
        value = str.__str__(self) #.value
        while value.startswith(str.__str__(chars)): #.value):
            value = value[1:]
            expr = ["ite", ["str.prefixof", chars, expr],
                    ["str.substr", expr, 1, ["-", ["str.len", expr], 1]],
                    expr
                    ]
        return ConcolicObject(value, expr)

    @staticmethod
    def maketrans(x, y=-1, z=-1): # default arguments are not checked yet
        raise NotImplementedError

    def partition(self, sep):
        return str.__str__(self).partition(sep)
        raise NotImplementedError

    # TODO: Temp
    def replace(self, old, new, count=-1):
        if not isinstance(old, ConcolicStr): old = ConcolicStr(old)
        if not isinstance(new, ConcolicStr): new = ConcolicStr(new)
        value = str.__str__(self) #.value
        expr = self
        count = int.__int__(count) #.value
        if count == 0:
            return ConcolicObject(value, expr)
        n_value = value.replace(str.__str__(old), str.__str__(new), 1)
        n_expr = ["str.replace", expr, old, new]
        if count > 0:
            count -= 1
        while n_value != value and (count == -1 or count > 0):
            value = n_value
            expr = n_expr
            n_value = value.replace(str.__str__(old), str.__str__(new), 1)
            n_expr = ["str.replace", expr, old, new]
            if count > 0:
                count -= 1
        return ConcolicObject(n_value, n_expr)

    def rfind(self, sub, start=-1, end=-1): # default arguments are not checked yet
        return ConcolicObject(str.__str__(self).rfind(sub, start, end))
        raise NotImplementedError

    def rindex(self, sub, start=-1, end=-1): # default arguments are not checked yet
        raise NotImplementedError

    def rjust(self, width, fillchar=' '):
        raise NotImplementedError

    def rpartition(self, sep):
        return super().rpartition(sep)
        raise NotImplementedError

    def rsplit(self, sep=None, maxsplit=-1):
        raise NotImplementedError

    # TODO: Temp
    def rstrip(self, chars=None):
        if chars is None: chars = ConcolicObject(" ") # ConcolicObject("\" \"", " ")
        if not isinstance(chars, ConcolicStr): chars = ConcolicStr(chars)
        if int.__int__(len(chars)) == 0: return self
        if int.__int__(len(chars)) > 1: raise NotImplementedError
        assert int.__int__(len(chars)) == 1
        expr = self
        value = str.__str__(self) #.value
        while value.endswith(str.__str__(chars)): #.value):
            value = value[:-1]
            expr = ["ite", ["str.suffixof", chars, expr],
                    ["str.substr", expr, 0, ["-", ["str.len", expr], 1]],
                    expr
                   ]
        return ConcolicObject(value, expr)

    # TODO: Temp
    def split(self, sep=None, maxsplit=-1):
        if sep is None:
            res = str.__str__(self).split(sep, maxsplit) #raise NotImplementedError
            for i in range(len(res)):
                res[i] = ConcolicObject(res[i])
            return res #ConcolicList(res)
        if not isinstance(sep, ConcolicStr): sep = ConcolicStr(sep)
        sep2 = sep + sep
        sep_len = sep.__len__() # a constant
        ans_list = []
        substr = self
        while True:
            split_index = substr.find(sep)
            if split_index == -1 or maxsplit == 0:
                ans_list.append(substr)
                break
            elif maxsplit == -1:
                ans_list.append(substr.substr(stop=split_index))
                substr = substr.substr(start=split_index+sep_len)
            elif maxsplit > 0:
                ans_list.append(substr.substr(stop=split_index))
                substr = substr.substr(start=split_index+sep_len)
                maxsplit -= 1
            else:
                raise NotImplementedError
        return ans_list
        # if maxsplit == -1:
        #     len_expr = ['+', 1, ['div', ['-', ['str.len', ['str.replaceall', self, sep, sep2]], ['str.len', self]], ['str.len', sep]]]
        #     return ConcolicList(ans_list, len_expr=len_expr)
        # else:
        #     return ConcolicList(ans_list)

    def splitlines(self, keepends=False):
        if keepends: raise NotImplementedError
        if "\r\n" in str.__str__(self): #.value:
            return self.split("\r\n")
        else:
            return self.split("\n")

    def startswith(self, prefix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        if not isinstance(prefix, ConcolicStr): prefix = ConcolicStr(prefix)
        value = str.__str__(self).startswith(str.__str__(prefix)) #.value)
        expr = ["str.prefixof", prefix, self]
        return ConcolicObject(value, expr)

    # TODO: Temp
    def strip(self, chars=None):
        return self.lstrip(chars).rstrip(chars)

    def swapcase(self):
        raise NotImplementedError

    def title(self):
        raise NotImplementedError

    # def translate(self, table):
    #     raise NotImplementedError

    # Return a new string, no continued expr
    # TODO: Temp
    def upper(self):
        value = str.__str__(self).upper()
        return ConcolicObject(value) #'\"' + value + '\"')

    def zfill(self, width):
        raise NotImplementedError

    #############################################################################################
    # All underscored methods of the parent class "str" are implemented in the following section,
    # except __class__, __delattr__, __dir__, __doc__, __format__, __getattribute__, __getnewargs
    # __, __init_subclass__, __reduce__, __reduce_ex__, __repr__, __setattr__, __sizeof__, __subc
    # lasshook__. Note that __new__ and __init__ are implemented at the beginning of this class.
    #############################################################################################

    def __add__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        value = str.__str__(self) + str.__str__(other)
        expr = ["str.++", self, other]
        return ConcolicObject(value, expr)

    def __contains__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        value = str.__str__(self).__contains__(str.__str__(other))
        expr = ["str.contains", self, other]
        return ConcolicObject(value, expr)

    def __eq__(self, other):
        if other is None: return False
        return self.compare_op("==", other)

    def __ge__(self, other):
        return self.compare_op(">=", other)

    # TODO
    def __getitem__(self, key):
        if isinstance(key, int):
            if not isinstance(key, ConcolicInt): key = ConcolicInt(key)
            if key < 0:
                key += len(self)
            value = str.__str__(self)[int.__int__(key)]
            expr = ["str.at", self, key]
            return ConcolicObject(value, expr)
        if not isinstance(key, slice): raise NotImplementedError
        if key.step is not None: raise NotImplementedError
        return self.substr(key.start, key.stop)

    def __gt__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op(">", other)

    def __hash__(self):
        return hash(str.__str__(self))

    def __iter__(self):
        index = ConcolicObject(0)
        while index < self.__len__():
            result = self.__getitem__(index)
            index += ConcolicObject(1)
            yield result

    def __le__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("<=", other)

    def __len__(self):
        value = len(str.__str__(self)) #.value)
        expr = ["str.len", self]
        return ConcolicObject(value, expr)

    def __lt__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("<", other)

    def __mod__(self, tpl):
        if isinstance(tpl, str): return ConcolicObject(str.__str__(self).__mod__(tpl)) # 鴕鳥心態 (NotImplementedError)
        if not isinstance(tpl, tuple): return ConcolicObject(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
        if '%r' in str.__str__(self): return ConcolicObject(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
        if '%i' in str.__str__(self): return ConcolicObject(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
        lst = list(tpl) # convert from tuple to list for convenience
        res = ConcolicObject('') # 這裡可能需要再修改，如果是主詞是變數的話原本的 expr 就會被吃掉...
        remain = str.__str__(self)
        while True:
            split_by_int = remain.split('%d', 1)
            split_by_str = remain.split('%s', 1)
            if len(split_by_int) == 1 and len(split_by_str) == 1: break
            if len(split_by_int[0]) < len(split_by_str[0]):
                res += split_by_int[0]
                remain = str.__str__(res) + split_by_int[1]
                x = lst.pop(0)
                if isinstance(x, ConcolicStr):
                    res += x
                else:
                    if isinstance(x, int): x = x.__str__()
                    if isinstance(x, ConcolicStr): res += x
                    elif isinstance(x, str):
                        res += ConcolicObject(x)
                    else:
                        raise NotImplementedError
            else:
                res += split_by_str[0]
                remain = str.__str__(res) + split_by_str[1]
                x = lst.pop(0)
                if isinstance(x, ConcolicStr):
                    res += x
                else:
                    if not isinstance(x, str): x = str(x)
                    res += ConcolicObject(x)
        return res

    def __mul__(self, value):
        return ConcolicObject(str.__str__(self).__mul__(value))

    def __ne__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("!=", other)

    def __repr__(self):
        return str.__str__(self)

    # def __rmod__(self, value):
    #     raise NotImplementedError

    def __rmul__(self, value):
        raise NotImplementedError

    def __str__(self):
        return str.__str__(self) # why???
        # return self # "{ConStr, value: %s, expr: %s)" % (self.escape_value(), self)

    ################################################################
    # Other helper methods are implemented in the following section.
    ################################################################

    # custom method to get the primitive value
    def parent(self):
        return str.__str__(self)

    def substr(self, start=None, stop=None): # stop is exclusive...
        if stop is None:
            stop = len(self)
        if not isinstance(stop, ConcolicInt):
            stop = ConcolicObject(stop)
        if start is None:
            start = ConcolicObject(0)
        if not isinstance(start, ConcolicInt):
            start = ConcolicObject(start)
        if int.__int__(start) < 0:
            start += self.__len__()
        if int.__int__(start) < 0:
            start = ConcolicObject(0)
        if int.__int__(start) >= self.__len__():
            start = self.__len__()
        if int.__int__(stop) < 0:
            stop += self.__len__()
        if int.__int__(stop) < 0:
            stop = ConcolicObject(0)
        if int.__int__(stop) > self.__len__():
            stop = self.__len__()
        value = str.__str__(self)[int.__int__(start):int.__int__(stop)]
        expr = ["str.substr", self, start, (stop-start)]
        return ConcolicObject(value, expr)

    def compare_op(self, operator, other):
        val_l = str.__str__(self) #.value
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        val_r = str.__str__(other) #.value
        if operator == "==":
            value = val_l == val_r
            expr = ["=", self, other]
        elif operator == "!=":
            value = val_l != val_r
            expr = ['not', ["=", self, other]]
        elif operator == ">":
            # assert len(val_l) == 1 and len(val_r) == 1
            value = val_l > val_r
            expr = ['not', ['str.<=', self, other]]
            # expr = ["str.in.re", self, ["re.range", other, "\"\\xff\""]]
            # expr = ["and", ["not", ["=", self, other]], expr]
        elif operator == "<":
            # assert len(val_l) == 1 and len(val_r) == 1
            value = val_l < val_r
            expr = ['str.<', self, other]
            # expr = ["str.in.re", self, ["re.range", "\"\\x00\"", other]]
            # expr = ["and", ["not", ["=", self, other]], expr]
        elif operator == ">=":
            # assert len(val_l) == 1 and len(val_r) == 1
            value = val_l >= val_r
            expr = ['not', ['str.<', self, other]]
            # expr = ["str.in.re", self, ["re.range", other, "\"\\xff\""]]
        elif operator == "<=":
            # assert len(val_l) == 1 and len(val_r) == 1
            value = val_l <= val_r
            expr = ['str.<=', self, other]
            # expr = ["str.in.re", self, ["re.range", "\"\\x00\"", other]]
        else:
            raise NotImplementedError
        return ConcolicObject(value, expr)

    """
       Global functions
    """

    def __int2__(self):
        self.isnumber().__bool__()
        expr = ["ite", ["str.prefixof", "\"-\"", self],
                ["-", ["str.to.int",
                    ["str.substr", self, "1", ["-", ["str.len", self], "1"]]
                    ]
                ],
                ["str.to.int", self]
            ]
        return ConcolicObject(int(str.__str__(self)), expr)

    def isnumber(self):
        expr = ["ite", ["str.prefixof", "\"-\"", self],
               ["and",
                ["ite", ["=", "(- 1)",
                        ["str.to.int", ["str.substr", self, "1", ["-", ["str.len", self], "1"]]]
                       ],
                 "false",
                 "true"
                ],
                [">", ["str.len", self], "1"]
               ],
               ["ite", ["=", "(- 1)", ["str.to.int", self]],
                 "false",
                 "true"
               ]
              ]
        my_str = str.__str__(self)
        if my_str.startswith('-'): my_str = my_str[1:]
        return ConcolicObject(my_str.isdigit(), expr)
