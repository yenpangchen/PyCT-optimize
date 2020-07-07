from ..utils import *
from .concolic_type import *
from .concolic_int import *
from .concolic_list import *

log = logging.getLogger("ct.con.str")

class ConcolicStr(str): #(ConcolicType):
    # def __init__(self, expr, value=None):
    #     if isinstance(expr, str):
    #         expr = expr.replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t")
    #     self.expr = expr

    #     if value is None:
    #         self.value = expr.replace("\"", "", 1).replace("\"", "", -1)
    #     else:
    #         self.value = value
    #     log.debug("  ConStr, value: %s, expr: %s" % (self.value, self.expr))

    def __new__(cls, expr, value=None): # maybe decorator required?
        if value is not None:
            return str.__new__(cls, value)
        else:
            if isinstance(expr, int): expr = str(expr)
            if isinstance(expr, str): expr = expr.replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t")
            return str.__new__(cls, expr.replace("\"", "", 1).replace("\"", "", -1))

    def __init__(self, expr, value=None): # maybe decorator required?
        if isinstance(expr, int): expr = str(expr)
        if isinstance(expr, str): expr = expr.replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t")
        if value is None: expr = "\"" + expr + "\"" # 這一步很重要，因為 SMT solver 分不清楚 var name 和 string const 的差別，所以必須藉由在兩側加上雙引號的方式去區別兩者！
        self.expr = expr
        log.debug("  ConStr, value: %s, expr: %s" % (self, self.expr))

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
        raise NotImplementedError
        return ConcolicInteger(str.__str__(self).count(str.__str__(sub)))

    def encode(self, encoding="utf-8", errors="strict"):
        return str.__str__(self).encode(encoding, errors)
        raise NotImplementedError

    def endswith(self, suffix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        # if not isinstance(suffix, ConcolicStr): suffix = ConcolicStr(suffix)
        assert isinstance(suffix, ConcolicStr)
        value = str.__str__(self).endswith(str.__str__(suffix))
        expr = ["str.suffixof", suffix.expr, self.expr]
        return ConcolicType(expr, value)

    def expandtabs(self, tabsize=8):
        raise NotImplementedError

    def find(self, sub, start=ConcolicInteger(0), end=None):
        # if not isinstance(sub, ConcolicStr): sub = ConcolicStr(sub)
        assert isinstance(sub, ConcolicStr)
        # if not isinstance(start, ConcolicInteger): start = ConcolicInteger(start)
        assert isinstance(start, ConcolicInteger)
        if end is not None:
            partial = self.get_slice(start, end)
            value = str.__str__(partial).find(str.__str__(sub), int.__int__(start), int.__int__(end))
            expr = ["str.indexof", partial.expr, sub.expr, start.expr]
        else:
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start))
            expr = ["str.indexof", self.expr, sub.expr, start.expr]
        return ConcolicInteger(expr, value)

    def format(self, *args, **kwargs):
        raise NotImplementedError

    def format_map(self, mapping):
        raise NotImplementedError

    def index(self, sub, start=ConcolicInteger(0), end=None):
        res = self.find(sub, start, end)
        if res == -1: raise ValueError
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
        expr = ["str.in.re", self.expr, ["re.+", ["re.range", "\"0\"", "\"9\""]]]
        return ConcolicType(expr, value)

    def isidentifier(self):
        raise NotImplementedError

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
        return str.__str__(self).join(array)
        raise NotImplementedError
        # if isinstance(array, ConcolicList):
        #     orig = ConcolicStr(self.expr, self.value)
        #     self.value = ""
        #     self.expr = "\"\""
        #     for element in array.value:
        #         if isinstance(element, ConcolicInteger):
        #             append = ConcolicStr(element.get_str())
        #         if isinstance(element, ConcolicStr):
        #             append = element
        #         else:
        #             append = ConcolicStr('\"' + str.__str__(element) + '\"')
        #         self = self.__add__(append)
        #         self = self.__add__(orig)
        # else:
        #     log.warrning("Not implemented: str.join(<other type>)")

    def ljust(self, width, fillchar=' '):
        raise NotImplementedError

    # Return a new string, no continued expr
    # TODO: Temp
    def lower(self):
        # raise NotImplementedError
        return ConcolicStr(str.__str__(self).lower())

    # TODO: Temp
    def lstrip(self, chars=None):
        if chars is None: chars = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
        if int.__int__(len(chars)) == 0: return self
        if int.__int__(len(chars)) > 1: raise NotImplementedError
        assert int.__int__(len(chars)) == 1
        expr = self.expr
        value = str.__str__(self) #.value
        while value.startswith(str.__str__(chars)): #.value):
            value = value[1:]
            expr = ["ite", ["str.prefixof", chars.expr, expr],
                    ["str.substr", expr, 1, ["-", ["str.len", expr], 1]],
                    expr
                    ]
        return ConcolicStr(expr, value)

    @staticmethod
    def maketrans(x, y=-1, z=-1): # default arguments are not checked yet
        raise NotImplementedError

    def partition(self, sep):
        raise NotImplementedError

    # TODO: Temp
    def replace(self, old, new, count=-1):
        # if not isinstance(old, ConcolicStr): old = ConcolicStr(old)
        assert isinstance(old, ConcolicStr)
        # if not isinstance(new, ConcolicStr): new = ConcolicStr(new)
        assert isinstance(new, ConcolicStr)
        value = str.__str__(self) #.value
        expr = self.expr
        # if isinstance(count, ConcolicInteger):
        assert isinstance(count, ConcolicInteger)
        count = int.__int__(count) #.value
        if count == 0:
            return ConcolicStr(expr, value)
        n_value = value.replace(str.__str__(old), str.__str__(new), 1)
        n_expr = ["str.replace", expr, old.expr, new.expr]
        if count > 0:
            count -= 1
        while n_value != value and (count == -1 or count > 0):
            value = n_value
            expr = n_expr
            n_value = value.replace(str.__str__(old), str.__str__(new), 1)
            n_expr = ["str.replace", expr, old.expr, new.expr]
            if count > 0:
                count -= 1
        return ConcolicStr(n_expr, n_value)

    def rfind(self, sub, start=-1, end=-1): # default arguments are not checked yet
        raise NotImplementedError

    def rindex(self, sub, start=-1, end=-1): # default arguments are not checked yet
        raise NotImplementedError

    def rjust(self, width, fillchar=' '):
        raise NotImplementedError

    def rpartition(self, sep):
        raise NotImplementedError

    def rsplit(self, sep=None, maxsplit=-1):
        raise NotImplementedError

    # TODO: Temp
    def rstrip(self, chars=None):
        if chars is None: chars = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
        if int.__int__(len(chars)) == 0: return self
        if int.__int__(len(chars)) > 1: raise NotImplementedError
        assert int.__int__(len(chars)) == 1
        expr = self.expr
        value = str.__str__(self) #.value
        while value.endswith(str.__str__(chars)): #.value):
            value = value[:-1]
            expr = ["ite", ["str.suffixof", chars.expr, expr],
                    ["str.substr", expr, 0, ["-", ["str.len", expr], 1]],
                    expr
                   ]
        return ConcolicStr(expr, value)

    # TODO: Temp
    def split(self, sep=None, maxsplit=ConcolicInteger(-1)): # default arguments are not checked yet
        # return str.__str__(self).split(sep, maxsplit)
        raise NotImplementedError
        if sep == None:
            sep = ' '
        return str.__str__(self).split(str.__str__(sep), int.__int__(maxsplit))
        # assert isinstance(maxsplit, ConcolicInteger)
        maxsplit = int.__int__(maxsplit) #.value
        if sep is not None:
            if len(str.__str__(self)) == 0:
                return ConcolicList([ConcolicStr("")]) # ConcolicList([ConcolicStr("\"\"")])
        else:
            sep = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
            if len(str.__str__(self)) == 0:
                return ConcolicList([ConcolicStr("\"\"")])
        assert isinstance(sep, ConcolicStr)#: #str):
        #    sep = ConcolicStr(sep)
        if maxsplit == 0 or str.__str__(sep) not in str.__str__(self): #.value:
            return ConcolicList([self])
        else:
            sep_idx = self.find(sep)
            if maxsplit is None:
                return ConcolicList([self.get_slice(None, sep_idx)]) + \
                   ConcolicList(self.get_slice(sep_idx + 1).split(sep))
            else:
                return [self.get_slice(None, sep_idx)] + [self.get_slice(sep_idx + 1).split(sep, maxsplit - 1)]
                # return ConcolicList([self.get_slice(None, sep_idx)]) + \
                #    ConcolicList(self.get_slice(sep_idx + 1).split(sep, maxsplit - 1))

    def splitlines(self, keepends=False):
        if keepends: raise NotImplementedError
        if "\\r\\n" in str.__str__(self): #.value:
            return self.split("\\r\\n")
        else:
            return self.split("\\n")

    def startswith(self, prefix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        # if not isinstance(prefix, ConcolicStr): prefix = ConcolicStr(prefix)
        assert isinstance(prefix, ConcolicStr)
        value = str.__str__(self).startswith(str.__str__(prefix)) #.value)
        expr = ["str.prefixof", prefix.expr, self.expr]
        return ConcolicType(expr, value)

    # TODO: Temp
    def strip(self, chars=None):
        return self.lstrip(chars).rstrip(chars)

    def swapcase(self):
        raise NotImplementedError

    def title(self):
        raise NotImplementedError

    def translate(self, table):
        # return NotImplemented
        raise NotImplementedError

    # Return a new string, no continued expr
    # TODO: Temp
    def upper(self):
        value = str(self).upper()
        return ConcolicStr(value) #'\"' + value + '\"')

    def zfill(self, width):
        raise NotImplementedError

    #############################################################################################
    # All underscored methods of the parent class "str" are implemented in the following section,
    # except __class__, __delattr__, __dir__, __doc__, __format__, __getattribute__, __getnewargs
    # __, __init_subclass__, __iter__, __reduce__, __reduce_ex__, __repr__, __setattr__, __sizeof
    # __, __subclasshook__. Note that __new__ and __init__ are implemented at the beginning of th
    # is class.
    #############################################################################################

    def __add__(self, other):
        assert isinstance(other, ConcolicStr)
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        value = str.__str__(self) + str.__str__(other)
        expr = ["str.++", self.expr, other.expr]
        return ConcolicStr(expr, value)

    def __radd__(self, other): # the supplementary method for the case <str> + <ConcolicStr>
        return NotImplemented
        # raise NotImplementedError
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        # assert isinstance(other, ConcolicStr)
        # value = str.__str__(other) + str.__str__(self)
        # expr = ["str.++", other.expr, self.expr]
        # return ConcolicStr(expr, value)

    def __contains__(self, other):
        assert isinstance(other, ConcolicStr)
        value = str.__str__(self).__contains__(str.__str__(other))
        expr = ["str.contains", self.expr, other.expr]
        return ConcolicType(expr, value)

    def __eq__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op("==", other)

    def __ge__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op(">=", other)

    # TODO
    def __getitem__(self, key):
        if isinstance(key, int):
        # if isinstance(key, ConcolicInteger):
            if not isinstance(key, ConcolicInteger): key = ConcolicInteger(key)
            # assert isinstance(key, ConcolicInteger)
            value = str.__str__(self)[int.__int__(key)]
            expr = ["str.at", self.expr, key.expr]
            return ConcolicStr(expr, value)
        if not isinstance(key, slice): raise NotImplementedError
        if key.step is not None: raise NotImplementedError
        return self.get_slice(key.start, key.stop)

    def __gt__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op(">", other)

    def __hash__(self):
        return hash(str.__str__(self))

    def __le__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op("<=", other)

    def __len__(self):
        value = len(str.__str__(self)) #.value)
        expr = ["str.len", self.expr]
        return ConcolicInteger(expr, value)

    def __lt__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op("<", other)

    def __mod__(self, tpl):
        if isinstance(tpl, str): return str.__str__(self).__mod__(tpl) # 鴕鳥心態 (NotImplementedError)
        if not isinstance(tpl, tuple): raise NotImplementedError
        lst = list(tpl) # convert from tuple to list for convenience
        res = ConcolicStr('') # 這裡可能需要再修改，如果是主詞是變數的話原本的 expr 就會被吃掉...
        remain = str.__str__(self)
        while True:
            split_by_int = remain.split('%d', 1)
            split_by_str = remain.split('%s', 1)
            if len(split_by_int) == 1 and len(split_by_str) == 1: break
            if len(split_by_int[0]) < len(split_by_str[0]):
                res += split_by_int[0]
                remain = str.__str__(res) + split_by_int[1]
                if isinstance(lst[0], ConcolicStr):
                    res += lst.pop(0)
                else:
                    res += ConcolicStr(lst.pop(0))
            else:
                res += split_by_str[0]
                remain = str.__str__(res) + split_by_str[1]
                if isinstance(lst[0], ConcolicStr):
                    res += lst.pop(0)
                else:
                    res += ConcolicStr(lst.pop(0))
        return res
        raise NotImplementedError

    def __mul__(self, value):
        return str.__str__(self).__mul__(value)
        raise NotImplementedError

    def __ne__(self, other):
        # if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        assert isinstance(other, ConcolicStr)
        return self.compare_op("!=", other)

    def __rmod__(self, value):
        return NotImplemented
        # raise NotImplementedError

    def __rmul__(self, value):
        raise NotImplementedError

    def __str__(self):
        return str.__str__(self)
        # return self # "{ConStr, value: %s, expr: %s)" % (self.escape_value(), self.expr)

    ################################################################
    # Other helper methods are implemented in the following section.
    ################################################################

    # custom method to get the primitive value
    def parent(self):
        return str.__str__(self)

    def get_slice(self, start=None, stop=None):
        if stop is None:
            stop = len(self)
        else:
            # if not isinstance(stop, ConcolicInteger):
            #     stop = ConcolicInteger(stop)
            assert isinstance(stop, ConcolicInteger)
        if start is None:
            start = ConcolicInteger(0)
        else:
            # if not isinstance(start, ConcolicInteger):
            #     start = ConcolicInteger(start)
            assert isinstance(start, ConcolicInteger)
        value = str.__str__(self)[int.__int__(start):int.__int__(stop)]
        if int.__int__(start) < 0:
            start.expr = ["+", ["str.len", self.expr], start.expr]
        if int.__int__(stop) < 0:
            stop.expr = ["+", ["str.len", self.expr], stop.expr]
        expr = ["str.substr", self.expr, start.expr, (stop-start).expr]
        return ConcolicStr(expr, value)

    def compare_op(self, operator, other):
        val_l = str.__str__(self) #.value
        assert isinstance(other, ConcolicStr)
        val_r = str.__str__(other) #.value
        if operator == "==":
            value = val_l == val_r
            expr = ["=", self.expr, other.expr]
        elif operator == "!=":
            value = val_l != val_r
            expr = ['not', ["=", self.expr, other.expr]]
        elif operator == ">":
            value = val_l > val_r
            expr = ["str.in.re", self.expr, ["re.range", other.expr, "\"\\xff\""]]
            expr = ["and", ["not", ["=", self.expr, other.expr]], expr]
        elif operator == "<":
            value = val_l < val_r
            expr = ["str.in.re", self.expr, ["re.range", "\"\\x00\"", other.expr]]
            expr = ["and", ["not", ["=", self.expr, other.expr]], expr]
        elif operator == ">=":
            value = val_l >= val_r
            expr = ["str.in.re", self.expr, ["re.range", other.expr, "\"\\xff\""]]
        elif operator == "<=":
            value = val_l <= val_r
            expr = ["str.in.re", self.expr, ["re.range", "\"\\x00\"", other.expr]]
        else:
            raise NotImplementedError
        return ConcolicType(expr, value)

    """
       Global functions
    """
    # def len(self):
    #     value = len(self.value)
    #     expr = ["str.len", self.expr]
    #     return ConcolicInteger(expr, value)
    def __int__(self):
        value = int(self, 10)
        expr = ["ite", ["str.prefixof", "\"-\"", self.expr],
                ["-", ["str.to.int",
                       ["str.substr", self.expr, "1", ["-", ["str.len", self.expr], "1"]]
                      ]
                ],
                ["str.to.int", self.expr]
               ]
        return ConcolicInteger(expr, value)
    # def escape_value(self):
    #     return self.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    #     # value = self.value.replace("\n", "\\n")
    #     # value = value.replace("\r", "\\r")
    #     # value = value.replace("\t", "\\t")
    #     # return value
    # def contains(self, other):
    #     value = other.value in self.value
    #     expr = ["str.contains", self.expr, other.expr]
    #     return ConcolicType(expr, value)
    # def not_contains(self, other):
    #     value = other.value not in self.value
    #     expr = ["not", ["str.contains", self.expr, other.expr]]
    #     return ConcolicType(expr, value)
    # def is_number(self):
    #     value = True
    #     expr = ["ite", ["str.prefixof", "\"-\"", self.expr],
    #            ["and",
    #             ["ite", ["=", "(- 1)",
    #                     ["str.to.int", ["str.substr", self.expr, "1", ["-", ["str.len", self.expr], "1"]]]
    #                    ],
    #              "false",
    #              "true"
    #             ],
    #             [">", ["str.len", self.expr], "1"]
    #            ],
    #            ["ite", ["=", "(- 1)", ["str.to.int", self.expr]],
    #              "false",
    #              "true"
    #            ]
    #           ]
    #     return ConcolicType(expr, value)
    # def store(self, index, value):
    #     if isinstance(index, ConcolicInteger):
    #         index = index.value
    #     self.value[index] = value
