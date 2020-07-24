from .concolic_bool import *
from .concolic_int import *
from .concolic_list import *
# import logging
log = logging.getLogger("ct.con.str")

class ConcolicStr(str):
    def __new__(cls, value, expr=None):
        return str.__new__(cls, value)

    def __init__(self, value, expr=None):
        self.hasvar = expr is not None
        if expr is not None:
            self.expr = expr
            # if isinstance(self.expr, list):
            #     self.expr = global_utils.add_extended_vars_and_queries('String', self.expr)
        else:
            value = value.replace("\\", "\\\\").replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t").replace('"', '""')
            value_new = ""
            for ch in value:
                if ord(ch) > 127: # unicode characters
                    value_new += '\\u{' + str(hex(ord(ch)))[2:] + '}'
                else:
                    value_new += ch
            value = "\"" + value_new + "\"" # 這一步很重要，因為 SMT solver 分不清楚 var name 和 string const 的差別，所以必須藉由在兩側加上雙引號的方式去區別兩者！
            self.expr = value
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
        # raise NotImplementedError
        return ConcolicInt(str.__str__(self).count(str.__str__(sub)))

    def encode(self, encoding="utf-8", errors="strict"):
        return str.__str__(self).encode(encoding, errors)
        raise NotImplementedError

    def endswith(self, suffix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        if not isinstance(suffix, ConcolicStr): suffix = ConcolicStr(suffix)
        value = str.__str__(self).endswith(str.__str__(suffix))
        if self.hasvar or suffix.hasvar:
            expr = ["str.suffixof", suffix.expr, self.expr]
            return ConcolicBool(value, expr)
        else:
            return ConcolicBool(value)

    # def expandtabs(self, tabsize=8):
    #     raise NotImplementedError

    def find(self, *args):
        argshasvar = self.hasvar
        L = len(args)
        if L < 1: raise TypeError('find() takes at least 1 argument (' + L + ' given)')
        sub = args[0]
        if not isinstance(sub, ConcolicStr): sub = ConcolicStr(sub)
        argshasvar |= sub.hasvar
        if L < 2: start = ConcolicInt(0)
        else: start = args[1]
        if not isinstance(start, ConcolicStr): start = ConcolicInt(start)
        argshasvar |= start.hasvar
        if L < 3: end = None
        else: end = args[2]
        if L > 3: raise TypeError('find() takes at most 3 arguments (' + L + ' given)')
        if end is not None:
            if not isinstance(end, ConcolicInt): end = ConcolicInt(end)
            argshasvar |= end.hasvar
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start), int.__int__(end))
            expr = ["str.indexof", self.substr(start, end).expr, sub.expr, start.expr]
        else:
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start))
            expr = ["str.indexof", self.expr, sub.expr, start.expr]
        if argshasvar:
            return ConcolicInt(value, expr)
        else:
            return ConcolicInt(value)

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
        if self.hasvar:
            expr = ["str.in.re", self.expr, ["re.+", ["re.range", "\"0\"", "\"9\""]]]
            return ConcolicBool(value, expr)
        else:
            return ConcolicBool(value)

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
        return ConcolicStr(str.__str__(self).join(array))
        raise NotImplementedError
        # if isinstance(array, ConcolicList):
        #     orig = ConcolicStr(self.value, self.expr)
        #     self.value = ""
        #     self.expr = "\"\""
        #     for element in array.value:
        #         if isinstance(element, ConcolicInt):
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
        assert len(str.__str__(chars)) == 1
        expr = self.expr
        value = str.__str__(self) #.value
        while value.startswith(str.__str__(chars)): #.value):
            value = value[1:]
            expr = ["ite", ["str.prefixof", chars.expr, expr],
                    ["str.substr", expr, 1, ["-", ["str.len", expr], 1]],
                    expr
                    ]
        if self.hasvar or chars.hasvar:
            return ConcolicStr(value, expr)
        else:
            return ConcolicStr(value)

    @staticmethod
    def maketrans(x, y=-1, z=-1): # default arguments are not checked yet
        raise NotImplementedError

    def partition(self, sep):
        raise NotImplementedError

    # TODO: Temp
    def replace(self, old, new, count=-1):
        if not isinstance(old, ConcolicStr): old = ConcolicStr(old)
        if not isinstance(new, ConcolicStr): new = ConcolicStr(new)
        hasvar = self.hasvar or old.hasvar or new.hasvar or (type(count) is ConcolicInt and count.hasvar)
        value = str.__str__(self) #.value
        expr = self.expr
        count = int.__int__(count) #.value
        if count == 0:
            return ConcolicStr(value, expr)
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
        if hasvar:
            return ConcolicStr(n_value, n_expr)
        else:
            return ConcolicStr(n_value)

    def rfind(self, sub, start=-1, end=-1): # default arguments are not checked yet
        return ConcolicInt(str.__str__(self).rfind(sub, start, end))
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
        if self.hasvar or chars.hasvar:
            return ConcolicStr(value, expr)
        else:
            return ConcolicStr(value)

    # TODO: Temp
    def split(self, sep=None, maxsplit=-1):
        if sep is None:
            res = str.__str__(self).split(sep, maxsplit) #raise NotImplementedError
            for i in range(len(res)):
                res[i] = ConcolicStr(res[i])
            return ConcolicList(res)
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
        len_expr = ['+', 1, ['div', ['-', ['str.len', ['str.replaceall', self.expr, sep.expr, sep2.expr]], ['str.len', self.expr]], ['str.len', sep.expr]]]
        return ConcolicList(ans_list, len_expr=len_expr) # 我們目前先不考慮 maxsplit 的限制

    def splitlines(self, keepends=False):
        if keepends: raise NotImplementedError
        if "\\r\\n" in str.__str__(self): #.value:
            return self.split("\\r\\n")
        else:
            return self.split("\\n")

    def startswith(self, prefix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        if not isinstance(prefix, ConcolicStr): prefix = ConcolicStr(prefix)
        value = str.__str__(self).startswith(str.__str__(prefix)) #.value)
        if self.hasvar or prefix.hasvar:
            expr = ["str.prefixof", prefix.expr, self.expr]
            return ConcolicBool(value, expr)
        else:
            return ConcolicBool(value)

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
        return ConcolicStr(value) #'\"' + value + '\"')

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
        if self.hasvar or other.hasvar:
            expr = ["str.++", self.expr, other.expr]
            return ConcolicStr(value, expr)
        else:
            return ConcolicStr(value)

    def __contains__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        value = str.__str__(self).__contains__(str.__str__(other))
        if self.hasvar or other.hasvar:
            expr = ["str.contains", self.expr, other.expr]
            return ConcolicBool(value, expr)
        else:
            return ConcolicBool(value)

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
            expr = ["str.at", self.expr, key.expr]
            if self.hasvar or key.hasvar:
                return ConcolicStr(value, expr)
            else:
                return ConcolicStr(value)
        if not isinstance(key, slice): raise NotImplementedError
        if key.step is not None: raise NotImplementedError
        return self.substr(key.start, key.stop)

    def __gt__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op(">", other)

    def __hash__(self):
        return hash(str.__str__(self))

    def __iter__(self):
        index = ConcolicInt(0)
        while index < self.__len__():
            result = self.__getitem__(index)
            index += ConcolicInt(1)
            yield result

    def __le__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("<=", other)

    def __len__(self):
        value = len(str.__str__(self)) #.value)
        if self.hasvar:
            expr = ["str.len", self.expr]
            return ConcolicInt(value, expr)
        else:
            return ConcolicInt(value)

    def __lt__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("<", other)

    def __mod__(self, tpl):
        if isinstance(tpl, str): return ConcolicStr(str.__str__(self).__mod__(tpl)) # 鴕鳥心態 (NotImplementedError)
        if not isinstance(tpl, tuple): return ConcolicStr(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
        if '%r' in str.__str__(self): return ConcolicStr(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
        if '%i' in str.__str__(self): return ConcolicStr(str.__str__(self).__mod__(tpl)) # raise NotImplementedError
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
                x = lst.pop(0)
                if isinstance(x, ConcolicStr):
                    res += x
                else:
                    if type(x) is int: x = int.__str__(x)
                    res += ConcolicStr(x)
            else:
                res += split_by_str[0]
                remain = str.__str__(res) + split_by_str[1]
                x = lst.pop(0)
                if isinstance(x, ConcolicStr):
                    res += x
                else:
                    res += ConcolicStr(x)
        return res
        raise NotImplementedError

    def __mul__(self, value):
        return ConcolicStr(str.__str__(self).__mul__(value))
        raise NotImplementedError

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
        # return self # "{ConStr, value: %s, expr: %s)" % (self.escape_value(), self.expr)

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
            stop = ConcolicInt(stop)
        if start is None:
            start = ConcolicInt(0)
        if not isinstance(start, ConcolicInt):
            start = ConcolicInt(start)
        if int.__int__(start) < 0:
            start += self.__len__()
        if int.__int__(start) < 0:
            start = ConcolicInt(0)
        if int.__int__(start) >= self.__len__():
            start = self.__len__()
        if int.__int__(stop) < 0:
            stop += self.__len__()
        if int.__int__(stop) < 0:
            stop = ConcolicInt(0)
        if int.__int__(stop) > self.__len__():
            stop = self.__len__()
        value = str.__str__(self)[int.__int__(start):int.__int__(stop)]
        expr = ["str.substr", self.expr, start.expr, (stop-start).expr]
        if self.hasvar or start.hasvar or stop.hasvar:
            return ConcolicStr(value, expr)
        else:
            return ConcolicStr(value)

    def compare_op(self, operator, other):
        val_l = str.__str__(self) #.value
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        val_r = str.__str__(other) #.value
        if operator == "==":
            value = val_l == val_r
            expr = ["=", self.expr, other.expr]
        elif operator == "!=":
            value = val_l != val_r
            expr = ['not', ["=", self.expr, other.expr]]
        elif operator == ">":
            assert len(val_l) == 1 and len(val_r) == 1
            value = val_l > val_r
            expr = ['not', ['str.<=', self.expr, other.expr]]
            # expr = ["str.in.re", self.expr, ["re.range", other.expr, "\"\\xff\""]]
            # expr = ["and", ["not", ["=", self.expr, other.expr]], expr]
        elif operator == "<":
            # assert len(val_l) == 1 and len(val_r) == 1
            value = val_l < val_r
            expr = ['str.<', self.expr, other.expr]
            # expr = ["str.in.re", self.expr, ["re.range", "\"\\x00\"", other.expr]]
            # expr = ["and", ["not", ["=", self.expr, other.expr]], expr]
        elif operator == ">=":
            assert len(val_l) == 1 and len(val_r) == 1
            value = val_l >= val_r
            expr = ['not', ['str.<', self.expr, other.expr]]
            # expr = ["str.in.re", self.expr, ["re.range", other.expr, "\"\\xff\""]]
        elif operator == "<=":
            assert len(val_l) == 1 and len(val_r) == 1
            value = val_l <= val_r
            expr = ['str.<=', self.expr, other.expr]
            # expr = ["str.in.re", self.expr, ["re.range", "\"\\x00\"", other.expr]]
        else:
            raise NotImplementedError
        if self.hasvar or other.hasvar:
            return ConcolicBool(value, expr)
        else:
            return ConcolicBool(value)

    """
       Global functions
    """
    # def len(self):
    #     value = len(self.value)
    #     expr = ["str.len", self.expr]
    #     return ConcolicInt(value, expr)
    def __int__(self):
        if self.hasvar:
            self.isnumber().__bool__()
            expr = ["ite", ["str.prefixof", "\"-\"", self.expr],
                    ["-", ["str.to.int",
                        ["str.substr", self.expr, "1", ["-", ["str.len", self.expr], "1"]]
                        ]
                    ],
                    ["str.to.int", self.expr]
                ]
            return ConcolicInt(int(str.__str__(self)), expr)
        else:
            return ConcolicInt(int(str.__str__(self)))
    # def escape_value(self):
    #     return self.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    #     # value = self.value.replace("\n", "\\n")
    #     # value = value.replace("\r", "\\r")
    #     # value = value.replace("\t", "\\t")
    #     # return value
    def isnumber(self):
        expr = ["ite", ["str.prefixof", "\"-\"", self.expr],
               ["and",
                ["ite", ["=", "(- 1)",
                        ["str.to.int", ["str.substr", self.expr, "1", ["-", ["str.len", self.expr], "1"]]]
                       ],
                 "false",
                 "true"
                ],
                [">", ["str.len", self.expr], "1"]
               ],
               ["ite", ["=", "(- 1)", ["str.to.int", self.expr]],
                 "false",
                 "true"
               ]
              ]
        my_str = str.__str__(self)
        if my_str.startswith('-'): my_str = my_str[1:]
        if self.hasvar:
            return ConcolicBool(my_str.isdigit(), expr)
        else:
            return ConcolicBool(my_str.isdigit())
    # def store(self, index, value):
    #     if isinstance(index, ConcolicInt):
    #         index = index.value
    #     self.value[index] = value
