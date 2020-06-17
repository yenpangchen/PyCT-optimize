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

    def __new__(cls, expr, value=None):
        if value is not None:
            return str.__new__(cls, value)
        else:
            if isinstance(expr, str): expr = expr.replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t")
            return str.__new__(cls, expr.replace("\"", "", 1).replace("\"", "", -1))

    def __init__(self, expr, value=None):
        if isinstance(expr, str): expr = expr.replace("\r", "\\r").replace("\n", "\\n").replace("\t", "\\t")
        if value is None: expr = "\"" + expr + "\"" # 這一步很重要，因為 SMT solver 分不清楚 var name 和 string const 的差別，所以必須藉由在兩側加上雙引號的方式去區別兩者！
        self.expr = expr
        log.debug("  ConStr, value: %s, expr: %s" % (self, self.expr))

    def __add__(self, other):
        value = str(self) + str(other)
        expr = ["str.++", self.expr, other.expr]
        return ConcolicStr(expr, value)

    def __contains__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        value = str(other) in str(self)
        expr = ["str.contains", self.expr, other.expr]
        return ConcolicType(expr, value)

    def __len__(self):
        value = len(str(self)) #.value)
        expr = ["str.len", self.expr]
        return ConcolicInteger(expr, value)

    """
       Global functions
    """
    # def len(self):
    #     value = len(self.value)
    #     expr = ["str.len", self.expr]
    #     return ConcolicInteger(expr, value)

    def int(self):
        value = int(self.value)
        expr = ["ite", ["str.prefixof", "\"-\"", self.expr],
                ["-", ["str.to.int", 
                       ["str.substr", self.expr, "1", ["-", ["str.len", self.expr], "1"]]
                      ]
                ],
                ["str.to.int", self.expr]
               ]
        return ConcolicInteger(expr, value)

    def get_index(self, index):
        if isinstance(index, int):
            index = ConcolicInteger(index, index)
        value = self.value[index.value]
        if index.value < 0:
            expr = ["str.at", self.expr, ["+", ["str.len", self.expr], index.expr]]
        else:
            expr = ["str.at", self.expr, index.expr]
        return ConcolicStr(expr, value)
    
    # def escape_value(self):
    #     return self.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    #     # value = self.value.replace("\n", "\\n")
    #     # value = value.replace("\r", "\\r")
    #     # value = value.replace("\t", "\\t")
    #     # return value

    # def __str__(self):
    #     return "{ConStr, value: %s, expr: %s)" % (self.escape_value(), self.expr)


    # def contains(self, other):
    #     value = other.value in self.value
    #     expr = ["str.contains", self.expr, other.expr]
    #     return ConcolicType(expr, value)

    def not_contains(self, other):
        value = other.value not in self.value
        expr = ["not", ["str.contains", self.expr, other.expr]]
        return ConcolicType(expr, value)

    def get_slice(self, start=None, stop=None):
        stop = len(self) if stop is None else ConcolicInteger(stop)
        start = ConcolicInteger(0) if start is None else ConcolicInteger(start)
        value = str(self)[int(start):int(stop)]
        if int(start) < 0:
            start.expr = ["+", ["str.len", self.expr], start.expr]
        if int(stop) < 0:
            stop.expr = ["+", ["str.len", self.expr], stop.expr]
        expr = ["str.substr", self.expr, start.expr, (stop-start).expr]
        return ConcolicStr(expr, value)

    
    def find(self, findstr, beg=ConcolicInteger(0), end=None):
        if not isinstance(findstr, ConcolicStr): findstr = ConcolicStr(findstr)
        if not isinstance(beg, ConcolicInteger): beg = ConcolicInteger(beg)
        if end is not None:
            raise NotImplementedError
            # partial = self.get_slice(beg, end)
            # value = partial.value.find(findstr.value, beg.value, end.value)
            # expr = ["str.indexof", partial.expr, findstr.expr, beg.expr]
        else:
            value = str(self).find(str(findstr), int(beg))
            expr = ["str.indexof", self.expr, findstr.expr, beg.expr]

        return ConcolicInteger(expr, value)

    def startswith(self, prefix):
        if not isinstance(prefix, ConcolicStr): prefix = ConcolicStr(prefix)
        value = str(self).startswith(str(prefix)) #.value)
        expr = ["str.prefixof", prefix.expr, self.expr]
        return ConcolicType(expr, value)

    def endswith(self, suffix):
        value = self.value.endswith(suffix.value)
        expr = ["str.suffixof", suffix.expr, self.expr]
        return ConcolicType(expr, value)

    # TODO: Temp 
    def split(self, sep=None, maxsplit=None):
        if isinstance(maxsplit, ConcolicInteger):
            maxsplit = int(maxsplit) #.value
        if sep is not None:
            if len(str(self)) == 0:
                return ConcolicList([ConcolicStr("")]) # ConcolicList([ConcolicStr("\"\"")])
        else:
            sep = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
            if len(str(self)) == 0:
                return ConcolicList([ConcolicStr("\"\"")])
        if not isinstance(sep, ConcolicStr): #str):
            sep = ConcolicStr(sep)
        if maxsplit == 0 or str(sep) not in str(self): #.value:
            return ConcolicList([self])
        else:
            raise NotImplementedError
            sep_idx = self.find(sep)
            if maxsplit is None:
                return ConcolicList([self.get_slice(None, sep_idx)]) + \
                   ConcolicList(self.get_slice(sep_idx + 1).split(sep))
            else:
                return ConcolicList([self.get_slice(None, sep_idx)]) + \
                   ConcolicList(self.get_slice(sep_idx + 1).split(sep, maxsplit - 1))

    def splitlines(self):
        if "\\r\\n" in self.value:
            return self.split("\\r\\n")
        else:
            return self.split("\\n")

    def is_number(self):
        value = True
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
        return ConcolicType(expr, value)

    def isdigit(self):
        value = self.value.isdigit()
        expr = ["str.in.re", self.expr, ["re.+", ["re.range", "\"0\"", "\"9\""]]]
        return ConcolicType(expr, value)

    # TODO: Temp 
    def join(self, array):
        # TODO
        if isinstance(array, ConcolicList):
            orig = ConcolicStr(self.expr, self.value)
            self.value = ""
            self.expr = "\"\""
            for element in array.value:
                if isinstance(element, ConcolicInteger):
                    append = ConcolicStr(element.get_str())
                if isinstance(element, ConcolicStr):
                    append = element
                else:
                    append = ConcolicStr('\"' + str(element) + '\"')
                self = self.__add__(append)
                self = self.__add__(orig)

        else:
            log.warrning("Not implemented: str.join(<other type>)")
                


    # Return a new string, no continued expr
    # TODO: Temp 
    def lower(self):
        return ConcolicStr(str(self).lower())
        # return ConcolicStr('\"' + value + '\"')

    # Return a new string, no continued expr
    # TODO: Temp 
    def upper(self):
        value = self.value.upper()
        return ConcolicStr('\"' + value + '\"')

    # TODO: Temp 
    def replace(self, old, new, maxreplace=-1):
        if not isinstance(old, ConcolicStr): old = ConcolicStr(old)
        if not isinstance(new, ConcolicStr): new = ConcolicStr(new)
        value = str(self) #.value
        expr = self.expr

        if isinstance(maxreplace, ConcolicInteger):
            maxreplace = int(maxreplace) #.value

        if maxreplace == 0:
            return ConcolicStr(expr, value)
        
        n_value = value.replace(str(old), str(new), 1)
        n_expr = ["str.replace", expr, old.expr, new.expr]
        if maxreplace > 0:
            maxreplace -= 1

        while n_value != value and (maxreplace == -1 or maxreplace > 0):
            value = n_value
            expr = n_expr
            n_value = value.replace(str(old), str(new), 1)
            n_expr = ["str.replace", expr, old.expr, new.expr]
            if maxreplace > 0:
                maxreplace -= 1

        return ConcolicStr(n_expr, n_value)

    # TODO: Concrete value 
    def count(self, sub):
        return ConcolicInteger(str(self).count(sub))
        # return ConcolicInteger(count)


    # TODO: Temp 
    def strip(self, char=None):
        return self.lstrip(char).rstrip(char)


    # TODO: Temp 
    def lstrip(self, char=None):
        if char is None:
            char = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
        expr = self.expr
        value = str(self) #.value
        while value.startswith(str(char)): #.value):
            value = value[1:]
            expr = ["ite", ["str.prefixof", char.expr, expr],
                    ["str.substr", expr, 1, ["-", ["str.len", expr], 1]],
                    expr
                   ]
        return ConcolicStr(expr, value)

    # TODO: Temp 
    def rstrip(self, char=None):
        if char is None:
            char = ConcolicStr(" ") # ConcolicStr("\" \"", " ")
        expr = self.expr
        value = str(self) #.value
        while value.endswith(str(char)): #.value):
            value = value[:-1]
            expr = ["ite", ["str.suffixof", char.expr, expr],
                    ["str.substr", expr, 0, ["-", ["str.len", expr], 1]],
                    expr
                   ]
        return ConcolicStr(expr, value)


    def store(self, index, value):
        if isinstance(index, ConcolicInteger):
            index = index.value
        self.value[index] = value

    def index(self, target):
        expr = ["str.indexof", self.expr, target.expr, "0"]
        value = self.value.index(target.value)
        return ConcolicInteger(expr, value)

    def __eq__(self, other):
        if not isinstance(other, ConcolicStr): other = ConcolicStr(other)
        return self.compare_op("==", other)

    def compare_op(self, operator, other):
        val_l = str(self) #.value
        val_r = str(other) #.value
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
            return None

        return ConcolicType(expr, value)

    
    # TODO
    def __getitem__(self, key):
        if not isinstance(key, slice): raise NotImplementedError
        if key.step is not None: raise NotImplementedError
        return self.get_slice(key.start, key.stop)
