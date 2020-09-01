import copy, logging
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

    def __add__(self, value, /): # <slot wrapper '__add__' of 'str' objects>
        """Return self+value."""
        log.debug("  ConStr, __add__ is called")
        return self._bin_op('__add__', value)

    # __class__, <class 'type'>

    def __contains__(self, key, /): # <slot wrapper '__contains__' of 'str' objects>
        """Return key in self."""
        log.debug("  ConStr, __contains__ is called")
        return self._bin_op('__contains__', key)

    # __delattr__, <slot wrapper '__delattr__' of 'object' objects>

    # __dir__, <method '__dir__' of 'object' objects>

    def __eq__(self, value, /): # <slot wrapper '__eq__' of 'str' objects>
        """Return self==value."""
        log.debug("  ConStr, __eq__ is called")
        return self._bin_op('__eq__', value)

    def __format__(self, format_spec, /): # <method '__format__' of 'str' objects> TODO
        """Return a formatted version of the string as described by format_spec."""
        log.debug("  ConStr, __format__ is called")
        return ConcolicObject(super().__format__(unwrap(format_spec)))

    def __ge__(self, value, /): # <slot wrapper '__ge__' of 'str' objects>
        """Return self>=value."""
        log.debug("  ConStr, __ge__ is called")
        return self._bin_op('__ge__', value)

    # def __getattribute__(self, name, /): # <slot wrapper '__getattribute__' of 'str' objects>
    #     """Return getattr(self, name)."""

    # TODO: 罪魁禍首
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
        return self._substr(key.start, key.stop)

    # def __getnewargs__(...): # <method '__getnewargs__' of 'str' objects>

    def __gt__(self, value, /): # <slot wrapper '__gt__' of 'str' objects>
        """Return self>value."""
        log.debug("  ConStr, __gt__ is called")
        return self._bin_op('__gt__', value)

    def __hash__(self, /): # <slot wrapper '__hash__' of 'str' objects>
        """Return hash(self).""" # TODO: Is the inverse operation well-known?
        log.debug("  ConStr, __hash__ is called")
        return ConcolicObject(super().__hash__())

    # __init__, <slot wrapper '__init__' of 'object' objects>

    # __init_subclass__, <built-in method __init_subclass__ of type object at 0x9036c0>

    def __iter__(self, /): # <slot wrapper '__iter__' of 'str' objects>
        """Implement iter(self)."""
        log.debug("  ConStr, __iter__ is called")
        index = ConcolicObject(0)
        while index < self.__len__(): # Note this branch must be added in order to make this iterator work!
            result = self.__getitem__(index)
            index += ConcolicObject(1)
            yield result

    def __le__(self, value, /): # <slot wrapper '__le__' of 'str' objects>
        """Return self<=value."""
        log.debug("  ConStr, __le__ is called")
        return self._bin_op('__le__', value)

    def __len__(self, /): # <slot wrapper '__len__' of 'str' objects>
        """Return len(self)."""
        log.debug("  ConStr, __len__ is called")
        value = super().__len__()
        expr = ["str.len", self]
        return ConcolicObject(value, expr)

    def __lt__(self, value, /): # <slot wrapper '__lt__' of 'str' objects>
        """Return self<value."""
        log.debug("  ConStr, __lt__ is called")
        return self._bin_op('__lt__', value)

    def __mod__(self, other, /): # <slot wrapper '__mod__' of 'str' objects> TODO: move from approximation to exact computation
        # Meaning of modifiers is explained here: https://docs.python.org/3/library/stdtypes.html#printf-style-string-formatting
        """Return self%value.""" # I renamed the argument to "other" for convenience.
        log.debug("  ConStr, __mod__ is called")
        value = super().__mod__(unwrap(other))
        if not isinstance(other, tuple): return ConcolicObject(value) # TODO: 鴕鳥心態
        # One split example: ['abcd%def%dga%ib%dc%idefg']
        # -> [['abcd', 'ef', 'ga%ib', 'c%idefg']]
        # -> [['abcd', '%d', 'ef', '%d', 'ga%ib', '%d', 'c%idefg']]
        # -> ['abcd', '%d', 'ef', '%d', 'ga%ib', '%d', 'c%idefg'] (*1)
        # -> [['abcd'], ['%d'], ['ef'], ['%d'], ['ga', 'b'], ['%d'], ['c', 'defg']] (*2)
        # -> [['abcd'], ['%d'], ['ef'], ['%d'], ['ga', '%i', 'b'], ['%d'], ['c', '%i', 'defg']] (*3)
        # -> ['abcd', '%d', 'ef', '%d', 'ga', '%i', 'b', '%d', 'c', '%i', 'defg'] (*4)
        res_list = [unwrap(self)]
        ds = ['%d', '%i', '%o', '%u', '%x', '%X', '%e', '%E', '%f', '%F', '%g', '%G', '%c', '%r', '%s', '%a', '%%']
        for d in ds:
            res_list = list(map(lambda s: s.split(d), res_list)) # (*1 -> *2)
            def insert_delimiter(lst, d): res = [d] * (len(lst) * 2 - 1); res[0::2] = lst; return res
            res_list = list(map(lambda sublist: insert_delimiter(sublist, d), res_list)) # (*2 -> *3)
            res_list = [item for sublist in res_list for item in sublist] # (*3 -> *4)
        other = list(other) # convert from tuple to list
        res_str = self.__class__('')
        for s in res_list:
            if s not in ds:
                res_str += s
            else: # currently only supports '%d', '%i', '%r', '%s', '%%'. For other delimiters we just call str(e) for simplicity.
                if s == '%%':
                    res_str += '%'
                    continue
                if not other: # element list already empty
                    break
                e = other.pop(0)
                if s in ['%d', '%i']:
                    if isinstance(e, Concolic) and hasattr(e, '__int2__'):
                        e = e.__int2__().__str2__()
                    else:
                        try: e = int(e)
                        except: e = 0
                        e = str(e)
                elif s == '%r':
                    if isinstance(e, Concolic): # in concolic environment, we don't distinguish str() from repr()
                        if hasattr(e, '__str2__'): e = e.__str2__()
                    else:
                        try: e = repr(e)
                        except: e = ''
                else: # include the case '%s'
                    if isinstance(e, Concolic):
                        if hasattr(e, '__str2__'): e = e.__str2__()
                    else:
                        try: e = str(e)
                        except: e = ''
                res_str += e
        return res_str if unwrap(res_str) == value else value # TODO: difficult to pick all engines of elements in "other" here, so we omit truncation of expression here.

    def __mul__(self, value, /): # <slot wrapper '__mul__' of 'str' objects>
        """Return self*value."""
        log.debug("  ConStr, __mul__ is called")
        return self._bin_op('__mul__', value)

    def __ne__(self, value, /): # <slot wrapper '__ne__' of 'str' objects>
        """Return self!=value."""
        log.debug("  ConStr, __ne__ is called")
        return self._bin_op('__ne__', value)

    # __reduce__, <method '__reduce__' of 'object' objects>

    # __reduce_ex__, <method '__reduce_ex__' of 'object' objects>

    # def __repr__(self, /): # <slot wrapper '__repr__' of 'str' objects>
    #     """Return repr(self)."""

    def __rmod__(self, value, /): # <slot wrapper '__rmod__' of 'str' objects> TODO
        """Return value%self."""
        log.debug("  ConStr, __rmod__ is called")
        return super().__rmod__(unwrap(value))

    def __rmul__(self, value, /): # <slot wrapper '__rmul__' of 'str' objects>
        """Return value*self."""
        log.debug("  ConStr, __rmul__ is called")
        return self._bin_op('__rmul__', value)

    # __setattr__, <slot wrapper '__setattr__' of 'object' objects>

    # def __sizeof__(self, /): # <method '__sizeof__' of 'str' objects>
    #     """Return the size of the string in memory, in bytes."""

    # def __str__(self, /): # <slot wrapper '__str__' of 'str' objects>
    #     """Return str(self)."""

    # __subclasshook__, <built-in method __subclasshook__ of type object at 0x9036c0>

    def capitalize(self, /): # <method 'capitalize' of 'str' objects> TODO
        """Return a capitalized version of the string.\n\nMore specifically, make the first character have upper case and the rest lower case."""
        log.debug("  ConStr, capitalize is called")
        return ConcolicObject(super().capitalize())

    def casefold(self, /): # <method 'casefold' of 'str' objects> TODO
        """Return a version of the string suitable for caseless comparisons."""
        log.debug("  ConStr, casefold is called")
        return ConcolicObject(super().casefold())

    def center(self, width, fillchar=' ', /): # <method 'center' of 'str' objects> TODO
        """Return a centered string of length width.\n\nPadding is done using the specified fill character (default is a space)."""
        log.debug("  ConStr, center is called")
        return ConcolicObject(super().center(unwrap(width), unwrap(fillchar)))

    def count(self, *args): # <method 'count' of 'str' objects>
        """S.count(sub[, start[, end]]) -> int\n\nReturn the number of non-overlapping occurrences of substring sub in\nstring S[start:end].  Optional arguments start and end are\ninterpreted as in slice notation."""
        log.debug("  ConStr, count is called"); args = copy.copy(args) # 斷開魂結，斷開鎖鏈，斷開一切的牽連！(by 美江牧師)
        if isinstance(args, tuple): args = list(args)
        value = super().count(*map(unwrap, args))
        if not isinstance(args[0], Concolic):
            try: args[0] = str(args[0])
            except: args[0] = ''
            args[0] = self.__class__(args[0])
        if len(args) < 2: args.append(0)
        if not isinstance(args[1], Concolic):
            try: args[1] = int(args[1])
            except: args[1] = 0
            args[1] = ConcolicObject(args[1]) # ConcolicInt
        if len(args) < 3: args.append(self.__len__())
        if not isinstance(args[2], Concolic):
            try: args[2] = int(args[2])
            except: args[2] = self.__len__() # Default values are also ok to have expressions.
            args[2] = ConcolicObject(args[2]) # ConcolicInt
        main = self._substr(args[1], args[2])
        # args[0] = add_extend_vars('String', args[0])
        tokens = ["ite", ["<=", ["str.len", args[0]], "0"], ["+", "1", ["str.len", main]], ["div", ["-", ["str.len", ["str.replaceall", main, args[0], ["str.++", args[0], args[0]]]], ["str.len", main]], ["str.len", args[0]]]]
        return ConcolicObject(value, tokens)

    def encode(self, /, encoding='utf-8', errors='strict'): # <method 'encode' of 'str' objects> TODO
        """Encode the string using the codec registered for encoding."""
        log.debug("  ConStr, encode is called")
        return ConcolicObject(super().encode(unwrap(encoding), unwrap(errors)))

    def endswith(self, suffix, start=None, end=None): # default arguments are not checked yet
        if start is not None or end is not None: raise NotImplementedError
        if not isinstance(suffix, ConcolicStr): suffix = ConcolicStr(suffix)
        value = str.__str__(self).endswith(str.__str__(suffix))
        expr = ["str.suffixof", suffix, self]
        return ConcolicObject(value, expr)

    def expandtabs(self, /, tabsize=8): # <method 'expandtabs' of 'str' objects> TODO
        """Return a copy where all tab characters are expanded using spaces.\n\nIf tabsize is not given, a tab size of 8 characters is assumed."""
        log.debug("  ConStr, expandtabs is called")
        return ConcolicObject(super().expandtabs(unwrap(tabsize)))

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
            expr = ["str.indexof", self._substr(start, end), sub, start]
        else:
            value = str.__str__(self).find(str.__str__(sub), int.__int__(start))
            expr = ["str.indexof", self, sub, start]
        return ConcolicObject(value, expr)

    def format(self, *args, **kwargs): # <method 'format' of 'str' objects> TODO
        """S.format(*args, **kwargs) -> str\n\nReturn a formatted version of S, using substitutions from args and kwargs.\nThe substitutions are identified by braces ('{' and '}')."""
        log.debug("  ConStr, format is called"); args = [unwrap(arg) for arg in args]; kwargs = {k: unwrap(v) for (k, v) in kwargs.items()}
        return ConcolicObject(super().format(*args, **kwargs))

    def format_map(self, *args, **kwargs): # <method 'format_map' of 'str' objects> TODO
        """S.format_map(mapping) -> str\n\nReturn a formatted version of S, using substitutions from mapping.\nThe substitutions are identified by braces ('{' and '}')."""
        log.debug("  ConStr, format_map is called"); args = [unwrap(arg) for arg in args]; kwargs = {k: unwrap(v) for (k, v) in kwargs.items()}
        return ConcolicObject(super().format_map(*args, **kwargs))

    def index(self, *args):
        res = self.find(args)
        if res == -1: str.__str__(self).index(args) # raise the built-in error
        return res

    def isalnum(self, /): # <method 'isalnum' of 'str' objects> TODO
        """Return True if the string is an alpha-numeric string, False otherwise.\n\nA string is alpha-numeric if all characters in the string are alpha-numeric and\nthere is at least one character in the string."""
        log.debug("  ConStr, isalnum is called")
        return ConcolicObject(super().isalnum())

    def isalpha(self, /): # <method 'isalpha' of 'str' objects> TODO
        """Return True if the string is an alphabetic string, False otherwise.\n\nA string is alphabetic if all characters in the string are alphabetic and there\nis at least one character in the string."""
        log.debug("  ConStr, isalpha is called")
        return ConcolicObject(super().isalpha())

    def isascii(self, /): # <method 'isascii' of 'str' objects> TODO
        """Return True if all characters in the string are ASCII, False otherwise.\n\nASCII characters have code points in the range U+0000-U+007F.\nEmpty string is ASCII too."""
        log.debug("  ConStr, isascii is called")
        return ConcolicObject(super().isascii())

    def isdecimal(self, /): # <method 'isdecimal' of 'str' objects> TODO
        """Return True if the string is a decimal string, False otherwise.\n\nA string is a decimal string if all characters in the string are decimal and\nthere is at least one character in the string."""
        log.debug("  ConStr, isdecimal is called")
        return ConcolicObject(super().isdecimal())

    def isdigit(self, /): # <method 'isdigit' of 'str' objects>
        """Return True if the string is a digit string, False otherwise.\n\nA string is a digit string if all characters in the string are digits and there\nis at least one character in the string."""
        log.debug("  ConStr, isdigit is called")
        value = super().isdigit()
        expr = ["str.in.re", self, ["re.+", ["re.range", py2smt('0'), py2smt('9')]]]
        # Question: Is this expression equivalent to ["not", ["=", "-1", ["str.to.int", self]]]?
        return ConcolicObject(value, expr)

    def isidentifier(self, /): # <method 'isidentifier' of 'str' objects> TODO
        """Return True if the string is a valid Python identifier, False otherwise.\n\nCall keyword.iskeyword(s) to test whether string s is a reserved identifier,\nsuch as "def" or "class"."""
        log.debug("  ConStr, isidentifier is called")
        return ConcolicObject(super().isidentifier())

    def islower(self, /): # <method 'islower' of 'str' objects> TODO
        """Return True if the string is a lowercase string, False otherwise.\n\nA string is lowercase if all cased characters in the string are lowercase and\n there is at least one cased character in the string."""
        log.debug("  ConStr, islower is called")
        return ConcolicObject(super().islower())

    def isnumeric(self, /): # <method 'isnumeric' of 'str' objects> TODO
        """Return True if the string is a numeric string, False otherwise.\n\nA string is numeric if all characters in the string are numeric and there is at\nleast one character in the string."""
        log.debug("  ConStr, isnumeric is called")
        return ConcolicObject(super().isnumeric())

    def isprintable(self, /): # <method 'isprintable' of 'str' objects> TODO
        """Return True if the string is printable, False otherwise.\n\nA string is printable if all of its characters are considered printable in\nrepr() or if it is empty."""
        log.debug("  ConStr, isprintable is called")
        return ConcolicObject(super().isprintable())

    def isspace(self, /): # <method 'isspace' of 'str' objects> TODO
        """Return True if the string is a whitespace string, False otherwise.\n\nA string is whitespace if all characters in the string are whitespace and there\nis at least one character in the string."""
        log.debug("  ConStr, isspace is called")
        return ConcolicObject(super().isspace())

    def istitle(self, /): # <method 'istitle' of 'str' objects> TODO
        """Return True if the string is a title-cased string, False otherwise.\n\nIn a title-cased string, upper- and title-case characters may only\nfollow uncased characters and lowercase characters only cased ones."""
        log.debug("  ConStr, istitle is called")
        return ConcolicObject(super().istitle())

    def isupper(self, /): # <method 'isupper' of 'str' objects> TODO
        """Return True if the string is an uppercase string, False otherwise.\n\nA string is uppercase if all cased characters in the string are uppercase and\nthere is at least one cased character in the string."""
        log.debug("  ConStr, isupper is called")
        return ConcolicObject(super().isupper())

    def join(self, iterable, /): # <method 'join' of 'str' objects> TODO
        """Concatenate any number of strings.\n\nThe string whose method is called is inserted in between each given string.\nThe result is returned as a new string.\n\nExample: '.'.join(['ab', 'pq', 'rs']) -> 'ab.pq.rs'"""
        log.debug("  ConStr, join is called")
        return ConcolicObject(super().join(unwrap(iterable)))

    def ljust(self, width, fillchar=' ', /): # <method 'ljust' of 'str' objects> TODO
        """Return a left-justified string of length width.\n\nPadding is done using the specified fill character (default is a space)."""
        log.debug("  ConStr, ljust is called")
        return ConcolicObject(super().ljust(unwrap(width), unwrap(fillchar)))

    def lower(self, /): # <method 'lower' of 'str' objects> TODO
        """Return a copy of the string converted to lowercase."""
        log.debug("  ConStr, lower is called")
        return ConcolicObject(super().lower())

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

    # maketrans, <built-in method maketrans of type object at 0x9036c0> (@staticmethod)

    def partition(self, sep, /): # <method 'partition' of 'str' objects> TODO
        """Partition the string into three parts using the given separator."""
        log.debug("  ConStr, partition is called")
        return ConcolicObject(super().partition(unwrap(sep)))

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

    def rfind(self, *args, **kwargs): # <method 'rfind' of 'str' objects> TODO
        """S.rfind(sub[, start[, end]]) -> int"""
        log.debug("  ConStr, rfind is called"); args = [unwrap(arg) for arg in args]; kwargs = {k: unwrap(v) for (k, v) in kwargs.items()}
        return ConcolicObject(super().rfind(*args, **kwargs))

    def rindex(self, *args, **kwargs): # <method 'rindex' of 'str' objects> TODO
        """S.rindex(sub[, start[, end]]) -> int"""
        log.debug("  ConStr, rindex is called"); args = [unwrap(arg) for arg in args]; kwargs = {k: unwrap(v) for (k, v) in kwargs.items()}
        return ConcolicObject(super().rindex(*args, **kwargs))

    def rjust(self, width, fillchar=' ', /): # <method 'rjust' of 'str' objects> TODO
        """Return a right-justified string of length width.\n\nPadding is done using the specified fill character (default is a space)."""
        log.debug("  ConStr, rjust is called")
        return ConcolicObject(super().rjust(unwrap(width), unwrap(fillchar)))

    def rpartition(self, sep, /): # <method 'rpartition' of 'str' objects> TODO
        """Partition the string into three parts using the given separator."""
        log.debug("  ConStr, rpartition is called")
        return ConcolicObject(super().rpartition(unwrap(sep)))

    def rsplit(self, /, sep=None, maxsplit=-1): # <method 'rsplit' of 'str' objects> TODO
        """Return a list of the words in the string, using sep as the delimiter string."""
        log.debug("  ConStr, rsplit is called")
        return ConcolicObject(super().rsplit(unwrap(sep), unwrap(maxsplit)))

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
                ans_list.append(substr._substr(stop=split_index))
                substr = substr._substr(start=split_index+sep_len)
            elif maxsplit > 0:
                ans_list.append(substr._substr(stop=split_index))
                substr = substr._substr(start=split_index+sep_len)
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

    def swapcase(self, /): # <method 'swapcase' of 'str' objects> TODO
        """Convert uppercase characters to lowercase and lowercase characters to uppercase."""
        log.debug("  ConStr, swapcase is called")
        return ConcolicObject(super().swapcase())

    def title(self, /): # <method 'title' of 'str' objects> TODO
        """Return a version of the string where each word is titlecased.\n\nMore specifically, words start with uppercased characters and all remaining\ncased characters have lower case."""
        log.debug("  ConStr, title is called")
        return ConcolicObject(super().title())

    def translate(self, table, /): # <method 'translate' of 'str' objects> TODO
        """Replace each character in the string using the given translation table."""
        log.debug("  ConStr, translate is called")
        return ConcolicObject(super().translate(unwrap(table)))

    def upper(self, /): # <method 'upper' of 'str' objects> TODO
        """Return a copy of the string converted to uppercase."""
        log.debug("  ConStr, upper is called")
        return ConcolicObject(super().upper())

    def zfill(self, width, /): # <method 'zfill' of 'str' objects> TODO
        """Pad a numeric string with zeros on the left, to fill a field of the given width.\n\nThe string is never truncated."""
        log.debug("  ConStr, zfill is called")
        return ConcolicObject(super().zfill(unwrap(width)))

    ################################################################
    # Other helper methods are implemented in the following section.
    ################################################################

    def _bin_op(self, op, other):
        if op == '__add__':
            value = super().__add__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            expr = ['str.++', self, other]
            return ConcolicObject(value, expr)
        elif op == '__contains__':
            value = super().__contains__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            expr = ['str.contains', self, other]
            return ConcolicObject(value, expr)
        elif op == '__eq__':
            value = super().__eq__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            expr = ['=', self, other]
            return ConcolicObject(value, expr)
        elif op == '__ge__':
            value = super().__ge__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            # expr = ['str.<=', other, self]
            expr = ["str.in.re", self, ["re.range", other, "\"\\xff\""]]
            return ConcolicObject(value, expr)
        elif op == '__gt__':
            value = super().__gt__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            # expr = ['str.<', other, self]
            # self = add_extend_vars('String', self)
            # other = add_extend_vars('String', other)
            expr = ["str.in.re", self, ["re.range", other, "\"\\xff\""]]
            expr = ["and", ["not", ["=", self, other]], expr]
            return ConcolicObject(value, expr)
        elif op == '__le__':
            value = super().__le__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            # expr = ['str.<=', self, other]
            expr = ["str.in.re", self, ["re.range", "\"\\x00\"", other]]
            return ConcolicObject(value, expr)
        elif op == '__lt__':
            value = super().__lt__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            # expr = ['str.<', self, other]
            # self = add_extend_vars('String', self)
            # other = add_extend_vars('String', other)
            expr = ["str.in.re", self, ["re.range", "\"\\x00\"", other]]
            expr = ["and", ["not", ["=", self, other]], expr]
            return ConcolicObject(value, expr)
        elif op == '__mul__': # TODO: Expressions not implemented
            return ConcolicObject(super().__mul__(unwrap(other)))
        elif op == '__ne__':
            value = super().__ne__(unwrap(other))
            if not isinstance(other, Concolic):
                try: other = str(other)
                except: other = ''
                other = self.__class__(other)
            expr = ['not', ['=', self, other]]
            return ConcolicObject(value, expr)
        elif op == '__rmul__': # TODO: Expressions not implemented
            return ConcolicObject(super().__rmul__(unwrap(other)))
        else:
            raise NotImplementedError

    def _is_int(self):
        log.debug("  ConStr, _is_int is called")
        import re; INT_RE = re.compile(r"^[-]?\d+$"); value = INT_RE.match(unwrap(self)) is not None
        # TODO: Can this regular expression be written in SMT syntax?
        # self = add_extend_vars('String', self)
        expr = ["not", ["=", py2smt(-1), ["ite", ["str.prefixof", py2smt('-'), self],
                                                 ["str.to.int", ["str.substr", self, "1", ["str.len", self]]],
                                                 ["str.to.int", self]]]]
        return ConcolicObject(value, expr)

    def _substr(self, start=None, stop=None): # stop is exclusive...
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

    def __int2__(self):
        log.debug("  ConStr, __int2__ is called")
        self._is_int().__bool__() # our handmade branch in order to produce more successful testcases
        value = int(self)
        # self = add_extend_vars('String', self)
        expr = ["ite", ["str.prefixof", py2smt('-'), self],
                       ["-", ["str.to.int", ["str.substr", self, "1", ["str.len", self]]]],
                       ["str.to.int", self]] # For better results, avoid using ["str.replace", self, "-", ""] in the above line.
        return ConcolicObject(value, expr)

    def __str2__(self):
        log.debug("  ConStr, __str2__ is called")
        return self
