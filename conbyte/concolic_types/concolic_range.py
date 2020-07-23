# Copyright: copyright.txt
from .concolic_bool import *
from .concolic_int import *

log = logging.getLogger("ct.con.range")

"""
Classes:
    ConcolicRange
"""

class ConcolicRange: #():
    def __init__(self, start, end=None, step=None):
        if end is None:
            self.start = 0 #ConcolicInt(0)
            self.end = start
        else:
            self.start = start
            self.end = end
        if step is None:
            self.step = 1 #ConcolicInt(1)
        else:
            self.step = step
        # See if the args violates range()
        range(self.start, self.end, self.step)
        if not isinstance(self.start, ConcolicInt): self.start = ConcolicInt(self.start)
        if not isinstance(self.end, ConcolicInt): self.end = ConcolicInt(self.end)
        if not isinstance(self.step, ConcolicInt): self.step = ConcolicInt(self.step)

    def __iter__(self):
        current = self.start
        while True:
            if self.step > 0:
                if current < self.end:
                    result = current
                    current += self.step
                    yield result
                else:
                    break
            else: # self.step < 0
                if current > self.end:
                    result = current
                    current += self.step
                    yield result
                else:
                    break

    def __getitem__(self, key):
        if isinstance(key, slice) and \
            key.start == None and \
            key.stop == None and \
            key.step == -1:
            if self.step > 0:
                if (self.end - self.start) % self.step == 0:
                    k = (self.end - self.start) // self.step - 1
                else:
                    k = (self.end - self.start) // self.step
                start = self.start + k * self.step
                end = self.start - self.step
                step = -self.step
                return ConcolicRange(start, end, step)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    # def next_iter(self):
    #     if self.step.value > 0:
    #         cond_val = self.current.value < self.end.value
    #         cond_exp = "nil"
    #     else:
    #         cond_val = self.current.value > self.end.value
    #         cond_exp = "nil"

    #     if cond_val:
    #         ret = self.current
    #         self.current += self.step
    #     else:
    #         ret = None
    #     return ConcolicBool(cond_val, cond_exp), ret

    # def __str__(self):
    #     return "(Inter s: %s, e: %s, c: %s, step: %s)" % (self.start, self.end, self.current, self.step)

    # def reverse(self):
    #     self.step.negate()
    #     tmp = self.end + self.step
    #     self.end  = self.start + self.step
    #     self.start = tmp
    #     self.current = self.start
