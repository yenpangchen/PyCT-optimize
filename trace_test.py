import sys
import inspect
import os
import arg_wrapper
import logging
import json
from try_run_pyct import pyct_test_transformers
import traceCall as tc


class testClass():
    def t(self,a):
        if a==0:
            return True
        else:
            return False
        
def branch_test_nothing():
    a()
    b()

def a():
    c()

def b():
    pass

def c():
    pass

def branch_test(b,a):
        if a==0:
            return True
        else:
            return False
        
def branch_test_matrix(a):
        if a[0]==0:
            return True
        else:
            return False

def branch_test_dict(a):
        if a['k']==0:
            return True
        else:
            return False
        
def branch_test_kwarg(a,**kwargs):
        if kwargs['kw']==0:
            return True
        else:
            return False
        
def branch_test_arg(*args):
        if len(args)>2:
            return True
        else:
            return False
        
def branch_test_type(a,*args,b=10,**kwargs):
    if kwargs['c']==0:
        return True
    else:
        return False
        
def branch_test_everything():
    c=testClass()
    c.t(0)
    branch_test(5,a=0)
    branch_test_matrix([3,2])
    branch_test_kwarg(3,**{"a":5})


# def deathlock_test_1(a):
#     if a==0:
#         deathlock_test_2(0)
#         return True
#     else:
#         return False
    
# def deathlock_test_2(a):
#     if a==0:
#         deathlock_test_1(0)
#         return 1
#     else:
#         return False
# 设置跟踪函数
sys.settrace(tc.trace_calls)

# 调用函数
# print(f"call function result:{branch_test(5,a=0)}")
# print(f"call function result:{branch_test_matrix([3,2])}")
# print(f"call function result:{branch_test_dict({'k':0})}")
# print(f"call function result:{branch_test_arg(3,2,5,6)}")
# print(f"call function result:{branch_test_kwarg(3,kw=0)}")
print(f"call function result:{branch_test_type(3,*(2,3),b=10,c=10,**{'d':5})}")
# print(f"call function result:{branch_test_nothing()}")
# branch_test_everything()


# 取消跟踪函数
sys.settrace(None)
