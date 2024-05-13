import unittest
import os

import keras
from myDNN import NNModel 
import numpy as np
import itertools

from utils.pyct_attack_exp_research_question import pyct_mnist_random
# from utils.pyct_attack_exp import get_save_dir_from_save_exp
PYCT_ROOT = '/home/soslab/PyCT-optimize'
MODEL_ROOT = os.path.join(PYCT_ROOT, 'model')

def branch_test(a):
        if a==0:
            return True
        else:
            return False
        
def branch_test_matrix(a):
        if a[0]==0:
            return True
        else:
            return False
        
def branch_test_kwarg(c,**a):
        if a['a']==0:
            return True
        else:
            return False


     


class branch_testcase(unittest.TestCase):
    
    # def test_PyCT(self):
    #     branch_test(0)
    
    # def test_PyCT_matrix(self):
        # branch_test_matrix([0,0,1])

    def test_PyCT_kwarg(self):
        inp={'a':3,'b':4}
        branch_test_kwarg(c=3,**inp)

# if __name__ == '__main__': 
#     os.environ['run_pyct_in_unittest'] = 'True'
#     cov = coverage.Coverage()
#     cov.start() # Start measuring coverage
#     loader = unittest.TestLoader()
#     # suite = loader.discover(start_dir='.', pattern=pattern)
#     suite = loader.discover(start_dir='.', pattern='load_model_testcase.py')
#     runner = unittest.TextTestRunner(verbosity=1)


#     runner.run(suite)
    
#     cov.stop() # Stop measuring coverage
#     cov.save() # Save the coverage data to disk
#     cov.report(skip_empty=True,show_missing=True,file=open(f'coverage_report_manual/unittest.txt', 'w'))
