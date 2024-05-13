import unittest
import os
import re
import sys
import inspect
import keras
import json
import logging
from myDNN import NNModel 
import arg_wrapper
from try_run_pyct import pyct_test_transformers
import traceCall as tc
import numpy as np
import linecache
import itertools

from utils.pyct_attack_exp_research_question import pyct_mnist_random
# from utils.pyct_attack_exp import get_save_dir_from_save_exp
PYCT_ROOT = '/home/soslab/PyCT-optimize'
MODEL_ROOT = os.path.join(PYCT_ROOT, 'model')
function_list=[]


def init_model(model_path):
        model = keras.models.load_model(model_path)
        layers = [l for l in model.layers if type(l).__name__ not in ['Dropout']]
        myModel = NNModel()

        # 1: is because 1st dim of input shape of Keras model is batch size (None)
        myModel.input_shape = model.input_shape[1:]
        for layer in layers:
            myModel.addLayer(layer)
        return myModel
        # print("model:",myModel)
def predict(model,**data):
        print(data)
        input_shape = model.input_shape
        # print("model:",myModel)
        iter_args = (range(dim) for dim in input_shape)
        X = np.zeros(input_shape).tolist()
        data_name_prefix = "v_"
        for i in itertools.product(*iter_args):
            if len(i) == 2:
                X[i[0]][i[1]] = data[f"{data_name_prefix}{i[0]}_{i[1]}"]
            elif len(i) == 3:
                X[i[0]][i[1]][i[2]] = data[f"{data_name_prefix}{i[0]}_{i[1]}_{i[2]}"]
            elif len(i) == 4:
                X[i[0]][i[1]][i[2]][i[3]] = data[f"{data_name_prefix}{i[0]}_{i[1]}_{i[2]}_{i[3]}"]

        out_val = model.forward(X)

        # 用一顆神經元做二分類
        if len(out_val) == 1:
            if out_val[0] > 0.5:
                ret_class = 1
            else:
                ret_class = 0
        else:
            max_val, ret_class = out_val[0], 0
            for i,cl_val in enumerate(out_val):
                if cl_val > max_val:
                    max_val, ret_class = cl_val, i

        logging.info(f"[DEBUG]predicted class:{ret_class}")
        return ret_class

# class load_model_testcase(unittest.TestCase):

#     def test_model_PyCT(self):

#         inputs=[]
#         modelN=[]
#         os.environ['run_pyct_in_unittest'] = 'True'
#         f=open("/home/soslab/PyCT-optimize/model/used_model.txt","r")
        
#         for model_name in f.read().splitlines():
#             # print(f"add {model_name}")
#             inputs.append(pyct_mnist_random(model_name))
#             modelN.append(model_name)
#             # print(inputs)
#         # print(self.modelN)

#         for i,model_name in enumerate(modelN):
            
#             input=inputs[i]
#             model_path = os.path.join(MODEL_ROOT, f"{model_name}.h5")
#             modpath = os.path.join(PYCT_ROOT, f"dnn_predict_common.py")
#             func = "predict"
#             funcname = t if (t:=func) else modpath.split('.')[-1]
#             save_dir = None
#             smtdir = None


#             dump_projstats = False
#             file_as_total = False
#             formula = None
#             include_exception = False
#             lib = None
#             logfile = None
#             # root = os.path.dirname(__file__)
#             root="/home/soslab/PyCT-optimize"
#             safety = 0
#             # verbose = 1 # 5:all, 3:>=DEBUG. 2:including SMT, 1: >=INFO
#             # norm = True


#             statsdir = None
#             if dump_projstats:
#                 statsdir = os.path.join(
#                     os.path.abspath(os.path.dirname(__file__)), "project_statistics",
#                     os.path.abspath(root).split('/')[-1], modpath, funcname)

#             # from libct.utils import get_module_from_rootdir_and_modpath, get_function_from_module_and_funcname
#             # module = get_module_from_rootdir_and_modpath(root, modpath)
#             # func_init_model = get_function_from_module_and_funcname(module, "init_model")
#             # execute = get_function_from_module_and_funcname(module, funcname)
#             # func_init_model(model_path) #dnn_predict_common_line9
#             # execute(**input[0]['in_dict'])
#             #----- build model finish!!-----
#             # print(input[0]['in_dict'])

#             i=predict(init_model(model_path),input[0]['in_dict'])
            
#             print(i)

def test_model_PyCT():
    inputs=[]
    modelN=[]
    os.environ['run_pyct_in_unittest'] = 'True'
    f=open("/home/soslab/PyCT-optimize/model/used_model.txt","r")
    
    for model_name in f.read().splitlines():
        inputs.append(pyct_mnist_random(model_name))
        modelN.append(model_name)

    for i,model_name in enumerate(modelN):
        
        input=inputs[i]
        model_path = os.path.join(MODEL_ROOT, f"{model_name}.h5")
        modpath = os.path.join(PYCT_ROOT, f"dnn_predict_common.py")
        func = "predict"
        funcname = t if (t:=func) else modpath.split('.')[-1]
        save_dir = None
        smtdir = None


        dump_projstats = False
        file_as_total = False
        formula = None
        include_exception = False
        lib = None
        logfile = None
        # root = os.path.dirname(__file__)
        root="/home/soslab/PyCT-optimize"
        safety = 0
        # verbose = 1 # 5:all, 3:>=DEBUG. 2:including SMT, 1: >=INFO
        # norm = True


        statsdir = None
        if dump_projstats:
            statsdir = os.path.join(
                os.path.abspath(os.path.dirname(__file__)), "project_statistics",
                os.path.abspath(root).split('/')[-1], modpath, funcname)

        # from libct.utils import get_module_from_rootdir_and_modpath, get_function_from_module_and_funcname
        # module = get_module_from_rootdir_and_modpath(root, modpath)
        # func_init_model = get_function_from_module_and_funcname(module, "init_model")
        # execute = get_function_from_module_and_funcname(module, funcname)
        # func_init_model(model_path) #dnn_predict_common_line9
        # execute(**input[0]['in_dict'])
        #----- build model finish!!-----
        # print(input[0]['in_dict'])
        
        # model=myModel

        model=init_model(model_path)
        sys.settrace(tc.trace_calls)
        
        i=predict(model,**input[0]['in_dict'])
        sys.settrace(None)

        # print(function_list)
        # with open('/home/soslab/PyCT-optimize/function_list.txt', 'w') as f:
        #     # 对于列表中的每个值，将其写入文件并添加换行符
        #     for item in function_list:
        #         print("!!")
        #         f.write(f"{item}\n")  # 写入列表中的项，换行

        print(i)

if __name__ == '__main__': 
    
    # b=load_model_testcase()
    # b.test_model_PyCT()
    # FORMAT = '%(asctime)s %(filename)s %(funcName)s %(levelname)s: %(message)s'
    logging.basicConfig(level=logging.INFO)
    test_model_PyCT()
    






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
