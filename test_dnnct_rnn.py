#!/usr/bin/env python3

import logging, os
import numpy as np
import itertools
import libct.explore
from libct.utils import get_module_from_rootdir_and_modpath, get_function_from_module_and_funcname


# PYCT_ROOT = 'PyCT-optimize'
PYCT_ROOT = './'
MODULE_ROOT = os.path.join(PYCT_ROOT, "dnn_predict_py")
MODEL_ROOT = os.path.join(MODULE_ROOT, 'model')
MODEL_NAME = "test_1_RNN"
MODEL_PATH = os.path.join(MODEL_ROOT, f"{MODEL_NAME}.h5")


input_dim = 2
input_time_step = 4
hidden_state_dim = 6

##########################################
def create_and_save_test_RNN_model():
    import tensorflow as tf
    from tensorflow.keras import layers
    from tensorflow.keras.layers import SimpleRNN, Dense
    from tensorflow.keras.models import Sequential
    from tensorflow.keras import initializers

    keras_model = Sequential()

    simple_rnn = SimpleRNN(units=hidden_state_dim, activation='tanh',
                        input_shape=(input_time_step, input_dim),
                        bias_initializer=initializers.glorot_normal())

    keras_model.add(simple_rnn)
    keras_model.add(Dense(6, activation='relu'))
    keras_model.add(Dense(2))

    keras_model.summary()
    keras_model.save(MODEL_PATH)


def get_test_input_dict():
    # Define input sequence and target output
    np.random.seed(1028)
    inputs = np.random.normal(10, 2, size=(input_time_step, input_dim))

    in_dict = dict()
    con_dict = dict()

    for i,j in itertools.product(
        range(input_time_step),
        range(input_dim),
    ):
        key = f"v_{i}_{j}"
        in_dict[key] = float(inputs[i][j])
        con_dict[key] = 0

    return in_dict, con_dict


create_and_save_test_RNN_model()
in_dict, con_dict = get_test_input_dict()
con_dict['v_0_0'] = 1
con_dict['v_3_0'] = 1

modpath = os.path.join(PYCT_ROOT, f"dnn_predict_common.py")
func = "predict"
funcname = t if (t:=func) else modpath.split('.')[-1]


dump_projstats = False
file_as_total = False
formula = None
include_exception = False
max_iter = 0
lib = None
logfile = None
root = os.path.dirname(__file__)
safety = 0
single_timeout = 900
timeout = 900
total_timeout = 900
verbose = 1 # 5:all, 3:>=DEBUG. 2:including SMT, 1: >=INFO
norm = True


statsdir = None
if dump_projstats:
    statsdir = os.path.join(
        os.path.abspath(os.path.dirname(__file__)), "project_statistics",
         os.path.abspath(root).split('/')[-1], modpath, funcname)


module = get_module_from_rootdir_and_modpath(root, modpath)
func_init_model = get_function_from_module_and_funcname(module, "init_model")
execute = get_function_from_module_and_funcname(module, funcname)
func_init_model(MODEL_PATH)

##############################################################################
# This section creates an explorer instance and starts our analysis procedure!

engine = libct.explore.ExplorationEngine(solver='cvc4', timeout=timeout, safety=safety,
                                           store=formula, verbose=verbose, logfile=logfile,
                                           statsdir=statsdir, module_=module, execute_=execute)

# con_dict = eval(args.concolic_dict) if args.concolic_dict else {}

result = engine.explore(
     modpath, in_dict, root=root, funcname=func, max_iterations=max_iter,
     single_timeout=single_timeout, total_timeout=total_timeout, deadcode=set(),
     include_exception=include_exception, lib=lib,
     file_as_total=file_as_total, concolic_dict=con_dict, norm=norm)

explore_stats = result[1]
print("\nTotal iterations:", result[0])
##############################################################################

################################################################
# This section prints the generated inputs and coverage results.
# print("\nGenerated inputs")
# print(engine.inputs)
# if len(engine.errors) > 0: print("\nError inputs"); print(engine.errors)
# engine.print_coverage() # Line coverage + Missing lines
# if result_list := list(zip(engine.inputs, engine.results)):
#     print("# of input vectors:", len(result_list)); print(result_list); print()
################################################################
