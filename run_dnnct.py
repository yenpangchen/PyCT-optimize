#!/usr/bin/env python3

import os
import libct.explore as explore
import json
from libct.utils import get_module_from_rootdir_and_modpath, get_function_from_module_and_funcname
from utils.pyct_attack_exp import get_save_dir_from_save_exp
import unittest
import coverage

PYCT_ROOT = './'
MODEL_ROOT = os.path.join(PYCT_ROOT, 'model')


def run(model_name, in_dict,  norm, solve_order_stack, con_dict={}, save_exp=True,
        max_iter=0, single_timeout=900, timeout=900, total_timeout=900, verbose=1,
        limit_change_range=None, only_first_forward=False):

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
    root = os.path.dirname(__file__)
    safety = 0

    # verbose = 1 # 5:all, 3:>=DEBUG. 2:including SMT, 1: >=INFO
    # norm = True


    statsdir = None
    if dump_projstats:
        statsdir = os.path.join(
            os.path.abspath(os.path.dirname(__file__)), "project_statistics",
            os.path.abspath(root).split('/')[-1], modpath, funcname)
    print(f"in_dict:{in_dict}")
    print(f"rootdir: {root}")
    print(f"relative_modpath: {modpath}")
    module = get_module_from_rootdir_and_modpath(root, modpath)
    func_init_model = get_function_from_module_and_funcname(module, "init_model")
    execute = get_function_from_module_and_funcname(module, funcname)
    func_init_model(model_path) #dnn_predict_common_line9
    #----- build model finish!!-----
    print("----- build model finish!!-----")
    # print("execute test")
    # print(f"run_dnct in_dict: {in_dict}")
    execute(**in_dict)
    # test_case=load_model_testcase(func_init_model,in_dict)
    # cov = coverage.Coverage()
    # cov.load()
    # cov.start() # Start measuring coverage  
    # suite = (unittest.TestLoader().loadTestsFromTestCase(test_case))
    # runner = unittest.TextTestRunner(verbosity=1)

    
    # runner.run(suite)
    
    # cov.stop()
    # cov.report(skip_empty=True,show_missing=True,file=open(f'coverage_report_manual/{funcname}_unittest+pyct.txt', 'w'))

    

    # print("module:",module)
    # print("func_init_model:",func_init_model)
    # print("execute:",execute)
    # print("func_init_model(model_path):",func_init_model(model_path))

    ##############################################################################
    # This section creates an explorer instance and starts our analysis procedure!    
    if save_exp is not None:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"                    
        save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q, only_first_forward=only_first_forward)
        print("==========savedir:",save_dir)
        if save_exp.get('save_smt', False):        
            smtdir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q, only_first_forward=only_first_forward) 

           
    
    engine = explore.ExplorationEngine(solver='cvc4', timeout=timeout, safety=safety,
                                            store=formula, verbose=verbose, logfile=logfile,
                                            statsdir=statsdir, smtdir=smtdir,
                                            save_dir=save_dir, input_name=save_exp['input_name'],
                                            module_=module, execute_=execute,
                                            only_first_forward=only_first_forward)


    result = engine.explore(
        modpath, in_dict, concolic_dict=con_dict, root=root, funcname=func, max_iterations=max_iter,
        single_timeout=single_timeout, total_timeout=total_timeout, deadcode=set(),
        include_exception=include_exception, lib=lib,
        file_as_total=file_as_total, norm=norm, solve_order_stack=solve_order_stack,
        limit_change_range=limit_change_range, 
    )
        
            
    return result


# class load_model_testcase(unittest.TestCase):
#     def __init__(self,processed_model,inputs) -> None:
#         from load_model_testcase import init_testcase
#         self.processed_model=processed_model
#         #inputs = pyct_shap_1_4_8_16_32_48_64(model_name, first_n_img=10)
#         self.inputs = inputs
        
        
        
#     def test_model_PyCT(self):
#         self.processed_model.predict(self.inputs)

