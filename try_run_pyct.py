# 一定要在最一開始import此模組，後續取得自動import的模組清單才不會錯
import sys
# sys.path.insert(0, '/home/.local/lib')
# sys.path.insert(1, '/home/soslab/PyCT-optimize')
# sys.path.pop(0)

import os, multiprocessing


from run_pyct_debug_multi import run_explore_one_func_no_coverage


# rootdir = os.path.abspath(args.project)
# lib = rootdir + '/.venv/lib/python3.8/site-packages'
# sys.path.insert(0, lib); sys.path.insert(0, rootdir)
# project_name = rootdir.split('/')[-1]


def pyct_test_transformers(file, funcname, in_dict,logfile=None):
    """
    params example:
        file = "/home/jack/coverage/transformers/tests/models/albert/test_modeling_albert.py"
        funcname = "AlbertModelTest.test_config"
    """
    
    # 5:all, 3:>=DEBUG. 2:including SMT, 1: >=INFO
    verbose = 5
    lib = None
    # rootdir = "/home/soslab/PyCT-optimize" 0506暫時刪除
    
    rootdir = file.replace(os.path.basename(file),"")
    TOTAL_TIMEOUT = 3600
    
    # with multiprocessing.Pool(1) as pool:
    #     res = pool.apply(run_pyct_one_func_no_coverage, (rootdir, file, funcname, lib, TOTAL_TIMEOUT, verbose, in_dict))
    #     res.wait()
    
    p = multiprocessing.Process(target=run_explore_one_func_no_coverage,
                                args=(rootdir, file, funcname, lib, TOTAL_TIMEOUT, verbose, in_dict,logfile))
    # file&rootdir must be ~~~/OOO.py and ~~~
    # p = multiprocessing.Process(target=run_pyct_one_func,
    #                             args=(rootdir, file, funcname, lib, TOTAL_TIMEOUT, verbose, in_dict))
    
    p.start()
    p.join()



if __name__ == '__main__':
    sys.path.insert(0, '/home/soslab/pyct-coverage/coverage/transformers/src')
    
    rootdir = os.path.abspath(".")
    # file = "/home/jack/coverage/transformers/tests/models/reformer/test_tokenization_reformer.py"
    # funcname = "ReformerTokenizationTest.test_convert_token_and_id"
    
    file = "/home/soslab/PyCT-optimize/configuration_utils.py"
    funcname = "PretrainedConfig.update_from_string"
    
    lib = None
    TOTAL_TIMEOUT = 60
    verbose = 3
    in_dict = {}

    
    pyct_test_transformers(file, funcname, in_dict)
    
    # p = multiprocessing.Process(target=test_run_pyct_one_func,
    #                             args=(rootdir, file, funcname, lib, TOTAL_TIMEOUT, verbose, in_dict))
    # p.start()
    # p.join()
    
    
    # run_pyct(rootdir=os.path.abspath("."), files, lib, TOTAL_TIMEOUT, verbose)

    # main(rootdir=os.path.abspath("."), pattern="./src/transformers",
    #      lib=None, TOTAL_TIMEOUT=15, verbose=3, num_processes=1)




