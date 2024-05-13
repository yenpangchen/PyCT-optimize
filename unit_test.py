# 一定要在最一開始import此模組，後續取得自動import的模組清單才不會錯
import sys
sys.path.insert(0, '/home/.local/lib')
# sys.path.insert(1, '/home/ray/PyCT-optimize')
# sys.path.insert(3, '/home/ray/pyct-coverage/coverage/transformers')
# import arg_wrapper.arg_wrapper as arg_wrapper 有問題不要import

import unittest
import sys
import logging
import time
# import tensorflow as tf
import os
import coverage
FORMAT = '%(asctime)s %(filename)s %(funcName)s %(levelname)s: %(message)s'
# 轉換為 struct_time 格式的本地時間



def unit_test(pattern):
    #pattern = "test_feature_extraction_clap.py" # tests/utils/test_audio_utils.py
    # fileName=f'/home/ray/pyct-coverage/coverage/transformers/log/unit_test_transformer_{pattern}.log'
    time_result = time.localtime(time.time())
    fileName=f'/home/soslab/PyCT-optimize/log/unit_test_{time_result.tm_mon}_{time_result.tm_mday}_{time_result.tm_hour}_{time_result.tm_min}.log'
    
    # # print(f'fileNameout={fileName}')
    # logger=logging.getLogger('ct')
    # handler=logging.FileHandler(fileName,mode='w')
    # formatter=logging.Formatter(FORMAT)
    # handler.setFormatter(formatter)
    logging.basicConfig(level=logging.DEBUG, filename=fileName, filemode='a', format=FORMAT)
    # logger.addHandler(handler)
    # logger.setLevel('INFO')
    #pattern = ""
    logging.info(f"=============================={pattern}[START PROCESSING]==============================")
    print(f"=============================={pattern}[START PROCESSING]==============================")

    os.environ['run_pyct_in_unittest'] = 'False'
    cov = coverage.Coverage()
    cov.start() # Start measuring coverage
    loader = unittest.TestLoader()
    suite = loader.discover(start_dir='.', pattern=pattern)
    runner = unittest.TextTestRunner(verbosity=1)

    
    runner.run(suite)
        
    cov.stop() # Stop measuring coverage
    cov.save() # Save the coverage data to disk
    cov.report(show_missing=True,file=open(f'coverage_report_manual/{pattern}_unittest.txt', 'w'))

    


    logging.info("==============================[START PYCT in UNITTEST]==============================")
    print("="*30, "[START PYCT in UNITTEST]", "="*30)
    os.environ['run_pyct_in_unittest'] = 'True'
      

    # cov = coverage.Coverage(concurrency='multiprocessing')
    cov = coverage.Coverage()
    cov.load()
    cov.start() # Start measuring coverage 
    loader = unittest.TestLoader()
    suite = loader.discover(start_dir='.', pattern=pattern)
    runner = unittest.TextTestRunner(verbosity=1)

    
    runner.run(suite)
    
    cov.stop()
    cov.report(show_missing=True,file=open(f'coverage_report_manual/{pattern}_unittest+pyct.txt', 'w'))

    



    return fileName



if __name__ == '__main__': 
    # unit_test_transformer('test_load_model.py')
    # unit_test('load_model_testcase.py')
    unit_test('branch_testcase.py')
    # unit_test('test_ct.py')
