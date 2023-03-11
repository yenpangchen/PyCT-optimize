import time
from multiprocessing import Process

model_name = "mnist_sep_act_m6_9628"

NUM_PROCESS = 4
TIMEOUT = 1800

if __name__ == "__main__":
    from utils.pyct_attack_exp import pyct_shap_3_5_10_hard, run_multi_attack
    
    # from utils.pyct_attack_exp import pyct_shap_1_test
    # inputs = pyct_shap_1_test(model_name)
    
    
    inputs = pyct_shap_3_5_10_hard(model_name, first_n_img=400)
    
    print("#"*40, f"number of inputs: {len(inputs)}", "#"*40)
    time.sleep(3)

    ########## 分派input給各個subprocesses ##########    
    all_subprocess_tasks = [[] for _ in range(NUM_PROCESS)]
    cursor = 0
    for task in inputs:    
        all_subprocess_tasks[cursor].append(task)    
       
        cursor+=1
        if cursor == NUM_PROCESS:
            cursor = 0


    running_processes = []
    for sub_tasks in all_subprocess_tasks:
        p = Process(target=run_multi_attack, args=(sub_tasks, TIMEOUT, ))
        p.start()
        running_processes.append(p)
        time.sleep(2) # subprocess start 的間隔時間
       
    for p in running_processes:
        p.join()


    print('done')

