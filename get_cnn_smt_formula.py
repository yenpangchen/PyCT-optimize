import time
from multiprocessing import Process

model_name = "mnist_sep_act_m6_9628"
# model_name = "mnist_sep_act_m6_9653_noise"

NUM_PROCESS = 1
TIMEOUT = 600

if __name__ == "__main__":
    from utils.pyct_attack_exp import pyct_shap_1_4_8_16_32, run_multi_attack
     
    inputs = pyct_shap_1_4_8_16_32(model_name, first_n_img=1)
    
    # use thie to save smt constraints in exp dir
    for input in inputs:
        input['save_exp']['save_smt'] = True
    

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
        if len(sub_tasks) > 0:
            p = Process(target=run_multi_attack, args=(sub_tasks, TIMEOUT, ))
            p.start()
            running_processes.append(p)
            time.sleep(1) # subprocess start 的間隔時間
       
    for p in running_processes:
        p.join()


    print('done')

