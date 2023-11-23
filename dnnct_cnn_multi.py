# import time
# from multiprocessing import Process

# model_name = "mnist_sep_act_m6_9628"
# # model_name = "mnist_sep_act_m6_9653_noise"

# NUM_PROCESS = 25
# TIMEOUT = 1800

# if __name__ == "__main__":
#     from utils.pyct_attack_exp import run_multi_attack_subprocess_wall_timeout
#     from utils.pyct_attack_exp_research_question import (        
#         pyct_shap_1_4_8_16_32_only_first_forward,
#         pyct_shap_1_4_8_16_32_48_64, pyct_random_1_4_8_16_32_48_64,
#     )
     
#     inputs = pyct_shap_1_4_8_16_32_48_64(model_name, first_n_img=100)
#     # inputs = pyct_random_1_4_8_16_32_48_64(model_name, first_n_img=100)

#     print("#"*40, f"number of inputs: {len(inputs)}", "#"*40)
#     time.sleep(3)

#     ########## 分派input給各個subprocesses ##########    
#     all_subprocess_tasks = [[] for _ in range(NUM_PROCESS)]
#     cursor = 0
#     for task in inputs:    
#         all_subprocess_tasks[cursor].append(task)    
       
#         cursor+=1
#         if cursor == NUM_PROCESS:
#             cursor = 0


#     running_processes = []
#     for sub_tasks in all_subprocess_tasks:
#         if len(sub_tasks) > 0:
#             p = Process(target=run_multi_attack_subprocess_wall_timeout, args=(sub_tasks, TIMEOUT, ))
#             p.start()
#             running_processes.append(p)
#             time.sleep(1) # subprocess start 的間隔時間
       
#     for p in running_processes:
#         p.join()

#     print('done')


import time
from multiprocessing import Process


NORM_01 = True
# model_name = "mnist_sep_act_m6_9653_noise"
# model_name = "mnist_sep_act_m7_9876"
model_name = "mnist_sep_act_m6_9628"

NUM_PROCESS = 30
TIMEOUT = 1800

if __name__ == "__main__":
    from utils.pyct_attack_exp import run_multi_attack_subprocess_wall_timeout
    from utils.pyct_attack_exp_research_question import (        
        pyct_shap_1_4_8_16_32_only_first_forward,
        pyct_shap_1_4_8_16_32, pyct_random_1_4_8_16_32,
    )
     
    inputs = pyct_shap_1_4_8_16_32(model_name, first_n_img=100)
    # inputs = pyct_random_1_4_8_16_32(model_name, first_n_img=100)

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
            p = Process(target=run_multi_attack_subprocess_wall_timeout, args=(sub_tasks, TIMEOUT, NORM_01))
            p.start()
            running_processes.append(p)
            time.sleep(1) # subprocess start 的間隔時間
       
    for p in running_processes:
        p.join()

    print('done')

