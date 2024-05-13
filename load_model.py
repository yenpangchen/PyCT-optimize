
import time
from multiprocessing import Process

def run_mnist_model(model_name="mnist_sep_act_m6_9628"):
    NORM_01 = True
    # model_name = "mnist_sep_act_m6_9653_noise"
    # model_name = "mnist_sep_act_m7_9876"
    # model_name = "mnist_sep_act_m6_9628"

    NUM_PROCESS = 30
    TIMEOUT = 1800
    from utils.pyct_attack_exp import run_multi_attack_subprocess_wall_timeout
    from utils.pyct_attack_exp_research_question import pyct_mnist_random
     
    #inputs = pyct_shap_1_4_8_16_32_48_64(model_name, first_n_img=10)
    inputs = pyct_mnist_random(model_name)

    print("#"*40, f"number of inputs: {len(inputs)}", "#"*40)
    time.sleep(3)

    p = Process(target=run_multi_attack_subprocess_wall_timeout, args=(inputs, TIMEOUT, NORM_01))
    p.start()
    p.join()
        

    print('done')


if __name__ == '__main__': 
    run_mnist_model("simple_mnist_bad_07685")


