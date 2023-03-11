import os
import json
import numpy as np


def get_save_dir_from_save_exp(save_exp, model_name, s_or_q):
    save_dir = os.path.join("exp", model_name, s_or_q, save_exp['exp_name'], save_exp['input_name'])
    return save_dir


def run_multi_attack(args, timeout):
    import run_dnnct
    
    for one_input in args:        
        print(one_input['save_exp'])
        
        result = run_dnnct.run(
            **one_input, norm=True,
            max_iter=0, total_timeout=timeout, single_timeout=timeout, timeout=timeout
        )
        
        recorder = result[0]
                        


##### Generate Inputs #####
# exp test
def pyct_shap_1_test(model_name, first_n_img=500):
    from utils.dataset import MnistDataset
    mnist_dataset = MnistDataset()
        
    ### SHAP and hard image index
    test_shap_pixel_sorted = np.load('./shap_value/mnist_sep_act_m6_9628/mnist_sort_shap_pixel.npy')
    is_hard_img = np.load('./exp_result/is_hard_img.npy')
    

    inputs = []

    for solve_order_stack in [False]:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"

        for ton_n_shap in [1]:
            
            for idx, is_hard in zip(range(first_n_img), is_hard_img):
                if not is_hard:
                    # 該張圖不是困難的就跳過
                    continue

                save_exp = {
                    "input_name": f"mnist_test_{idx}",
                    "exp_name": f"shap_{ton_n_shap}"
                }

                save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q)
                if os.path.exists(save_dir):
                    # 已經有紀錄的圖跳過
                    continue
                
                
                attack_pixels = test_shap_pixel_sorted[idx, :ton_n_shap].tolist()
                in_dict, con_dict = mnist_dataset.get_mnist_test_data_and_set_condict(idx, attack_pixels)
                
                
                one_input = {
                    'model_name': model_name,
                    'in_dict': in_dict,
                    'con_dict': con_dict,
                    'solve_order_stack': solve_order_stack,
                    'save_exp': save_exp,
                }

                inputs.append(one_input)
                
    return inputs

# exp 1
def pyct_shap_3_5_10_hard(model_name, first_n_img):
    from utils.dataset import MnistDataset
    mnist_dataset = MnistDataset()
        
    ### SHAP and hard image index
    test_shap_pixel_sorted = np.load('./shap_value/mnist_sep_act_m6_9628/mnist_sort_shap_pixel.npy')
    is_hard_img = np.load('./exp_result/is_hard_img.npy')
    

    inputs = []

    for solve_order_stack in [False, True]:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"

        for ton_n_shap in [3, 5, 10]:
            
            for idx, is_hard in zip(range(first_n_img), is_hard_img):
                if not is_hard:
                    # 該張圖不是困難的就跳過
                    continue

                save_exp = {
                    "input_name": f"mnist_test_{idx}",
                    "exp_name": f"shap_{ton_n_shap}"
                }

                save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q)
                if os.path.exists(save_dir):
                    # 已經有紀錄的圖跳過
                    continue
                
                
                attack_pixels = test_shap_pixel_sorted[idx, :ton_n_shap].tolist()
                in_dict, con_dict = mnist_dataset.get_mnist_test_data_and_set_condict(idx, attack_pixels)
                
                
                one_input = {
                    'model_name': model_name,
                    'in_dict': in_dict,
                    'con_dict': con_dict,
                    'solve_order_stack': solve_order_stack,
                    'save_exp': save_exp,
                }

                inputs.append(one_input)
                
    return inputs

