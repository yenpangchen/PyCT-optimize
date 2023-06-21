import os
import numpy as np
from utils.pyct_attack_exp import get_save_dir_from_save_exp

##### Generate Inputs #####

def pyct_shap_1_4_8_16_32_48_64(model_name, first_n_img):
    from utils.dataset import MnistDataset
    mnist_dataset = MnistDataset()
        
    ### SHAP
    test_shap_pixel_sorted = np.load(f'./shap_value/{model_name}/mnist_sort_shap_pixel.npy')
    
    inputs = []

    for solve_order_stack in [False, True]:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"

        for ton_n_shap in [1,4,8,16,32,48,64]:
            
            for idx in range(first_n_img):
                save_exp = {
                    "input_name": f"mnist_test_{idx}",
                    "exp_name": f"shap_{ton_n_shap}"
                }

                save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q, only_first_forward=False)
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


def pyct_random_1_4_8_16_32_48_64(model_name, first_n_img):
    from utils.dataset import MnistDataset
    from utils.gen_random_pixel_location import mnist_test_data_10000
    
    mnist_dataset = MnistDataset()        
    random_pixels = mnist_test_data_10000()
    
    inputs = []

    for solve_order_stack in [False, True]:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"

        for ton_n in [1,4,8,16,32,48,64]:
            
            for idx in range(first_n_img):
                save_exp = {
                    "input_name": f"mnist_test_{idx}",
                    "exp_name": f"random_{ton_n}"
                }

                save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q, only_first_forward=False)
                if os.path.exists(save_dir):
                    # 已經有紀錄的圖跳過
                    continue
                                
                attack_pixels = random_pixels[idx, :ton_n].tolist()
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



# exp 4 only use queue for SHAP 1,4,8,16,32 + only_first_forward
def pyct_shap_1_4_8_16_32_only_first_forward(model_name, first_n_img):
    from utils.dataset import MnistDataset
    mnist_dataset = MnistDataset()
        
    ### SHAP
    test_shap_pixel_sorted = np.load(f'./shap_value/{model_name}/mnist_sort_shap_pixel.npy')
    
    inputs = []

    for solve_order_stack in [False]:
        if solve_order_stack:
            s_or_q = "stack"
        else:
            s_or_q = "queue"

        for ton_n_shap in [1,4,8,16,32]:
            
            for idx in range(first_n_img):
                save_exp = {
                    "input_name": f"mnist_test_{idx}",
                    "exp_name": f"shap_{ton_n_shap}"
                }

                save_dir = get_save_dir_from_save_exp(save_exp, model_name, s_or_q, only_first_forward=True)
                if os.path.exists(os.path.join(save_dir, 'stats.json')):
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
                    'only_first_forward': True,
                }

                inputs.append(one_input)
                
    return inputs
