import itertools
import numpy as np

class MnistDataset:
    def __init__(self):
        from tensorflow.keras.datasets.mnist import load_data        
        
        # Load the data and split it between train and test sets
        (x_train, y_train), (x_test, y_test) = load_data()
        
        # Scale images to the [0, 1] range
        x_train = x_train.astype("float32") / 255
        x_test = x_test.astype("float32") / 255

        # Make sure images have shape (28, 28, 1)
        
        del x_train
        del y_train
        
        # self.x_train = np.expand_dims(x_train, -1)
        self.x_test = np.expand_dims(x_test, -1)

    def get_mnist_test_data(self, idx):        
        in_dict = dict()
        con_dict = dict()

        test_img = self.x_test[idx]

        for i,j,k in itertools.product(
            range(test_img.shape[0]),
            range(test_img.shape[1]),
            range(test_img.shape[2])
        ):
            key = f"v_{i}_{j}_{k}"
            in_dict[key] = float(test_img[i][j][k])
            con_dict[key] = 0
        
        return in_dict, con_dict
    
    
    def get_mnist_test_data_and_set_condict(self, idx, attack_pixels):
        in_dict, con_dict = self.get_mnist_test_data(idx)
        
        for i,j,k in attack_pixels:
            key = f"v_{i}_{j}_{k}"
            con_dict[key] = 1
        
        return in_dict, con_dict
        
    
