import numpy as np
import random
from itertools import product


def mnist_test_data_10000():
    np.random.seed(1028)
    random.seed(1028)
    random_pixels = [] # shape: (10000, 784, 3)


    all_possible_pixels = []
    for i, j in product(range(28), range(28)):
        all_possible_pixels.append([i, j, 0]) # 0 is because MNIST only has one channel


    for idx in range(10000):
        random.shuffle(all_possible_pixels)
        random_pixels.append(all_possible_pixels.copy())
   
    random_pixels = np.array(random_pixels)
    return random_pixels
   


# array([[ 6, 25,  0],
#        [12, 11,  0],
#        [27, 18,  0],


# res = mnist_test_data_10000()
# print()



