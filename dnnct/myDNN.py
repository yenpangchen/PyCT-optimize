

import numpy as np
import math
from itertools import product
import collections
from functools import reduce  
import operator



import keras
from keras.layers import (
    Dense,
    Conv1D, Conv2D,
    LocallyConnected1D, LocallyConnected2D,
    Flatten,
    ELU,
    Activation,
    MaxPool2D,
    LSTM,
    Embedding,
    BatchNormalization,
)

LAYERS = (
    Dense,
    Conv1D, Conv2D,
    LocallyConnected1D, LocallyConnected2D,
    Flatten,
    ELU,
    Activation,
    MaxPool2D,
    LSTM,
    Embedding,
    BatchNormalization,
)

ACTIVATIONS = (
    'linear',
    'relu',
    'elu',
    'softplus',
    'softsign',
    'sigmoid',
    'tanh',
    'hard_sigmoid',
    'softmax',
)

# https://stackoverflow.com/questions/17531796/find-the-dimensions-of-a-multidimensional-python-array
# return the dimension of a python list
def dim(a):
    if not type(a) == list:
        return []
    return [len(a)] + dim(a[0])

# acivation function
def actFunc(val, type):
    if type=='linear':
        pass
    elif type=='relu':
        if val < 0.0:
            return 0.0
        else:
            return val
    elif type=='softmax':
        pass
    elif type=='sigmoid':
        pass
    elif type=='tanh':
        pass
    elif type=='elu':
        pass
    elif type=='softplus':
        pass
    elif type=='softsign':
        pass
    else:
        raise NotImplementedError()
    return 0


class ActivationLayer:
    def __init__(self, type):
        if type not in ACTIVATIONS: raise NotImplementedError()
        self.type = type
        self._output = None
    def forward(self, tensor_in):
        out_shape = dim(tensor_in)
        tensor_out = tensor_in
        if len(out_shape)==1:
            if self.type=="softmax":
                denom = 0
                for idx in range(0, out_shape[0]):
                    denom = denom + math.exp(tensor_in[idx])
                for idx in range(0, out_shape[0]):
                    tensor_out[idx] = math.exp(tensor_in[idx]) / denom
            else:
                for idx in range(0, out_shape[0]):
                    tensor_out[idx] = actFunc(tensor_in[idx], self.type)
        elif len(out_shape)==2:
            for i, j in product( range(0, out_shape[0]),
                                 range(0, out_shape[1])):
                tensor_out[i][j] = actFunc(tensor_in[i][j], self.type)
        elif len(out_shape)==3:
            for i, j, k in product( range(0, out_shape[0]),
                                    range(0, out_shape[1]),
                                    range(0, out_shape[2])):
                tensor_out[i][j][k] = actFunc(tensor_in[i][j][k], self.type)
        else:
            raise NotImplementedError()
        print("[DEBUG]Finish Activation Layer forwarding!!")
        #print("Output #Activations=%i" % len(tensor_out))
        ## DEBUG
        self._output = tensor_out
        return tensor_out
    def getOutput(self):
        return self._output

class DenseLayer:
    def __init__(self, weights, bias, shape, activation="None"):
        self.weights = weights.astype(float)
        self.bias = bias
        self.shape = shape
        self.activation = activation
        self._output = None
    def addActivation(self, activation):
        self.activation = activation

    def forward(self, tensor_in):
        in_shape = dim(tensor_in)
        assert len(in_shape)==1, "DenseLayer.forward() with non flattened input!"
        assert in_shape[0]==self.shape[1], "DenseLayer.forward(), dim. mismatching between input and weights!"
        tensor_out = self.bias.tolist()

        for out_id in range(0, self.shape[0]):
            ## Dot operation
            for in_id in range(0, self.shape[1]):
                tensor_out[out_id] = tensor_in[in_id]*float(self.weights[out_id][in_id]) + tensor_out[out_id]
            if self.activation!="None":
                tensor_out[out_id] = actFunc(tensor_out[id], self.activation) 

        print("[DEBUG]Finish Dense Layer forwarding!!")
        #print("Output #Activations=%i" % len(tensor_out))
        self._output = tensor_out
        return tensor_out
    def getOutput(self):
        return self._output

class Conv2DLayer:
    def __init__(self, weights, bias, shape, activation="None", stride=1, padding='valid'):
        self.weights = weights.astype(float)
        self.shape = shape
        self.bias = bias
        self.padding = padding
        self.stride = stride
        self.activation = activation
        self._output = None
    def addActivation(self, activation):
        self.activation = activation
    def forward(self, tensor_in):
        in_shape = dim(tensor_in)
        assert in_shape[2] == self.shape[3], "Conv2DLayer, channel length mismatching!"
        ## For now, we assume stride=1 and padding='valid'
        ## TODO  stride!=1 and padding!='valid'
        out_shape = [in_shape[0]-self.shape[1]+1,
                     in_shape[1]-self.shape[2]+1,
                     self.shape[0]]
        #tensor_out = np.zeros( out_shape ).tolist()
        tensor_out = []
        for _ in range(out_shape[0]):
            tensor_out.append( [[0.0]*out_shape[2] for i in range(out_shape[1])] ) 

        for channel in range(0, out_shape[2]):
            filter_weights = self.weights[channel]
            num_row, num_col, num_depth = self.shape[1], self.shape[2], self.shape[3]
            for row in range(0, out_shape[0]):
                for col in range(0, out_shape[1]):
                    tensor_out[row][col][channel] = float(self.bias[channel])
                    ## inner product of the filter and the input image segments
                    for i, j, k in product( range(row, row+num_row),
                                            range(col, col+num_col), 
                                            range(0, num_depth)):
                        tensor_out[row][col][channel] = tensor_in[i][j][k] * float(filter_weights[i-row][j-col][k]) + tensor_out[row][col][channel] 
                    if self.activation!="None":
                        tensor_out[row][col][channel] = actFunc(tensor_out[row][col][channel], self.activation)
                    #print(type(tensor_out[row][col][channel]))
            #print("Finished %i feature Map" % channel)
        print("[DEBUG]Finish Conv2D Layer forwarding!!")
        #print("Feature Map Shape: %ix%ix%i" % tuple(out_shape))
        self._output = tensor_out
        return tensor_out

    def getOutput(self):
        return self._output


class MaxPool2DLayer:
    def __init__(self, shape, stride=1, padding='valid'):
        self.pool_size = shape
        self.stride = stride
        self.padding = padding
        self._output = None
    def forward(self, tensor_in):
        in_shape = dim(tensor_in)
        assert(len(in_shape)==3)

        ## For now, we assume stride=1 and padding='valid'
        ## TODO  stride!=1 and padding!='valid'
        r, c = self.pool_size[0], self.pool_size[1]
        out_shape = [ in_shape[0] // r,
                      in_shape[1] // c,
                      in_shape[2]]
        # tensor_out = np.zeros(out_shape).tolist()
        tensor_out = []
        for _ in range(out_shape[0]):
            tensor_out.append( [[0.0]*out_shape[2] for i in range(out_shape[1])] )

        for row in range(0, out_shape[0]):
            for col in range(0, out_shape[1]):
                for depth in range(0, out_shape[2]):
                    max_val = -10000
                    if tensor_in[row*r  ][col*c  ][depth] > max_val:
                        max_val = tensor_in[row*r  ][col*c  ][depth]
                    if tensor_in[row*r+1][col*c  ][depth] > max_val:
                        max_val = tensor_in[row*r+1][col*c  ][depth]
                    if tensor_in[row*r  ][col*c+1][depth] > max_val:
                        max_val = tensor_in[row*r  ][col*c+1][depth]
                    if tensor_in[row*r+1][col*c+1][depth]:
                        max_val = tensor_in[row*r+1][col*c+1][depth]
                    tensor_out[row][col][depth] = max_val
                    #print(type(tensor_out[row][col][depth]))
        ## fix the shape of tensor_out
        print("[DEBUG]Finish MaxPool2D Layer forwarding!!")
        #print("Feature Map Shape: %ix%ix%i" % tuple(out_shape))
        self._output = tensor_out
        return tensor_out

    def getOutput(self):
        return self._output

class FlattenLayer:
    def __init__(self):
        self._output = None
    def forward(self, tensor_in):
        tensor_out = self._flatten(tensor_in)
        self._output = tensor_out
        return tensor_out
    def _flatten(self, x):
        if isinstance(x, collections.Iterable):
            return [a for i in x for a in self._flatten(i)]
        else:
            return [x]
    def getOutput(self):
        return self._output

class NNModel:
    def __init__(self):
        self.layers = []

    def forward(self, tensor_in):
        # tensor_it = tensor_in
        print("[DEBUG]DNN start forwarding")
        for i, layer in enumerate(self.layers):
            tensor_in = layer.forward(tensor_in)
        print("[DEBUG]DNN finish forwarding")
        return tensor_in

    def getLayOutput(self, idx):
        if idx >= len(self.layers):
            return None
        else:
            return self.layers[idx].getOutput()

    def addLayer(self, layer):

        if type(layer) == Conv2D:
            #print("Conv2D")
            # shape: (outputs, rows, cols, channel)
            weights = layer.get_weights()[0].transpose(3, 0, 1, 2)
            biases = layer.get_weights()[1]
            activation = layer.get_config()['activation']

            self.layers.append(Conv2DLayer(weights, biases, weights.shape))
            # print("Add Activation Layer:", activation)
            self.layers.append(ActivationLayer(activation))
        elif type(layer) == Dense:
            #print("Dense")
            # shape: (outputs, inputs)
            weights = layer.get_weights()[0].transpose()
            biases = layer.get_weights()[1]
            activation = layer.get_config()['activation']

            self.layers.append(DenseLayer(weights, biases, weights.shape))
            # print("Add Activation Layer:", activation)
            self.layers.append(ActivationLayer(activation))
        elif type(layer) == MaxPool2D:
            #print("MaxPool2D")
            pool_size = layer.get_config()['pool_size']
            # print(pool_size)
            self.layers.append(MaxPool2DLayer(pool_size))
        elif type(layer) == Flatten:
            #print("Flatten")
            self.layers.append(FlattenLayer())
        else:
            raise NotImplementedError()
