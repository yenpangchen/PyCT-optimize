import keras
from dnnct.myDNN import ACTIVATIONS, NNModel, LAYERS 
import numpy as np
import sys
from tensorflow.keras import datasets, layers
from keras.layers import (
    Dense,
    Conv1D, Conv2D,
    LocallyConnected1D, LocallyConnected2D,
    Flatten,
    ELU,
    Activation,
    MaxPooling2D,
    LSTM,
    Embedding,
    BatchNormalization,
)

(train_images, train_labels), (test_images, test_labels) = datasets.cifar10.load_data()
train_images, test_images = train_images / 255.0, test_images / 255.0


model = keras.models.load_model("dnn_example/cnn_simple.h5")
layers = [l for l in model.layers if type(l).__name__ not in ['Dropout']]
myModel = NNModel()
for layer in layers:
	myModel.addLayer(layer)

# shape = train_images[1].shape
# print(shape)
img = train_images[0]#.reshape(shape[0], shape[1], shape[2])
print(myModel.forward(img.tolist()))
#print(myModel.getLayOutput(2))
