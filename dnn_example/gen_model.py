import tensorflow as tf
import numpy as np
import sys
from keras import backend as K
from keras.models import Model


from tensorflow.keras import datasets, layers, models
import keras


# https://www.tensorflow.org/tutorials/images/cnn

(train_images, train_labels), (test_images, test_labels) = datasets.cifar10.load_data()
train_images, test_images = train_images / 255.0, test_images / 255.0


# for i in range(3):
#     #print(train_images[0].shape, train_labels[0])
#     shape = train_images[0].shape
#     tmp = train_images[0].reshape(shape[2], shape[0], shape[1])
#     #np.savetxt(sys.stdout, tmp[i], fmt='%.10f')

# model = keras.models.load_model("cnn_simple.h5")
# print(model.predict( train_images[0:1] ) )


# layer_name = 'max_pooling2d'
# intermediate_layer_model = Model(inputs=model.input,
#                                  outputs=model.get_layer(layer_name).output)
# intermediate_output = intermediate_layer_model.predict(train_images[0:1])
# #print(intermediate_output.shape)
# #print(intermediate_output.tolist())
# exit()

class_names = ['airplane', 'automobile', 'bird', 'cat', 'deer',
               'dog', 'frog', 'horse', 'ship', 'truck']
               
model = models.Sequential()
model.add(layers.Conv2D(8, (3, 3), activation='relu', input_shape=(32, 32, 3)))
model.add(layers.MaxPooling2D((2, 2)))
# model.add(layers.Conv2D(8, (3, 3), activation='relu'))
# model.add(layers.MaxPooling2D((2, 2)))
# model.add(layers.Conv2D(8, (3, 3), activation='relu'))

model.add(layers.Flatten())
model.add(layers.Dense(8, activation='relu'))
model.add(layers.Dense(10))

model.summary()

model.compile(optimizer='adam',
              loss=tf.keras.losses.SparseCategoricalCrossentropy(from_logits=True),
              metrics=['accuracy'])

model.fit(train_images, train_labels, epochs=1, 
                    validation_data=(test_images, test_labels))



model.save("cnn_simple.h5")

