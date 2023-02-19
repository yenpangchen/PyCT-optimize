
import argparse, logging, os, sys
from itertools import product

MODELNAME = "myModel"

f = argparse.RawTextHelpFormatter._split_lines
argparse.RawTextHelpFormatter._split_lines = lambda *args, **kwargs: f(*args, **kwargs) + ['']
parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)

parser.add_argument("nnpath", metavar="path.to.NN", help="import path to the target Neural Network in .hd5 format (file) relative to the project root")
parser.add_argument("image", metavar="image_file", help="Initial vector/matrix (file) of the Concolic tester. The input should repect the format illustrated in README.md")
# args = parser.parse_args()

class TestArgs:
    def __init__(self) -> None:
        self.nnpath = None
        self.image = None

args = TestArgs()
# args.nnpath = "model/simple_mnist_m6_09585.h5"
args.nnpath = "model/simple_mnist_bad_07685.h5"
args.image = "dnn_example/mnist/0_12_random.in"

with open('dnnct/template.py', "r") as f:
    f_temp = f.read()

f_temp = f_temp.replace("REPLACEME", args.nnpath)

concolic_dict = dict()
value_dict = dict()

with open('dnn_predict.py', "w+") as f_pred, open(args.image, "r") as f_img:
    f_pred.write(f_temp) # model construction
    header = [ int(s) for s in f_img.readline().strip().split(',') ]
    img_shape, num_concolic = header[:-1], header[-1]
    num_pred_args = img_shape[0]*img_shape[1]*img_shape[2]
    f_pred.write("\ndef predict(")
    args_str = ""
    for i, j, k in product( range(0, img_shape[0]),
                            range(0, img_shape[1]),
                            range(0, img_shape[2])):
        if i or j or k: args_str += ", "
        arg_name = "p_{row}_{col}_{ch}".format(row=i, col=j, ch=k)
        args_str += arg_name
        concolic_dict[arg_name], value_dict[arg_name] = 0, 0

    f_pred.write(args_str); f_pred.write("):\n")
    
    ## function body
    f_pred.write("\timg_in = np.zeros(({row}, {col}, {ch})).tolist()\n".format(row=img_shape[0], col=img_shape[1], ch=img_shape[2]))
    for i, j, k in product( range(0, img_shape[0]),
                            range(0, img_shape[1]),
                            range(0, img_shape[2])):
        f_pred.write("\timg_in[{row}][{col}][{ch}]=p_{row}_{col}_{ch}\n".format(row=i, col=j, ch=k) )
    f_pred.write("\tout_val={model}.forward(img_in)\n".format(model=MODELNAME))
    f_pred.write("\tmax_val, ret_class = -100.0, 0\n")
    f_pred.write("\tfor i,cl_val in enumerate(out_val):\n")
    f_pred.write("\t\tif cl_val > max_val:\n")
    f_pred.write("\t\t\tmax_val, ret_class = cl_val, i\n")
    f_pred.write("\tprint(\"[DEBUG]predicted class:\", ret_class)\n")
    f_pred.write("\treturn ret_class")


    ## PyCT command generation
    for ch in range(img_shape[2]):
        for row in range(img_shape[0]):
            line = f_img.readline().strip()
            vals = [ float(s) for s in line.split()]
            for col in range(img_shape[1]):
                value_dict["p_{r}_{c}_{ch}".format(r=row, c=col, ch=ch)] = vals[col]
                
    
    for _ in range(num_concolic):
        line = f_img.readline().strip()
        pos = [ int(s) for s in line.split()]
        concolic_dict["p_{r}_{c}_{ch}".format(r=pos[0], c=pos[1], ch=pos[2])] = 1

verb_option = "-v 1"
s_TO_option = "--single_timeout 900"
t_TO_option = "--total_timeout 7200"
norm_option = "-n 1"
#smt_option = "-d SMT_LOG"

cmd = "./pyct.py dnn_predict.py \"{val_dict}\" -c \"{con_dict}\" {verb} {single_to} {total_to} {n_option} -r . -s predict ".format(
    val_dict=value_dict, con_dict=concolic_dict, verb=verb_option, single_to=s_TO_option, n_option=norm_option,
    total_to=t_TO_option)

#cmd = "./pyct.py dnn_predict \"{val_dict}\"  {verb} {single_to} {smt} {n_option} -r . -s predict ".format(
#    val_dict=value_dict, con_dict=concolic_dict, verb=verb_option, single_to=s_TO_option, n_option=norm_option, smt = smt_option)

#print("running command: {command}".format(command=cmd))
os.system(cmd)
with open("cmd.do", "w+" ) as f_cmd:
    f_cmd.write(cmd)

# num_rows, num_cols, num_of_channels, num_concolic_pixel

# e.g. for a RGB 4x4 images, 


# 4, 4, 3, 3
# 11  12  13  14
# 21  22  23  24
# 31  32  33  34
# 41  42  43  44
# 11  12  13  14
# 21  22  23  24
# 31  32  33  34
# 41  42  43  44
# 11  12  13  14
# 21  22  23  24
# 31  32  33  34
# 41  42  43  44
# 1  1  1
# 1  2  3
# 2  1  3


