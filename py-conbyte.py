#!/usr/bin/env python3

import argparse, logging, os, sys
import conbyte.explore

# Our main program starts now!
f = argparse.RawTextHelpFormatter._split_lines
argparse.RawTextHelpFormatter._split_lines = lambda *args, **kwargs: f(*args, **kwargs) + ['']
parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)

# Execution configuration
parser.add_argument("modpath", metavar="path.to.module", help="absolute import path to the target module (file) relative to the project root\nEx1: ./a/b/c.py -> a.b.c\nEx2: ./def.py -> def")
parser.add_argument("input", metavar="input_dict", help="dictionary of initial arguments to be passed into the target function\nPlease note that the double quotes outside the dictionary cannot be omitted!\nEx1: func(a=1,b=2) -> \"{'a':1,'b':2}\"\nEx2: func(a='',b='') -> \"{'a':'','b':''}\"")
parser.add_argument("-r", "--root", dest="root", help="path to the project root which the target function belongs to [default = path/to/this/project]\nThis option should always be provided if the target function belongs to another project.\nIf the target project is put inside this project (i.e., the latter's root path is a prefix of the former's),\nthe scope of coverage is only the target \"file.\" Otherwise, the scope covers the whole \"project.\"", default=os.path.dirname(__file__))
parser.add_argument("-s", "--func", dest="func", help="name of the target function\n(*) If the function \"func\" belongs to a class \"CLASS\", this name should be \"CLASS.func\".\n(*) If the function name is the same as that of the target file, this option can be omitted.", default=None)
parser.add_argument("-m", "--iter", dest="iter", help="maximum number of iterations [default = 200]", type=int, default=200)
parser.add_argument("--lib", dest="lib", help="another library path to be inserted at the beginning of sys.path\nFor example, if the target function belongs to another project requiring a virtual environment,\nyou may want to do \"--lib ~/.local/share/virtualenvs/projectname-projectid/lib/python3.8/site-packages\".", default=None)
parser.add_argument("--safety", dest="safety", help="indicates the behavior when the values in Python and in SMTLIB2 of a concolic object are not equal. [default = 0]\n(0) The expression in a concolic object is still preserved even if the values are different.\n(1) The expression in a concolic object will be erased if the values are different, but the program still continues.\n(2) The expression in a concolic object will be erased if the values are different, and the program exits soon.\nOnly in level 0 don't we verify return values of the target function since some objects in fact are not picklable,\nand therefore information about return values will not printed in the end.", type=int, default=0)
parser.add_argument("-t", "--timeout", dest="timeout", help="timeout (sec.) for the solver to solve a constraint [default = 10]", type=int, default=10)
parser.add_argument("--timeout2", dest="timeout2", help="timeout (sec.) for the explorer to go through one iteration [default = 15]", type=int, default=15)
parser.add_argument("--include_exception", dest="include_exception", action='store_true', help="update coverage statistics also when the return value is not picklable.")

# Logging configuration
parser.add_argument("-v", "--verbose", dest='verbose', help="logging level [default = 1]\n(0) Show messages whose levels not lower than WARNING.\n(1) Show messages from (0), plus basic iteration information.\n(2) Show messages from (1), plus solver information.\n(3) Show messages from (2), plus all concolic objects' information.", type=int, default=1)
parser.add_argument("-l", "--logfile", dest='logfile', help="name of the log file\n(*) When this argument is an empty string, all logging messages will not be dumped either to screens or to files.\n(*) When this option is not set, the logging messages will be dumped to screens.", default=None)
parser.add_argument("-d", "--formula", dest='formula', help="name of directory or file to store smtlib2 formulas\n(*) When this argument is a pure positive integer N, it means that we only want to store the N_th constraint\nwhere N is the number \"SMT-id\" shown in the log. The file should be named {N}.smt2 in the current directory.\n(*) Otherwise, this argument names the directory, and all constraints will be stored in this directory whose\nnames follow the rule mentioned above.\nIn either case, these *.smt2 files should be able to be called by a solver directly.", default=None)
parser.add_argument("--dump_projstats", dest="dump_projstats", action='store_true', help="dump project statistics under the directory \"./project_statistics/{project_name}/{path.to.module}/{func_name}/**\".")

# Solver configuration
# solver=[z3seq, z3str, trauc, cvc4]
parser.add_argument("--solver", dest='solver', help="solver type [default = cvc4]\nWe currently only support CVC4.", default="cvc4")

# Parse arguments
args = parser.parse_args()

##############################################################################
# This section creates an explorer instance and starts our analysis procedure!
funcname = t if (t:=args.func) else args.modpath.split('.')[-1]
statsdir = os.path.abspath(os.path.dirname(__file__)) + '/project_statistics/' + os.path.abspath(args.root).split('/')[-1] + '/' + args.modpath + '/' + funcname if args.dump_projstats else None
engine = conbyte.explore.ExplorationEngine(solver=args.solver, timeout=args.timeout, safety=args.safety,
                                           store=args.formula, verbose=args.verbose, logfile=args.logfile,
                                           statsdir=statsdir)
print("\nTotal iterations:", engine.explore(args.modpath, eval(args.input), root=args.root, funcname=args.func,
                                            max_iterations=args.iter, timeout=args.timeout2, deadcode=None,
                                            include_exception=args.include_exception, lib=args.lib))
##############################################################################

################################################################
# This section prints the generated inputs and coverage results.
print("\nGenerated inputs")
print(engine.inputs)
if len(engine.errors) > 0: print("\nError inputs"); print(engine.errors)
engine.print_coverage() # Line coverage + Missing lines
if result_list := list(zip(engine.inputs, engine.results)):
    print("# of input vectors:", len(result_list)); print(result_list); print()
################################################################
