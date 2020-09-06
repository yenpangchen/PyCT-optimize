#!/usr/bin/env python3

import argparse, logging, os, sys
import conbyte.explore

# Our main program starts now!
parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)

# Execution configuration
parser.add_argument("file", metavar="filename.py", help="target file")
parser.add_argument("inputs", metavar="input_args", help="input arguments of the target function")
parser.add_argument("-e", "--entry", dest="entry", help="name of the target function\nIf the function name is the same as that of the target file, this option can be omitted.", default=None)
parser.add_argument("-m", "--iter", dest="iteration", help="maximum number of iterations [default = 200]", type=int, default=200)
parser.add_argument("--safety", dest="safety", help="indicates the behavior when the values in Python and in SMTLIB2 of a concolic object are not equal. [default = 0]\n(0) The expression in a concolic object is still preserved even if the values are different.\n(1) The expression in a concolic object will be erased if the values are different, but the process still continues.\n(2) The expression in a concolic object will be erased if the values are different, and the process terminates soon afterwards.", type=int, default=0)
parser.add_argument("-t", "--timeout", dest="timeout", help="timeout (sec.) for the solver to solve a constraint [default = 10]", type=int, default=10)
parser.add_argument("--timeout2", dest="timeout2", help="timeout (sec.) for the explorer to go through one iteration [default = 15]", type=int, default=15)

# Logging configuration
parser.add_argument("-f", "--formula", dest='formula', help="name of directory or file to store smtlib2 formulas\n(*) When this argument is a pure positive integer N, it means that we only want to store the N_th constraint\nwhere N is the number \"SMT-id\" shown in the log. The file should be named {N}.smt2 in the current directory.\n(*) Otherwise, this argument names the directory, and all constraints will be stored in this directory whose\nnames follow the rule mentioned above.\nIn either case, these *.smt2 files should be able to be called by solvers directly.", default=None)
parser.add_argument("-l", "--logfile", dest='logfile', help="name of the log file\n(*) When this argument is an empty string, all logging messages will not be dumped either to screens or to files.\n(*) When this option is not set, the logging messages will be dumped to screens.", default=None)
parser.add_argument("-v", "--verbose", dest='verbose', help="logging level [default = 1]\n(0) Show messages whose levels not lower than WARNING.\n(1) Show messages from (0), plus basic iteration information.\n(2) Show messages from (1), plus solver information\n(3) Show messages from (2), plus all concolic object's information.", type=int, default=1)

# Solver configuration
# solver=[z3seq, z3str, trauc, cvc4]
parser.add_argument("-s", "--solver", dest='solver', help="solver type [default = cvc4]\nWe currently only support CVC4.", default="cvc4")

# Parse arguments
args = parser.parse_args()

# Check the target file
if not os.path.exists(args.file):
    parser.error("the given target file is invalid")
    sys.exit(1)

######################################################################################################
# This section mainly deals with the logging settings.
log_level = 25 - 5 * args.verbose # Please refer to ExplorationEngine.__init__ for the formula design.
if args.logfile:
    logging.basicConfig(filename=args.logfile, level=log_level,
                        format='%(asctime)s  %(name)s\t%(levelname)s\t %(message)s',
                        datefmt='%m/%d/%Y %I:%M:%S %p')
elif args.logfile == '':
    logging.basicConfig(level=logging.CRITICAL+1)
else:
    logging.basicConfig(level=log_level,# stream=sys.stdout,
                        format='  %(name)s\t%(levelname)s\t %(message)s')
######################################################################################################

#####################################################################################################################
# This section creates an explorer instance and starts our analysis procedure!
engine = conbyte.explore.ExplorationEngine(args.solver, args.timeout, args.safety, args.formula)
print("\nTotal iterations:", engine.explore(args.file, args.entry, eval(args.inputs), args.iteration, args.timeout2))
#####################################################################################################################

###############################################################################
# This section prints the generated inputs and coverage results.
print("\nGenerated inputs")
for inputs in engine.inputs:
    print(inputs)
if len(engine.errors) > 0: print("\nError inputs")
for inputs in engine.errors:
    print(inputs)
engine.print_coverage() # Line coverage + Branch coverage + Missing lines
result_list = list(zip(engine.inputs, engine.results))
print("# of input vectors:", len(result_list))
print(result_list)
###############################################################################
