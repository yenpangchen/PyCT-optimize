#!/usr/bin/env python3

import argparse, logging, os, sys
import conbyte.explore

# Our main program starts now!
parser = argparse.ArgumentParser()

# Execution configuration
parser.add_argument("file", metavar="path_to_file.py", help="the target file")
parser.add_argument("inputs", metavar="input_args", help="the input arguments")
parser.add_argument("-e", "--entry", dest="entry", help="entry point, if different from path_to_file.py", default=None)
parser.add_argument("-m", "--iter", dest="iteration", help="maximum number of iterations", type=int, default=200)
parser.add_argument("--safety", dest="safety", help="expression value safety level", type=int, default=0)
parser.add_argument("-t", "--timeout", dest="timeout", help="solver timeout (default = 10 sec)", type=int, default=10)
parser.add_argument("--timeout2", dest="timeout2", help="execution timeout (default = 15 sec)", type=int, default=15)

# Logging configuration
parser.add_argument("-f", "--formula", dest='formula', help="folder or file to store smtlib2 formulas", default=None)
parser.add_argument("-l", "--logfile", dest='logfile', help="store log", default=None)
parser.add_argument("-v", "--verbose", dest='verbose', help="set the verbosity level", type=int, default=1)

# Solver configuration
parser.add_argument("-s", "--solver", dest='solver', help="solver=[z3seq, z3str, trauc, cvc4]. Currently only support cvc4.", default="cvc4")

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
