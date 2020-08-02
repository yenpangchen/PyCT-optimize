#!/usr/bin/env python3

import argparse, logging, os, sys
import conbyte.explore

# Our main program starts now!
parser = argparse.ArgumentParser()

# Setup
parser.add_argument("file", metavar="path_to_target_file.py", help="specify the target file")
parser.add_argument("inputs", metavar="input_args", help="specify the input arguments")
parser.add_argument("-e", "--entry", dest="entry", action="store", help="specify entry point, if different from path_to_target_file.py", default=None)
parser.add_argument("-m", "--max_iter", dest="iteration", action="store", help="specify max iterations", type=int, default=50)
parser.add_argument("-t", "--timeout", dest="timeout", action="store", help="specify solver timeout (default = 1sec)", default=None)

# Logging configuration
parser.add_argument("-d", "--debug", dest='debug', action="store_true", help="enable debug logging")
parser.add_argument("-q", "--query", dest='query', action="store", help="store smt queries", default=None)
parser.add_argument("--quiet", dest='quiet', action="store_true", help="no logging")
parser.add_argument("-l", "--logfile", dest='logfile', action="store", help="store log", default=None)
parser.add_argument("--json", dest='get_json', action="store_true", help="print JSON format to stdout", default=None)

# Solver configuration
parser.add_argument("-s", "--solver", dest='solver', action="store", help="solver=[z3seq, z3str, trauc, cvc4], default to z3", default="z3seq")

# Parse arguments
args = parser.parse_args()

# Check the target file
if not os.path.exists(args.file):
    parser.error("the given target file is invalid")
    sys.exit(1)

###################################################################################
# This section mainly deals with the logging settings.
if args.debug:
    log_level = logging.DEBUG
else:
    log_level = logging.INFO
if args.logfile is not None:
    logging.basicConfig(filename=args.logfile, level=log_level, stream=sys.stdout,
                        format='%(asctime)s  %(name)s\t%(levelname)s\t%(message)s',
                        datefmt='%m/%d/%Y %I:%M:%S %p')
elif args.quiet:
    logging.basicConfig(filename="/dev/null", stream=sys.stdout)
else:
    if args.get_json:
        logging.basicConfig(filename="/dev/null", level=log_level, stream=sys.stdout,
                            format='  %(name)s\t%(levelname)s\t%(message)s')
    else:
        logging.basicConfig(level=log_level, stream=sys.stdout,
                            format='  %(name)s\t%(levelname)s\t%(message)s')
###################################################################################

#####################################################################################################################
# This section creates an explorer instance and starts our analysis procedure!
engine = conbyte.explore.ExplorationEngine()
print("\n# of iterations:", engine.explore(args.solver, args.file, args.entry, eval(args.inputs), args.iteration, args.timeout, args.query))
#####################################################################################################################

###############################################################################
# This section prints the generated inputs and coverage results.
if args.quiet: sys.exit(0)
if not args.get_json:
    print("\nGenerated inputs")
    for inputs in engine.inputs:
        print(inputs)
    if len(engine.errors) > 0: print("\nError inputs")
    for inputs in engine.errors:
        print(inputs)
    engine.print_coverage()
else:
    print(engine.result_to_json()); print()
result_list = list(zip(engine.inputs, engine.results))
print("# of input vectors:", len(result_list))
print(result_list); print()
print(bool(engine.coverage_statistics()[2]))
###############################################################################
