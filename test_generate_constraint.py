from libct.constraint import Constraint
from  libct.concolic.float import ConcolicFloat
import libct.explore
from libct.solver import Solver


formula = None
logfile = None
safety = 0
timeout = 10
verbose = 0
statsdir = None


engine = libct.explore.ExplorationEngine(solver='cvc4', timeout=timeout, safety=safety,
                                           store=formula, verbose=verbose, logfile=logfile,
                                           statsdir=statsdir)

args = {
    'a': 10,
    'b': ConcolicFloat(0.0, 'var1', engine),
}

def test(a, b):
    if a+b > 20:
        return 1
    else:
        return 0

test(**args)


constraint = engine.constraints_to_solve.pop(0)
solution = Solver.find_model_from_constraint(engine, constraint)



print(Constraint.global_constraints)


