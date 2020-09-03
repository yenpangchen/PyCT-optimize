# Copyright: see copyright.txt

import logging
from conbyte.constraint import Constraint
from conbyte.predicate import Predicate
from conbyte.utils import unwrap

log = logging.getLogger("ct.pathconstraint")

class PathToConstraint:
    root_constraint = None

    def __init__(self):
        if self.root_constraint is None:
            self.root_constraint = Constraint(None, None)
        self.current_constraint = self.root_constraint

    def add_branch(self, conbool):
        p = Predicate(conbool.expr, unwrap(conbool))
        c = self.current_constraint.find_child(p)
        pneg = Predicate(conbool.expr, not unwrap(conbool))
        cneg = self.current_constraint.find_child(pneg)
        if c is None and cneg is None:
            c = self.current_constraint.add_child(p); c.processed = True # for debugging purposes
            cneg = self.current_constraint.add_child(pneg)
            conbool.engine.constraints_to_solve.append(cneg) # add the negated constraint to the queue for later traversal
            log.debug(f"Cur constraint {c}"); log.debug(f"Add constraint {cneg}")
        else:
            assert c is not None and cneg is not None
        self.current_constraint = c # 把當前的 constraint 移到我們要的 child
