# Copyright: see copyright.txt
import logging
import conbyte.constraint, conbyte.predicate
from conbyte.utils import unwrap

log = logging.getLogger("ct.pathconstraint")

class PathToConstraint:
    def __init__(self):
         # 我在想下面這一行有沒有暗示 root <==> parent 和 last_predicate 都是 None
        self.root_constraint = conbyte.constraint.Constraint(None, None)
        self.current_constraint = self.root_constraint

    def add_branch(self, conbool):
        p = conbyte.predicate.Predicate(conbool.expr, unwrap(conbool))
        c = self.current_constraint.find_child(p)
        pneg = conbyte.predicate.Predicate(conbool.expr, not unwrap(conbool))
        cneg = self.current_constraint.find_child(pneg)
        if c is None and cneg is None:
            c = self.current_constraint.add_child(p)
            c.processed = True # 只是給我們看的，程式流程用不到這個
            cneg = self.current_constraint.add_child(pneg)
            # we add the new constraint to the queue of the engine for later processing
            conbool.engine.constraints_to_solve.append(cneg)
            log.debug(f"Cur constraint {c}")
            log.debug(f"Add constraint {cneg}")
        else:
            assert c is not None and cneg is not None
        self.current_constraint = c # 把當前的 constraint 移到我們要的 child
