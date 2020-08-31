# Copyright: see copyright.txt
import logging
import conbyte.constraint, conbyte.predicate
from conbyte.global_utils import unwrap

log = logging.getLogger("ct.pathconstraint")

class PathToConstraint:
    def __init__(self):
         # 我在想下面這一行有沒有暗示 root <==> parent 和 last_predicate 都是 None
        self.root_constraint = conbyte.constraint.Constraint(None, None, None, None)
        self.current_constraint = self.root_constraint

    def which_branch(self, conbool):
        # if conbool.expr == 'nil': log.debug("Skip nil"); return
        # if isinstance(conbool.expr, bool): return # Pure bool type assignment is normally not codition branch
        p = conbyte.predicate.Predicate(conbool.expr, unwrap(conbool))
        c = self.current_constraint.find_child(p)
        pneg = conbyte.predicate.Predicate(conbool.expr, not unwrap(conbool))
        cneg = self.current_constraint.find_child(pneg)
        if c is None and cneg is None:
            c = self.current_constraint.add_child(p, conbool.engine.extend_vars, conbool.engine.extend_queries)
            c.processed = True # 只是給我們看的，程式流程用不到這個
            cneg = self.current_constraint.add_child(pneg, conbool.engine.extend_vars, conbool.engine.extend_queries)
            conbool.engine.extend_vars = {}
            conbool.engine.extend_queries = []
            # we add the new constraint to the queue of the engine for later processing
            conbool.engine.constraints_to_solve.append(cneg)
            log.debug("Cur constraint %s" % c)
            log.debug("Add constraint %s" % cneg)
        else:
            conbool.engine.extend_vars = {}
            conbool.engine.extend_queries = []
            conbool.engine.num_of_extend_vars = 0
            assert c is not None and cneg is not None
        self.current_constraint = c # 把當前的 constraint 移到我們要的 child
