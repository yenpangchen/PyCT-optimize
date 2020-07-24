# Copyright: see copyright.txt
import logging
import conbyte.global_utils

from .predicate import Predicate
from .constraint import Constraint


log = logging.getLogger("ct.pathconstraint")

class PathToConstraint:
    def __init__(self):
        self.root_constraint = Constraint(None, None, None, None) # 我在想這一行有沒有暗示 root <==> parent 和 last_predicate 都是 None
        self.current_constraint = self.root_constraint
        self.expected_path = None

    def reset(self, expected): # expected 放的是 constraint, 裡面就存有最後一個 predicate 作為走訪起點, 向上走到 root 處
        self.current_constraint = self.root_constraint
        if expected is None:
            self.expected_path = None
        else:
            self.expected_path = []
            tmp = expected
            while tmp.last_predicate is not None:
                self.expected_path.append(tmp.last_predicate)
                tmp = tmp.parent
            assert tmp == self.current_constraint # 確保 tmp 最後一定是 root constraint

    def which_branch(self, conbool):
        if conbool.expr == 'nil':
            log.debug("Skip nil")
            return

        if isinstance(conbool.expr, bool):
            # Pure bool type assignment is normally not codition branch
            return

        p = Predicate(conbool.expr, conbool.value)
        c = self.current_constraint.find_child(p)
        pneg = Predicate(conbool.expr, not conbool.value)
        cneg = self.current_constraint.find_child(pneg)

        if c is None and cneg is None:
            c = self.current_constraint.add_child(p, conbyte.global_utils.extend_vars, conbyte.global_utils.extend_queries)
            c.processed = True # 只是給我們看的，程式流程用不到這個
            cneg = self.current_constraint.add_child(pneg, conbyte.global_utils.extend_vars, conbyte.global_utils.extend_queries)
            conbyte.global_utils.extend_vars = dict()
            conbyte.global_utils.extend_queries = []
            # we add the new constraint to the queue of the engine for later processing
            conbyte.global_utils.engine.constraints_to_solve.push(cneg) # dict(), [])) #new_constraints.append(cneg) #.add_constraint(cneg)
            log.debug("Cur constraint %s" % c)
            log.debug("Add constraint %s" % cneg)
        else:
            conbyte.global_utils.extend_vars = dict()
            conbyte.global_utils.extend_queries = []
            assert c is not None and cneg is not None

        self.current_constraint = c # 把當前的 constraint 移到我們要的 child

        # check for path mismatch
        # IMPORTANT: note that we don't actually check the predicate is the
        # same one, just that the direction taken is the same
        """
        if self.expected_path is not None and self.expected_path != []:
            expected = self.expected_path.pop()
            # while not at the end of the path, we expect the same predicate result
            # at the end of the path, we expect a different predicate result
            done = self.expected_path == []
            if (not done and expected.result != c.predicate.result or
                            done and expected.result == c.predicate.result):
                log.info("Replay mismatch (done=%s)" % done)
                log.debug(expected)
                log.debug(c.predicate)
        """
