# Copyright: see copyright.txt

class Constraint:
    def __init__(self, parent, last_predicate, height=0):
        self.parent = parent # should be "None" or "a Constraint"
        self.last_predicate = last_predicate # should be "None" or "a Predicate"
        self.children = [] # a list of "Constraint"s
        self.height = height # for debugging purposes
        self.processed = False # for debugging purposes

    def __eq__(self, other):
        """Two Constraints are equal iff they have the same chain of predicates"""
        return isinstance(other, self.__class__) and \
            self.parent is other.parent and \
            self.last_predicate == other.last_predicate

    def __str__(self):
        return str(self.last_predicate) + f"  (processed: {self.processed}, path_len: {self.height})"

    def add_child(self, predicate):
        # assert self.find_child(predicate) is None
        c = Constraint(self, predicate, self.height + 1)
        self.children.append(c)
        return c

    def find_child(self, predicate):
        return next((c for c in self.children if c.last_predicate == predicate), None)

    def get_all_asserts(self):
        self.processed = True # for debugging purposes
        asserts = []; tmp = self
        while tmp.last_predicate is not None: # collect all the assertions in this constraint path
            asserts.append(tmp.last_predicate)
            tmp = tmp.parent
        return asserts
