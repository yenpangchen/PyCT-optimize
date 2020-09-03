# Copyright: see copyright.txt

class Constraint:
    def __init__(self, parent, last_predicate, height=0):
        self.parent = parent # 可能是 None 或 Constraint type
        self.last_predicate = last_predicate # 應該是 Predicate type
        self.processed = False # 只是給我們看的，程式流程用不到這個
        self.children = [] # 裝了一堆 Constraint type
        self.height = height

    def __eq__(self, other):
        """Two Constraints are equal iff they have the same chain of predicates"""
        return isinstance(other, self.__class__) and \
            self.parent is other.parent and \
            self.last_predicate == other.last_predicate

    def get_asserts_and_query(self):
        self.processed = True # 只是給我們看的，程式流程用不到這個

        # collect the assertions
        asserts = []
        tmp = self.parent
        while tmp.last_predicate is not None: # 目前根據 path_to_constraint 的 constructor 猜測，它負責檢測是不是 root constraint
            asserts.append(tmp.last_predicate)
            tmp = tmp.parent
        return asserts, self.last_predicate

    def find_child(self, predicate):
        for c in self.children:
            if predicate == c.last_predicate:
                return c
        return None

    def add_child(self, predicate):
        assert self.find_child(predicate) is None
        c = Constraint(self, predicate, self.height + 1)
        self.children.append(c)
        return c

    def __str__(self):
        return str(self.last_predicate) + f"  (processed: {self.processed}, path_len: {self.height})"
