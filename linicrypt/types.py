from sage.all import *

class Constraint:
    def __init__(self, t, Q, a):
        self.t = t
        self.Q = Q
        self.a = a
    def __repr__(self):
        return "<{0.t}, {0.Q}, {0.a}>".format(self)
    def lhs(self): return self.Q
    def rhs(self): return self.a

