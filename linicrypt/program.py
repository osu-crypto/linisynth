# dsl for building linicrypt programs
from sage.all import *

class constraint:
    def __init__(self, t, Q, a):
        self.t = t
        self.Q = Q
        self.a = a
    def __repr__(self):
        return "<{0.t}, {0.Q}, {0.a}>".format(self)
    def lhs(self): return self.Q
    def rhs(self): return self.a

class env (dict):
    def __init__(self, field): 
        self._next_ref = 0
        self._next_rand_id = 0
        self.output = []
        self.field = field

    def next_rand_id(self):
        tmp = self._next_rand_id
        self._next_rand_id += 1
        return tmp

    def next_ref(self):
        tmp = self._next_ref
        self._next_ref += 1
        return tmp

    def lookup(self, ref): 
        return self[ref]    

    def insert(self, elem):
        inv = {v:k for k,v in self.iteritems()}
        if elem in inv: return inv[elem]
        r = self.next_ref()
        self[r] = elem
        return r

    def to_linicrypt(self):
        n = len(filter(lambda e: e[0] in ["Rand", "H"], self.itervalues()))
        fresh_ctr = 0
        t_ctr = 0
        mapping = {}
        A = []
        C = []
        for ref, expr in self.iteritems():
            if expr[0] == "Rand":
                row = vector(self.field, [0]*n)
                row[fresh_ctr] = 1
                fresh_ctr += 1
            elif expr[0] == "H":
                row = vector(self.field, [0]*n)
                row[fresh_ctr] = 1
                fresh_ctr += 1
                Q = [ A[mapping[arg]] for arg in expr[1] ]
                C.append(constraint(t_ctr, Q, row))
                t_ctr += 1
            elif expr[0] == "Plus":
                row = vector(self.field, [0]*n)
                for arg in expr[1]:
                    row += A[mapping[arg]]
            else:
                raise Exception("Unknown instruction: " + expr[0])
            mapping[ref] = len(A)
            A.append(row)
        # TODO: REMOVE LINES THAT AREN'T IN OUTPUT
        # for ref in self.iterkeys():
            # if not ref in self.output:
                 
        return (matrix(self.field, A), C)
    
def Rand(env):
    ident = env.next_rand_id()
    return env.insert(("Rand", ident))

def Plus(env, *args):
    return env.insert(("Plus", args))

def H(env, *args):
    return env.insert(("H", args))

def Output(env, *args):
    assert(not len(env.output))
    env.output = args

