from sage.all import *
import copy

class Graph (dict):
    def __init__(self, vertices):
        for v in vertices:
            self[str(v)] = dict()
    def add_edge(self, source, target, color):
        self[str(source)][str(target)] = color
    def path(self, source, success_func):
        visited = []
        queue   = [str(source)]
        while queue:
            u = queue.pop(0)
            if success_func(u): return True
            visited.append(u) 
            for v in self[u]:
                if v not in visited: queue.append(v)

def usefulfor(x, a_inp):
    A = matrix(filter(lambda r: r != vector(x), a_inp))
    for v in A:
        Ap = matrix(filter(lambda r: r != v, A))
        if v in span(Ap):
            yield v

def normalize(M, C):
    reachable = M.rows()
    S = copy.copy(C)
    G = Graph(M)
    done = False
    while not done:
        c = constraintInSpan(S, reachable)
        if not c:
            done = True
        else:
            for q in c.Q:
                for v in usefulfor(q, reachable):
                    G.add_edge(v, c.a, "black")
            for v in usefulfor(c.a, reachable):
                G.add_edge(v, c.a, "red")
            reachable.append(c.a)

    def keepConstraint(c):
        ok = True
        ok = ok and all([q in span(reachable) for q in c.Q]) 
        ok = ok and G.path(c.a, lambda x: "red" in G[x].values())
        return ok

    Cp = filter(keepConstraint, C)
    return (M, Cp)

# while there exists <t,Q,a> \in S with rows(Q) \subeq span(Reachable)
def constraintInSpan(S, reachable):
    for c in S:
        if all([q in span(reachable) for q in c.Q]):
            S.remove(c)
            return c

