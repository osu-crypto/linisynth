from sage.all import *
from linicrypt.normalize import *
from linicrypt.program import *
import itertools
import copy

def test():
    e = env(GF(2))
    v1 = Rand(e)
    v2 = Rand(e)
    v3 = Plus(e, v1, v2)
    v4 = H(e, v3)
    v5 = Plus(e, v4, v1)
    Output(e, v3, v5)
    return e

def res(a1, a2, b1, b2):
    pass

def generate_security_game(a1, a2, b1, b2):
    e = env(GF(2))
    A = Rand(e)
    B = Rand(e)
    d = Rand(e)
    for (ep, F1, F2, C) in generate_Gb(e, num_lines=8, starting_at=4):
        Ap = Plus(ep, A, d) if a1 + b1 else A
        Bp = Plus(ep, B, d) if a2 + b2 else B
        Output(ep, Ap, Bp, F1, F2, H(d))
        yield ep

def correctness(e, a1, a2, b1, b2):
    pass

def generate_line(n):
    for typ in ["Plus", "H"]:
        if typ == "Plus":
            for xs in itertools.combinations(range(n), 2):
                yield lambda e: Plus(e, xs)
        if typ == "H":
            for x in range(n):
                yield lambda e: H(e, [x])

def generate_Gb(e, num_lines, starting_at=0):
    def rec(n, lines):
        if n == 0:
            ep = copy.deepcopy(e)
            lines = map(lambda line: line(ep), lines)
            t = len(lines)
            ep.output = [t, t-1, t-2]
            return [ep] + lines[-3:]
        res = []
        for l in generate_line(n + starting_at-1):
            res.extend(rec(n-1, lines + [l]))
        return res
    return rec(num_lines, [])
