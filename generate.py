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
        Output(ep, Ap, Bp, F1, F2, H(ep, d))
        yield ep

def correctness(e, a1, a2, b1, b2):
    pass

def generate_line(n, num_h_args=1, field=GF(2)):
    for typ in ["Plus", "H"]:
        if typ == "Plus":
            for coefs in cartesian_product([field] * n):
                xs = [ arg for (arg, coef) in zip(range(n), coefs) if coef ]
                yield lambda e: Plus(e, *xs)

            # for xs in itertools.combinations(range(n), num_plus_args):
                # yield lambda e: Plus(e, *xs)
        if typ == "H":
            for xs in itertools.combinations(range(n), num_h_args):
                yield lambda e: H(e, *xs)

def generate_Gb(e, num_lines, starting_at=1):
    def rec(n, lines):
        if n == 0:
            ep = copy.deepcopy(e)
            lines = map(lambda line: line(ep), lines)
            yield tuple([ep] + lines[-3:])
        for line in generate_line(n + starting_at - 1):
            for x in rec(n-1, [line] + lines): yield x
    return rec(num_lines, [])
