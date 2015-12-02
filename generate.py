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

# def generate_security_game(a1, a2, b1, b2):
def generate_security_game():
    e = env(GF(2))
    A = Rand(e)
    B = Rand(e)
    d = Rand(e)
    # for (ep, F1, F2, C) in generate_Gb(e, b1, b2, A, B, d):
    for (ep, F1, F2, C) in generate_Gb(e, A, B, d):
        Ap = Plus(ep, A, d) if a1 + b1 else A
        Bp = Plus(ep, B, d) if a2 + b2 else B
        Cp = Plus(ep, C, d) if 1 + res(a1, a2, b1, b2) else C
        Output(ep, Ap, Bp, F1, F2, H(Cp))
        yield ep

def correctness(e, a1, a2, b1, b2):
    pass

def generate_line(args):
    for typ in ["Plus", "H"]:
        if typ == "Plus":
            for xs in itertools.combinations(args, 2):
                yield lambda e: Plus(e, xs)
        if typ == "H":
            for xs in itertools.combinations(args, 1):
                yield lambda e: H(e, xs)

def generate_Gb(b1, b2, *args):
    for l1 in generate_line(args):
        for l2 in generate_line(args):
            for l3 in generate_line(args):
                for l4 in generate_line(args):
                    def prog(e):
                        ep = copy.deepcopy(e)
                        r1 = l1(ep)
                        r2 = l2(ep)
                        r3 = l3(ep)
                        r4 = l4(ep)
                        for outs in itertools.combinations([r1,r2,r3,r4], 3):
                            ep.output = outs
                        yield ep
