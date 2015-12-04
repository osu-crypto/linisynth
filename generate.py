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

def generate_security_game(a1, a2, b1, b2, num_lines=7, field=GF(2)):
    e = env(field)
    A = Rand(e)
    B = Rand(e)
    d = Rand(e)
    for (ep, F1, F2, C) in generate_Gb(e, num_lines, starting_at=3, field=field):
        Ap = Plus(ep, A, d) if a1 + b1 else A
        Bp = Plus(ep, B, d) if a2 + b2 else B
        Output(ep, Ap, Bp, F1, F2, H(ep, d))
        yield ep

def res(a1, a2, b1, b2):
    pass

def correctness(e, a1, a2, b1, b2):
    pass

def generate_line(n, num_h_args=1, field=GF(2)):
    if n == 0: raise StopIteration
    for typ in ["Plus", "H"]:
        if typ == "Plus":
            for coefs in cartesian_product([field] * n):
                if not any(coefs): continue
                xs = zip(coefs, range(n))
                yield lambda e: Plus(e, *xs)
        if typ == "H":
            for xs in itertools.combinations(range(n), num_h_args):
                yield lambda e: H(e, *xs)

def generate_Gb(e, num_lines, starting_at=1, field=GF(2)):
    def rec(n, lines):
        if n == 0:
            ep = copy.deepcopy(e)
            lines = map(lambda line: line(ep), lines)
            yield tuple([ep] + lines[-3:]) # convention: the last 3 lines are output
        for line in generate_line(n + starting_at - 1, field=field):
            for x in rec(n-1, [line] + lines): yield x
    return rec(num_lines, [])

if __name__ == '__main__':
    for g in generate_security_game(1,1,1,1, field=GF(2)):
        l = g.to_linicrypt()
        n = normalize(l)
        (nrows, ncols) = n[0].dimensions()
        if n[0].rank() == nrows and len(n[1]) == 0:
            print "nrows={}, ncols={}, rank={}, n-constraints={}".format(nrows, ncols, rank(n[0]), len(n[1]))
            print l
            print n
            print
