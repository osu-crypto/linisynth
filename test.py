from sage.all import *
from linicrypt.normalize import *
from linicrypt.program import *

f = GF(2)

def security_game(Gb, a1, a2, b1, b2):
    e = env(f)
    A     = Rand(e)
    B     = Rand(e)
    delta = Rand(e)
    (F1, F2, C) = Gb(e, b1, b2, A, B, delta)
    Ap = Plus(e, A, delta) if a1 + b1 else A
    Bp = Plus(e, B, delta) if a2 + b2 else B
    Cp = Plus(e, C, delta) if 1 + res(a1, a2, b1, b2) else C
    Output(e, Ap, Bp, F1, F2, H(Cp))
    return e

def test():
    e = env(f)
    v1 = Rand(e)
    v2 = Rand(e)
    v3 = Plus(e, v1, v2)
    v4 = H(e, v3)
    v5 = Plus(e, v4, v1)
    Output(e, v3, v5)
    return e

