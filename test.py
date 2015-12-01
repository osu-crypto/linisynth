from sage.all import *
from linicrypt.types import *
from linicrypt.normalize import *

f = GF(2)
def mat(xs): return matrix(f, xs)
def vec(xs): return vector(f, xs)

test_m = mat([[1,0,0],[0,1,0],[1,1,0],[0,0,1],[1,0,1]])
test_c = [Constraint(0, mat([[1,1,0]]), vec([0,0,1]))]
