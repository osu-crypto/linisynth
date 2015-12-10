#/usr/bin/env python2

from pysmt.shortcuts import *
from pysmt.typing import BOOL
import string
import itertools
import copy

T = TRUE()
F = FALSE()

def mat(nrows, ncols, premapping={}): 
    return [ premapping[y] if y in premapping else [ FreshSymbol(BOOL) for x in range(ncols) ] for y in range(nrows) ]

def gate(i, j):
    bs = bits(i^j)
    return bs[0] and bs[1]

def transpose(A):
    return [ [ A[i][j] for i in range(len(A)) ] for j in range(len(A[0])) ]

def bits(x):
    assert(x < 4)
    return [ x&1, x&2 ]

def matrix_mul(A, B):
    assert(len(A[0]) == len(B))
    Bt = transpose(B)
    out = []
    for i in range(len(A)):
        out.append([])
        for j in range(len(Bt)):
            z = reduce( Xor, [ And(x, y) for (x, y) in zip(A[i], Bt[j]) ])
            out[i].append(z)
    return out

def determinant(A):
    assert(len(A) == len(A[0]))
    zs = []
    for pi in itertools.permutations(range(len(A))):
        xs = [ A[i][ pi[i] ] for i in range(len(A)) ]
        zs.append( And( *xs ) )
    return reduce( Xor, zs )

def right_zeros(v, num_nonzero):
    return Not(Or(*v[num_nonzero:]))

def generate_constraints(n_constraints=4, arity=1, starting_at=3):
    n_fresh = n_constraints + starting_at
    cs = []
    for i in range(n_constraints):
        lhs = []
        for k in range(arity):
            q = [ FreshSymbol(BOOL) if j < starting_at else F for j in range(n_fresh) ]
            lhs.append(q)
        rhs = [ FreshSymbol(BOOL) if j == i + starting_at else F for j in range(n_fresh) ] 
        cs.append(( lhs, rhs ))
    return cs

def view(Gb, i, j):
    width  = len(Gb[0][0])
    alphas = bits(j)
    v = [] 
    for k in range(2):
        row = [ T if l == k or (l == 3 and alphas[k]) else F for l in range(width) ]
        v.append(row)
    v.append([ T if x == k else F for x in range(width) ])
    v.extend( Gb[i][:-1] ) # Gb[i] without its output row
    return v

def security(gb_view, Cs, B, reach, delta):
    Gbp = matrix_mul(gb_view, B)
    mat_constraint  = And(*[ right_zeros(row, reach) for row in Gbp ] )
    cons_constraint = T
    for C in Cs:
        lhs   = [ matrix_mul([q],B)[0] for q in C[0] ]
        [rhs] = matrix_mul([C[1]], B)
        p = And(*[ right_zeros(v, reach) for v in lhs ])
        q = right_zeros( rhs, reach )
        cons_constraint = And(cons_constraint, Implies(p, q))
    basis_constraint = Not( right_zeros( B[delta], reach ))
    return And(*[ mat_constraint, cons_constraint, basis_constraint ])

# checks that A is the identity matrix with optional zeroes to the right
def is_id_matrix(A):
    const = T
    for row in range( len(A) ):
        for col in range( len(A[row]) ):
            if row == col:
                const = And( const, A[row][col] )
            else:
                const = And( const, Not(A[row][col]) )
    return const

# multiply a constraint typle by a basis change
def mul_constraint(C, B):
    (lhs, rhs) = C
    lhsp = []
    for q in lhs:
        [qp] = matrix_mul([q], B)
        lhsp.append(qp)
    [rhsp] = matrix_mul([rhs], B)
    return (lhsp, rhsp)

def vec_eq(v, w):
    vp = copy.copy(v)
    wp = copy.copy(w)
    if len(v) < len(w):
        for i in range(len(w) - len(v)):
            vp.append(F)
    elif len(w) < len(v):
        for i in range(len(v) - len(w)):
            wp.append(F)
    assert(len(vp) == len(wp))
    cs = [ Not(Xor(x,y)) for (x,y) in zip(vp,wp) ]
    return And(*cs)

def constraint_eq(C, D):
    assert(len(C[0]) == len(D[0]))
    cs = [ vec_eq(C[0][i], D[0][i]) for i in range(len(C[0])) ]
    cs += [ vec_eq(C[1], D[1]) ]
    return And(*cs)

def correctness(Gb, Gb_C, B, Ev, Ev_C, delta, width, reach):
    const = T
    for i in range(4):
        for j in range(4):
            g = view(Gb, i, j)
            X = matrix_mul(g, B[i][j])
            view_ok = is_id_matrix(X)
            c = Xor(g[delta], g[-1]) if gate(i,j) else g[-1]
            [cp] = matrix_mul([c], B[i][j])
            ev_correct = vec_eq(cp, Ev[j])
            Gb_Cp = [ mul_constraint(c, B[i][j]) for c in Gb_C[i] ]
            # match each oracle query to one in the garbler
            one_oracle_call_the_same = Or( *map(lambda c: constraint_eq(c, Ev_C[j][0]), Gb_Cp))
            return And(*[view_ok, ev_correct, one_oracle_call_the_same])

def generate_gb(size=3, input_bits=2, output_bits=1, h_arity=1, h_calls_gb=4, h_calls_ev=1):
    width = input_bits + 1 + h_calls_gb
    reach = size + h_calls_ev - h_calls_gb - 1
    delta = input_bits + 1

    # variables
    gb = [ mat(size, width) for i in range(4) ]
    cs = [ generate_constraints(n_constraints=h_calls_gb, arity=h_arity) for i in range(4) ]
    bs = [ [ mat(width, width, {2:[F]*6+[T]}) for j in range(4) ] for i in range(4) ]
    rs = [ sum( mat(output_bits, size - 1 + h_calls_ev), []) for i in range(4) ]
    ec = [ generate_constraints(n_constraints=1, arity=h_arity) for i in range(4) ]

    # constraints
    bs_invertable = And(*[ And(*[ determinant(b) for b in bi ]) for bi in bs ])

    sec_constraints = T
    for i in range(4):
        for j in range(4):
            g = view(gb, i, j)
            s = security(g, cs[i], bs[i][j], reach, delta)
            sec_constraints = And(sec_constraints, s)

    correct = correctness(gb, cs, bs, rs, ec, delta, width, reach)

    # the formula
    return And(*[ bs_invertable, sec_constraints, correct ])

if __name__ == "__main__":
    generate_gb()
