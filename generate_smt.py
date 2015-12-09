#/usr/bin/env python2

from pysmt.shortcuts import Not, Or, Xor, And, And, Xor, Int, FreshSymbol, Solver, Equals, Implies
from pysmt.typing import BOOL
import string
import itertools

TRUE  = FreshSymbol(BOOL)
FALSE = FreshSymbol(BOOL)

def mat(nrows, ncols): return [ [ FreshSymbol(BOOL) for x in range(ncols) ] for y in range(nrows) ]

def transpose(A):
    return [ [ A[i][j] for i in range(len(A)) ] for j in range(len(A[0])) ]

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

def right_zeroes(v, n=3):
    return Not(Or(*v[-n:]))

def generate_constraints(n_constraints=4, arity=1, starting_at=3):
    n_fresh = n_constraints + starting_at
    result = []
    for i in range(n_constraints):
        lhs = []
        for k in range(arity):
            q = []
            for j in range(n_fresh):
                if j < starting_at + i:
                    q.append( FreshSymbol(BOOL) )
                else:
                    q.append( FALSE )
            lhs.append(q)
        rhs = []
        for j in range(n_fresh):
            if j == i + starting_at:
                rhs.append( FreshSymbol(BOOL) )
            else:
                rhs.append( FALSE )
        result.append(( lhs, rhs ))
    return result

def security(gb_view, Cs, B, nzeroes, delta_row):
    Gbp = matrix_mul(gb_view, B)
    mat_constraint  = And(*[ right_zeroes(row, nzeroes) for row in Gbp ] )
    cons_constraint = TRUE
    for C in Cs:
        lhs   = [ matrix_mul([q],B)[0] for q in C[0] ]
        [rhs] = matrix_mul([C[1]], B)
        p = And(*[ right_zeroes(v, nzeroes) for v in lhs ])
        q = right_zeroes( rhs, nzeroes )
        cons_constraint = And(cons_constraint, Implies(p, q))
    basis_constraint = Not( right_zeroes( B[ delta_row ], nzeroes ))
    return And(*[ mat_constraint, cons_constraint, basis_constraint ])

def view(Gb, width):
    for alphas in itertools.product([False, True], [False, True]):
        output = [] 
        for k in range(2):
            row = []
            for l in range(width):
                if l == k or (l == 3 and alphas[k]):
                    row.append( TRUE )
                else:
                    row.append( FALSE )
            output.append(row)
        output.append([ TRUE if x == k else FALSE for x in range(width) ])
        output.extend( Gb[:-1] ) 
        yield output

def generate_gb(size=3, input_bits=2, output_bits=1, h_arity=1, h_calls_gb=4, h_calls_ev=1):
    # variables
    width = input_bits + 1 + h_calls_gb
    gb = [ mat(size, width) for i in range(4) ]
    cs = [ generate_constraints(n_constraints=h_calls_gb, arity=h_arity) for i in range(4) ]
    bs = [ [ mat(width, width) for i in range(4) ] for j in range(4) ]
    # constraints
    bs_invertable = And(*[ And(*[ determinant(b) for b in bi ]) for bi in bs ])
    nzeroes = h_calls_gb + 1 - size - h_calls_ev
    sec_constraints = TRUE
    for i in range(4):
        for g in view(gb[i], width):
            s = security( g, cs[i], bs[i][j], nzeroes, input_bits + 1 )
            sec_constraints = And(sec_constraints, s)
    return And(bs_invertable, sec_constraints)
