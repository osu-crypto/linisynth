#/usr/bin/env python2

from pysmt.shortcuts import *
from pysmt.typing import BOOL
import string
import itertools
import copy

T = TRUE()
F = FALSE()

def gate(i, j):
    bs = bits(i^j)
    return bs[0] and bs[1] 

def bits(x):
    assert(x < 4)
    return [ x&1, x&2 ]

def right_zeros(v, num_nonzero):
    return Not(Or(*v[num_nonzero:]))

class smatrix (list):
    def __init__(self, nrows, ncols, premapping={}, initialize=True):
        self.nrows = nrows
        self.ncols = ncols
        for y in range(nrows):
            if initialize:
                if y in premapping:
                    assert( ncols == len(premapping[y]) )
                    self.append( premapping[y] )
                else:
                    self.append([ FreshSymbol(BOOL) for x in range(ncols) ])
            else:
                self.append([ None for x in range(ncols) ])

    def dims(self): return (self.nrows, self.ncols)

    def transpose(self):
        A_t = smatrix(self.ncols, self.nrows, initialize=False)
        for i in range(self.nrows):
            for j in range(self.ncols):
                A_t[j][i] = self[i][j]
        return A_t

    def mul(self, A):
        assert(self.ncols == A.nrows)
        A_t = A.transpose()
        C   = smatrix(self.nrows, A.ncols, initialize=False)
        for i in range(self.nrows):
            for j in range(A_t.nrows):
                z = reduce( Xor, [ And(x, y) for (x, y) in zip(self[i], A_t[j]) ])
                C[i][j] = z
        return C

    def det(self):
        assert(self.nrows == self.ncols)
        zs = []
        for pi in itertools.permutations(range(self.nrows)):
            xs = [ self[i][pi[i]] for i in range(self.nrows) ]
            zs.append( And( *xs ) )
        return reduce( Xor, zs )

    def reverse_mapping(self, model):
        out = []
        for i in range(self.nrows):
            out.append([])
            for j in range(self.ncols):
                if model.get_value(self[i][j]).is_true():
                    out[i].append( 1 )
                else:
                    out[i].append( 0 )
        return out

    def concat_rows(self, rows):
        assert(all(map(lambda r: len(r) == self.ncols, rows)))
        out   = smatrix(self.nrows + len(rows), self.ncols, initialize=False)
        elems = self + rows
        for i in range(out.nrows):
            out[i] = elems[i]
        return out

    # checks that self is the identity matrix with optional zeroes to the right
    def is_id_matrix(self):
        c = T
        for row in range( self.nrows ):
            for col in range( self.ncols ):
                if row == col:
                    c = And( c, self[row][col] )
                else:
                    c = And( c, Not( self[row][col] ))
        return c

    def eq(self, other):
        assert(self.nrows == other.nrows)
        self_  = copy.deepcopy(self)
        other_ = copy.deepcopy(other)
        if self.ncols < other.ncols:
            self_.ncols = other.ncols
            for i in range(self.nrows):
                for j in range(other.ncols - self.ncols):
                    self_[i].append(F)
        elif other.ncols < self.ncols:
            other_.ncols = self.ncols
            for i in range(other.nrows):
                for j in range(self.ncols - other.ncols):
                    other_[i].append(F)
        assert(self_.dims() == other_.dims())
        c = T
        for i in range(self_.nrows):
            for j in range(self_.ncols):
                p = Not(Xor( self_[i][j], other_[i][j] ))
                c = And(c,p)
        return c

class constraint:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "Constraint lhs={} rhs={}".format(self.lhs, self.rhs)

    def basis_change(self, B):
        lhs_ = self.lhs.mul(B)
        rhs_ = self.rhs.mul(B)
        return constraint(lhs_, rhs_)

    def reverse_mapping(self, model):
        lhs_ = self.lhs.reverse_mapping(model)
        rhs_ = self.rhs.reverse_mapping(model)
        return constraint(lhs_, rhs_)

    def eq(self, other):
        return And( self.lhs.eq(other.lhs), self.rhs.eq(other.rhs) )

def generate_constraints(n_constraints, arity, previous_fresh):
    n_fresh = n_constraints + previous_fresh
    cs = []
    for i in range(n_constraints):
        lhs = smatrix( arity, n_fresh, initialize=False )
        rhs = smatrix( 1,     n_fresh, initialize=False )
        for j in range( arity ):
            for k in range( n_fresh ): 
                if k < i + previous_fresh:
                    lhs[j][k] = FreshSymbol(BOOL)
                else:
                    lhs[j][k] = F
        for k in range( n_fresh ):
            if k == i + previous_fresh:
                rhs[0][k] = T
            else:
                rhs[0][k] = F
        cs.append( constraint( lhs, rhs ))
    return cs

def get_view(Gb, input_bits, i, j):
    width  = Gb[0].ncols
    size   = Gb[0].nrows
    alphas = bits(j)
    v = smatrix(input_bits, width, initialize=False)
    for row in range(input_bits):
        for col in range(width):
            if row == col or (col == input_bits and alphas[row]):
                v[row][col] = T
            else:
                v[row][col] = F
    return v.concat_rows( Gb[i][:-1] ) # Gb[i] without its output row

def security(view, Cs, B, reach, delta):
    mat_const = And(*[ right_zeros(row, reach) for row in view.mul(B) ] )
    con_const = T
    for C in Cs:
        C_ = C.basis_change(B)
        p  = And(*[ right_zeros(v, reach) for v in C_.lhs ])
        q  = And(*[ right_zeros(v, reach) for v in C_.rhs ])
        con_const = And( con_const, Implies(p, q) )
    basis_const = Not( right_zeros( B[delta], reach ))
    return And(*[ mat_const, con_const, basis_const ])

def correctness(Gb, Gb_C, B, Ev, Ev_C, delta, width, reach):
    const = T
    for i in range(4):
        for j in range(4):
            # the basis changed garbler view is the identity matrix
            view_ok = get_view(Gb,i,j).mul(B[i][j]).is_id_matrix()

            g  = Gb[i]
            C  = Xor(g[delta], g[-1]) if gate(i,j) else g[-1]
            C_ = C.mul(B[i][j])
            ev_correct = C_.eq(
            ev_correct = vec_eq(cp, Ev[j])

            # each evaluator oracle query equals one in the basis changed garble constraints
            Gb_Cp = [ c.basis_change(B[i][j]) for c in Gb_C[i] ]
            matched_oracles = T
            for ev_c in Ev_C[j]:
                c = Or( *map(lambda c: ev_c.eq(c), Gb_Cp))
                matched_oracles = And(matched_oracles, c)

            return And(*[ view_ok, ev_correct, matched_oracles ])

def generate_gb(size=3, input_bits=2, output_bits=1, h_arity=1, h_calls_gb=4, h_calls_ev=1):
    width = input_bits + 1 + h_calls_gb
    reach = size + h_calls_ev - h_calls_gb - 1
    delta = input_bits + 1

    ################################################################################
    ## variables

    # a garbling scheme for each i
    gb = []
    cs = []
    for i in range(4):
        gb.append( smatrix( size, width ))
        cs.append( generate_constraints( h_calls_gb, h_arity, input_bits+1 ))

    # a basis change for each (i,j)
    bs = []
    for i in range(4):
        bs.append([])
        for j in range(4):
            b = smatrix( width, width, { 2:[F]*(width-1)+[T] })
            bs[i].append(b)

    # an evaluation scheme for each j
    ev = []
    ec = []
    for j in range(4):
        ev.append( smatrix( output_bits, size-1 + h_calls_ev ))
        ec.append( generate_constraints( 1, h_arity, size-1 ))

    ################################################################################
    ## constraints

    bs_invertable = And(*[ And(*[ b.det() for b in bi ]) for bi in bs ])

    secure = T
    for i in range(4):
        for j in range(4):
            view   = get_view(gb, input_bits, i, j)
            s      = security(view, cs[i], bs[i][j], reach, delta)
            secure = And(secure, s)

    correct = correctness(gb, cs, bs, ev, ec, delta, width, reach)

    ################################################################################
    ## the formula

    return { 'formula': And(*[ bs_invertable, secure ])
           , 'bs'     : bs
           , 'gb'     : gb
           , 'cs'     : cs
           , 'ev'     : ev
           , 'ec'     : ec
           }





if __name__ == "__main__":
    generate_gb()



