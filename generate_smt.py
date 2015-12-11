#/usr/bin/env python2

from pysmt.shortcuts import *
from pysmt.typing import BOOL
import string
import itertools
import copy

T = TRUE()
F = FALSE()

def and_gate(i, j):
    bs = bits(i^j)
    return [bs[0] and bs[1]]

def xor_gate(i, j):
    bs = bits(i^j)
    return [bs[0] ^ bs[1]]

def bits(x):
    assert(x < 4)
    return [ (x&1) > 0, (x&2) > 0 ]

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
        assert(all(map(lambda r: len(r) <= self.ncols, rows)))
        rows_ = copy.copy(rows)
        out   = smatrix(self.nrows + len(rows), self.ncols, initialize=False)
        elems = self + rows_
        for i in range(out.nrows):
            while len(elems[i]) < self.ncols:
                elems[i].append( F )
            out[i] = elems[i]
        return out

    # adds zero cols as necessary
    def eq(self, other):
        assert(self.nrows == other.nrows)
        c = T
        for i in range(self.nrows):
            p = vec_eq(self[i], other[i])
            c = And(c,p)
        return c

    def with_rows(self, rows):
        out = smatrix( len(rows), self.ncols, initialize=False )
        for (i, row) in zip(range(len(rows)), rows):
            out[i] = copy.copy(self[row])
        return out

def id_matrix(nrows, ncols):
    I = smatrix(nrows, ncols)
    for row in range( nrows ):
        for col in range( ncols ):
            if row == col:
                I[row][col] = T
            else:
                I[row][col] = F
    return I

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
    alphas = bits(i ^ j)
    v = smatrix(input_bits, width, initialize=False)
    for row in range(input_bits):
        for col in range(width):
            if row == col or (col == input_bits and alphas[row]):
                v[row][col] = T
            else:
                v[row][col] = F
    return v.concat_rows( Gb[i][:-1] ) # Gb[i] without its output row

def security(Gb, Gb_C, B, params):
    secure = T
    for i in range(4):
        for j in range(4):
            view   = get_view(gb, params['input_bits'], i, j)
            s      = security(view, cs[i], bs[i][j], params['reach'], params['delta'])
            secure = And(secure, s)
    return secure

def right_zeros(v, num_nonzero):
    return Not(Or(*v[num_nonzero:]))

def security_(view, Cs, B, reach, delta):
    mat_const = And(*[ right_zeros(row, reach) for row in view.mul(B) ] )
    con_const = T
    for C in Cs:
        C_ = C.basis_change(B)
        p  = And(*[ right_zeros(v, reach) for v in C_.lhs ])
        q  = And(*[ right_zeros(v, reach) for v in C_.rhs ])
        con_const = And( con_const, Implies(p, q) )
    basis_const = Not( right_zeros( B[delta], reach ))
    return And(*[ mat_const, con_const, basis_const ])

def correctness(Gb, Gb_C, B, Ev, Ev_C, params):
    output_rows = range( params['size'], params['size'] + params['output_bits'] )
    const = T
    for i in range(4):
        for j in range(4):
            # concat the output wires to the view, check that the top part is id, bottom eq to ev
            view = get_view(Gb, params['input_bits'], i, j)
            outs = Gb[i].with_rows(output_rows)
            for z in range(params['output_bits']):
                if params['gate'](i,j)[z]:
                    outs[z][params['delta']] = Not( outs[z][params['delta']] )
            checkL = view.concat_rows(outs)
            checkL_ = checkL.mul(B[i][j])
            checkR = id_matrix(view.nrows, view.ncols).concat_rows(Ev[j])
            ev_correct = checkL_.eq(checkR)
            # each evaluator oracle query equals one in the basis changed garble constraints
            Gb_Cp = [ c.basis_change(B[i][j]) for c in Gb_C[i] ]
            matched_oracles = T
            for ev_c in Ev_C[j]:
                c = Or( *map(lambda c: ev_c.eq(c), Gb_Cp))
                matched_oracles = And(matched_oracles, c)
            c = And(*[ ev_correct, matched_oracles ])
            const = And(const, c)
    return const

def generate_gb(gate=and_gate, size=2, input_bits=2, output_bits=1, h_arity=1, h_calls_gb=4, h_calls_ev=1):
    width = input_bits + 1 + h_calls_gb
    reach = size + input_bits + h_calls_ev
    delta = input_bits
    params = { "size"        : size
             , "input_bits"  : input_bits
             , "output_bits" : output_bits
             , "h_arity"     : h_arity
             , "h_calls_gb"  : h_calls_gb
             , "h_calls_ev"  : h_calls_ev
             , "width"       : width
             , "reach"       : reach
             , "delta"       : delta
             , "gate"        : gate
             }
    ################################################################################
    ## variables
    # a garbling scheme for each i
    gb = []
    cs = []
    for i in range(4):
        gb.append( smatrix( size + output_bits, width ))
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
        ev.append( smatrix( output_bits, size + input_bits + h_calls_ev ))
        ec.append( generate_constraints( h_calls_ev, h_arity, size + input_bits ))
    ################################################################################
    ## constraints
    bs_invertable = And(*[ And(*[ b.det() for b in bi ]) for bi in bs ])
    secure        = security(gb, cs, bs, params)
    correct       = correctness(gb, cs, bs, ev, ec, params)
    ################################################################################
    ## the formula
    return { 'formula': And(*[ bs_invertable, secure, correct ])
           , 'params' : params
           , 'bs'     : bs
           , 'gb'     : gb
           , 'cs'     : cs
           , 'ev'     : ev
           , 'ec'     : ec
           }

def check(scheme):
    z3 = Solver('z3')
    z3.add_assertion(scheme['formula'])
    ok = z3.solve()
    if ok:
        m = z3.get_model()
        z3.exit()
        return m
    else:
        z3.exit()

def reverse_mapping( scheme, model ):
    scheme_ = {}
    scheme_['gb'] = []
    scheme_['ev'] = []
    scheme_['cs'] = []
    scheme_['ec'] = []
    scheme_['bs'] = []
    for i in range(4):
        scheme_['bs'].append([])
        for j in range(4):
            scheme_['bs'][i].append( scheme['bs'][i][j].reverse_mapping(model) )
        scheme_['gb'].append( scheme['gb'][i].reverse_mapping(model) )
        scheme_['ev'].append( scheme['ev'][i].reverse_mapping(model) )
        # try:
        scheme_['cs'].append([])
        for c in scheme['cs'][i]:
            scheme_['cs'][i].append( c.reverse_mapping(model) )
        scheme_['ec'].append([])
        for c in scheme['ec'][i]:
            scheme_['ec'][i].append( c.reverse_mapping(model) )
    return scheme_

if __name__ == "__main__":
    generate_gb()
