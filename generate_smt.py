#/usr/bin/env python2

from pysmt.shortcuts import *
from pysmt.typing import BOOL
import string
import itertools
import copy

T = TRUE()
F = FALSE()

################################################################################
## shortcuts

# works
def free_xor():
    return generate_gb(h_calls_gb=0, h_calls_ev=0, size=0, gate=xor_gate)

# works
def half_gate():
    return generate_gb(input_bits=2, h_calls_gb=4, h_calls_ev=2, size=2, gate=and_gate)

def and_fan_in_3():
    return generate_gb(input_bits=3, h_calls_gb=8, h_calls_ev=3, size=3, gate=and_gate_3)

################################################################################
## gates

def and_gate(i, j):
    bs = bits(i^j, 2)
    return [bs[0] and bs[1]]

def and_gate_3(i, j):
    bs = bits(i^j, 3)
    return [bs[0] and bs[1] and bs[2]]

def xor_gate(i, j):
    bs = bits(i^j, 2)
    return [bs[0] ^ bs[1]]

################################################################################
## stuff

def bits(x, size):
    return [ (x&(2**i)>0) for i in range(size) ]

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
        if not rows: return copy.deepcopy(self)
        ncols = max(*([self.ncols] + map(len, rows)))
        out   = smatrix(self.nrows + len(rows), ncols, initialize=False)
        elems = copy.deepcopy(self) + copy.deepcopy(rows)
        for i in range(out.nrows):
            while len(elems[i]) < ncols:
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
    alphas = bits(i ^ j, input_bits)
    v = smatrix(input_bits, width, initialize=False)
    for row in range(input_bits):
        for col in range(width):
            if row == col or (col == input_bits and alphas[row]):
                v[row][col] = T
            else:
                v[row][col] = F
    return v.concat_rows( Gb[i][:-1] ) # Gb[i] without its output row

def right_zeros(v, num_nonzero):
    return Not(Or(*v[num_nonzero:]))

def security(Gb, Gb_C, B, params):
    secure = T
    for i in range(2**params['input_bits']):
        for j in range(2**params['input_bits']):
            view   = get_view(Gb, params['input_bits'], i, j)
            s      = security_(view, Gb_C[i], B[i][j], params['reach'], params['delta'])
            secure = And(secure, s)
    return secure

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
    for i in range(2**params['input_bits']):
        for j in range(2**params['input_bits']):
            # concat the output wires to the view, check that the top part is id, bottom eq to ev
            view = get_view(Gb, params['input_bits'], i, j)
            outs = Gb[i].with_rows(output_rows)
            for z in range(params['output_bits']):
                if params['gate'](i,j)[z]:
                    outs[z][params['delta']] = Not( outs[z][params['delta']] )

            checkL = view.concat_rows(outs)
            checkL_ = checkL.mul(B[i][j])
            I = id_matrix(view.nrows, view.ncols)
            checkR = I.concat_rows(Ev[j])
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
    print "params =", params
    ################################################################################
    ## variables
    # a garbling scheme for each i
    gb = []
    cs = []
    for i in range(2**input_bits):
        gb.append( smatrix( size + output_bits, width ))
        cs.append( generate_constraints( h_calls_gb, h_arity, input_bits+1 ))
    # a basis change for each (i,j)
    bs = []
    bi = []
    for i in range(2**input_bits):
        bs.append([])
        bi.append([])
        for j in range(2**input_bits):
            b    = smatrix( width, width, { 2:[F]*(width-1)+[T] })
            view = get_view(gb, input_bits, i, j)
            b_   = view.concat_rows(smatrix(view.ncols - view.nrows, width))
            bs[i].append(b)
            bi[i].append(b_)
    # an evaluation scheme for each j
    ev = []
    ec = []
    for j in range(2**input_bits):
        ev.append( smatrix( output_bits, size + input_bits + h_calls_ev ))
        ec.append( generate_constraints( h_calls_ev, h_arity, size + input_bits ))
    ################################################################################
    ## constraints
    # bs_invertable = And(*[ And(*[ b.det() for b in bi ]) for bi in bs ])
    I = id_matrix( width, width )
    bs_invertable = T
    for i in range(2**input_bits):
        for j in range(2**input_bits):
            p = I.eq( bs[i][j].mul(bi[i][j]) )
            bs_invertable = And(bs_invertable, p)
    # bs_invertable = T
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
    scheme_['params'] = scheme['params']
    scheme_['gb'] = []
    scheme_['ev'] = []
    scheme_['cs'] = []
    scheme_['ec'] = []
    scheme_['bs'] = []
    for i in range(2**scheme['params']['input_bits']):
        scheme_['bs'].append([])
        for j in range(2**scheme['params']['input_bits']):
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

def print_mapping( scheme ):
    params = scheme['params']
    # name the fresh vars
    gb_names = []
    cur_inp = 'A'
    for i in range(params['input_bits']):
        gb_names.append(cur_inp)
        cur_inp = chr(ord(cur_inp)+1)
    gb_names.append('delta')
    cur_inp = 0
    for i in range(params['h_calls_gb']):
        gb_names.append('H' + str(cur_inp))
        cur_inp += 1

    print gb_names
    
    ev_names = []
    cur_inp = 'A'
    for i in range(params['input_bits']):
        ev_names.append(cur_inp)
        cur_inp = chr(ord(cur_inp)+1)
    cur_inp = 0
    for i in range(params['size']):
        ev_names.append('F' + str(cur_inp))
        cur_inp += 1
    cur_inp = 0
    for i in range(params['h_calls_ev']):
        ev_names.append('h' + str(cur_inp))
        cur_inp += 1

    print ev_names

if __name__ == "__main__":
    generate_gb()
