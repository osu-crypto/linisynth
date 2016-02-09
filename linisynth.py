#!/usr/bin/env python2

# imports
from pysmt.shortcuts import *
from pysmt.typing import BOOL, INT
import string
import itertools
import copy
import tqdm
import sys
import argparse
import time
import re
from warnings import warn

################################################################################
# shortcuts {{{
def shortcuts():
    d = {}
    d['privacy-free-and-gate'] = \
        { "gate"         : and_gate
        , "size"         : 1
        , "input_bits"   : 2
        , "output_bits"  : 1
        , "h_arity"      : 1
        , "h_calls_gb"   : 2
        , "h_calls_ev"   : 1
        , "privacy_free" : 1
        , "adaptive"     : 0
        }


    d['mux4in'] = \
        { "gate"        : mux2_gate
        , "size"        : 4
        , "input_bits"  : 5
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['mux4in-2'] = \
        { "gate"        : mux2_gate
        , "size"        : 4
        , "input_bits"  : 5
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 6
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        }

    d['size3-in3-out2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 3
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['size3-in3-out2-2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 3
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 6
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        }

    d['size3-in3-out2-3'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 3
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 8
        , "h_calls_ev"  : 6
        , "helper_bits" : 0
        }

    d['size3-in2-out2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['size3-in2-out2-2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 5
        , "h_calls_ev"  : 3
        , "helper_bits" : 0
        }

    d['size3-in2-out2-3'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 6
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        }

    d['any-size-3-in2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['any-size-3-in2-2'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 5
        , "h_calls_ev"  : 3
        , "helper_bits" : 0
        }

    d['any-size-3-in2-3'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 2
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['any-size-3-in2-4'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 2
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 1
        , "helper_bits" : 0
        }

    d['any-size-3-in3'] = \
        { "gate"        : None
        , "size"        : 3
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['1-out-of-2-mux'] = \
        { "gate"        : mux_gate
        , "size"        : 2
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['mux2'] = \
        { "gate"        : mux_gate
        , "size"        : 2
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        , "adaptive"    : 0
        }

    d['privacy-free-mux'] = \
        { "gate"        : mux_gate
        , "size"        : 1
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 2
        , "h_calls_ev"  : 1
        , "helper_bits" : 0
        , "adaptive"    : 0
        , "privacy_free" : True
        }

    d['privacy-free-mux2'] = \
        { "gate"        : mux2_gate
        , "size"        : 2
        , "input_bits"  : 5
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 6
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        , "adaptive"    : 1
        , "privacy_free" : True
        }

    d['2-bit-leq'] = \
        { "gate"        : leq_gate
        , "size"        : 1
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 2
        , "h_calls_ev"  : 1
        , "helper_bits" : 0
        }

    d['leq2'] = \
        { "gate"        : leq_gate
        , "size"        : 2
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['2-bit-eq'] = \
        { "gate"        : eq_gate
        , "size"        : 2
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['eq3'] = \
        { "gate"        : eq3_gate
        , "size"        : 2
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['2-bit-eq-small'] = \
        { "gate"        : eq_gate
        , "size"        : 1
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['eq-smaller2'] = \
        { "gate"        : eq_gate
        , "size"        : 2
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 3
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['privacy-free-lt'] = \
        { "gate"         : lt_gate
        , "size"         : 1
        , "input_bits"   : 2
        , "output_bits"  : 1
        , "h_arity"      : 1
        , "h_calls_gb"   : 2
        , "h_calls_ev"   : 1
        , "helper_bits"  : 0
        , "adaptive"     : 0
        , "privacy_free" : 1
        }

    d['2-bit-lt'] = \
        { "gate"        : lt2_gate
        , "size"        : 2
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['lt2'] = \
        { "gate"        : lt2_gate
        , "size"        : 3
        , "input_bits"  : 4
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 8
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        }

    d['free-xor'] = \
        { "gate"        : xor_gate
        , "size"        : 0
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 0
        , "h_calls_ev"  : 0
        }

    d['nested-xor'] = \
        { "gate"        : nested_xor_gate
        , "size"        : 0
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 0
        , "h_calls_ev"  : 0
        , "helper_bits" : 0
        }

    d['and-xor'] = \
        { "gate"        : andxor_gate
        , "size"        : 2
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        }

    d['cheaper-and'] = \
        { "gate"        : and_gate
        , "size"        : 3
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 2
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 1
        }

    d['half-gate-h2'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 2
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 1
        , "adaptive"    : 0
        }

    d['cheaper-and2'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 2
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 1
        }

    d['half-gate'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "adaptive"    : 0
        }

    d['half-gate-adaptive'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "adaptive"    : 1
        }

    d['half-gate-cheaper'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 1
        }

    d['one-third-gate'] = \
        { "gate"        : and_gate
        , "size"        : 1
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 1
        }

    d['one-third-gate-big'] = \
        { "gate"        : and_gate
        , "size"        : 2
        , "input_bits"  : 2
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 1
        }

    d['and3'] = \
        { "gate"        : and3_gate
        , "size"        : 4
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 8
        , "h_calls_ev"  : 4
        , "helper_bits" : 1
        , "helper_gate" : and3_helper_gate
        }

    d['and3-smaller'] = \
        { "gate"        : and3_gate
        , "size"        : 3
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 8
        , "h_calls_ev"  : 4
        , "helper_bits" : 1
        , "helper_gate" : and3_helper_gate
        }

    d['and3-nohelper'] = \
        { "gate"        : and3_gate
        , "size"        : 4
        , "input_bits"  : 3
        , "output_bits" : 1
        , "h_arity"     : 1
        , "h_calls_gb"  : 8
        , "h_calls_ev"  : 4
        , "helper_bits" : 0
        }

    d['adder-nohelper'] = \
        { "gate"        : adder_gate
        , "size"        : 2
        , "input_bits"  : 3
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 0
        }

    d['adder'] = \
        { "gate"        : adder_gate
        , "size"        : 2
        , "input_bits"  : 3
        , "output_bits" : 2
        , "h_arity"     : 1
        , "h_calls_gb"  : 4
        , "h_calls_ev"  : 2
        , "helper_bits" : 1
        }
    return d
# }}}
# helper functions and constants# {{{

T = TRUE()
F = FALSE()

def mapall(f, stuff):
    return reduce(lambda z, x: And(z, f(x)), stuff, T)

def mapsome(f, stuff):
    return reduce(lambda z, x: Or(z, f(x)), stuff, F)

def bits(x, size):
    return [ (x&(2**i)>0) for i in range(size) ]
# }}}
# gates {{{

def all_gates(nins, nouts):
    truth_tables = []
    for i in range(nouts):
        tt = list(itertools.product(*[[True,False]]*(2**nins)))
        truth_tables.append(tt)
    indices = itertools.product(*[range(len(truth_tables[0]))]*nouts) 
    for assn in indices:
        def gate(inp, assn=assn):
            outputs = []
            for (out, ix) in enumerate(assn):
                outputs.append(truth_tables[out][ix][inp])
            return outputs
        yield gate

def mux2_gate(x):
    [x0, x1, y0, y1, c] = bits(x,5)
    return [y0, y1] if c else [x0, x1]

def mux_gate(x):
    [x0, x1, c] = bits(x,3)
    return [x1 if c else x0]

def eq_gate(i):
    x = (i) & 0b11
    y = (i & 0b1100) >> 2
    return [x == y]

def eq3_gate(i):
    x = (i) & 0b111
    y = (i & 0b111000) >> 3
    return [x == y]

def lt_gate(i):
    [x,y] = bits(i,2)
    return [x < y]

def lt2_gate(i):
    x = i & 0b11
    y = (i & 0b1100) >> 2
    return [x < y]

def leq_gate(i):
    x = (i) & 0b11
    y = (i & 0b1100) >> 2
    return [x <= y]

def and_gate(i):
    [x,y] = bits(i, 2)
    return [x and y]

def and3_gate(i):
    [x,y,z] = bits(i,3)
    return [x and y and z]

def xor_gate(i):
    [x,y] = bits(i, 2)
    return [x ^ y]

def andxor_gate(i):
    [x,y,z] = bits(i, 3)
    return [(x & y) ^ z]

def nested_xor_gate(i):
    [x,y,z] = bits(i, 3)
    return [x^y^z]

def adder_gate(i):
    [x, y, cin] = bits(i, 3)
    z = x ^ y ^ cin
    cout = (x & y) | (z & cin)
    return [z, cout]
# }}}
# helper gates {{{

def and3_helper_gate(i, j, z_gb):
    [a0,a1,a2] = bits(i^j, 3)
    return (a0 & a1) ^ z_gb

# }}}
# symbolic matrix class {{{

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
        return mapall(lambda t: vec_eq(t[0], t[1]), zip(self, other))

    def with_rows(self, rows):
        out = smatrix( len(rows), self.ncols, initialize=False )
        for (i, row) in zip(range(len(rows)), rows):
            out[i] = copy.copy(self[row])
        return out

    def max_hamming_weight(self, n):
        return mapall(lambda row: hamming_weight_leq(row, n), self)

    def get_variables(self):
        return sum(self, [])
# }}}
# vector ops {{{
def hamming_weight_leq(vec, n):
    ints = [ FreshSymbol(INT) for x in vec ]
    p = T
    total = Int(0)
    for (x, y) in zip(vec, ints):
        q = Ite(x, Equals(y, Int(1)), Equals(y, Int(0)))
        p = And(p,q)
        total = Plus(total, y)
    q = LE(total, Int(n))
    p = And(p, q)
    return p

def id_matrix(nrows, ncols):
    I = smatrix(nrows, ncols)
    for row in range( nrows ):
        for col in range( ncols ):
            if row == col:
                I[row][col] = T
            else:
                I[row][col] = F
    return I

def vec_leq(v,w):
    assert(len(v) == len(w))
    if len(v) == 1: return And(Not(v[0]), w[0])
    return Or(And(Not(v[-1]), w[-1]), And(Not(Xor(v[-1], w[-1])), vec_leq(v[:-1], w[:-1])))

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

def right_zeros(v, num_nonzero):
    return Not(Or(*v[num_nonzero:]))

# }}}
# oracle constraint class {{{

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

    def get_variables(self):
        return self.lhs.get_variables() + self.rhs.get_variables()
# }}}
################################################################################
## formula generation
def generate_constraints(n_constraints, arity, previous_fresh, adaptive=True):# {{{
    n_fresh = n_constraints + previous_fresh
    cs = []
    for i in range(n_constraints):
        lhs = smatrix( arity, n_fresh, initialize=False )
        rhs = smatrix( 1,     n_fresh, initialize=False )
        for j in range( arity ):
            for k in range( n_fresh ): 
                if k < previous_fresh:
                    lhs[j][k] = FreshSymbol(BOOL)
                elif adaptive and previous_fresh <= k < i + previous_fresh:
                    lhs[j][k] = FreshSymbol(BOOL)
                else:
                    lhs[j][k] = F
        for k in range( n_fresh ):
            if k == i + previous_fresh:
                rhs[0][k] = T
            else:
                rhs[0][k] = F
        cs.append( constraint( lhs, rhs ))
    # ensure lexocographic ordering
    lex = T
    for i in range(n_constraints - 1):
        v = sum(cs[i].lhs, [])
        w = sum(cs[i+1].lhs, [])
        p = vec_leq(v,w)
        lex = And(lex,p)
    return (cs, lex)
# }}}
def get_view(Gb, params, i, j, z):# {{{
    width  = Gb[0][0].ncols
    size   = Gb[0][0].nrows
    alphas = bits(i ^ j, params['input_bits'])
    v = smatrix(params['input_bits'], width, initialize=False)
    for row in range(params['input_bits']):
        for col in range(width):
            if row == col or (col == params['delta'] and alphas[row]):
                v[row][col] = T
            else:
                v[row][col] = F
    return v.concat_rows( Gb[i][z][:-params['output_bits']] ) # Gb[i] without its output row
# }}}
def security(Gb, Gb_C, B, params):# {{{
    secure = T
    with tqdm.tqdm(total=2**(params['color_bits']+params['input_bits']+params['helper_bits']), desc="security") as pbar:
        for i in range(2**params['color_bits']):
            for j in range(2**params['input_bits']):
                for z in range(2**params['helper_bits']):
                    view   = get_view(Gb, params, i, j, z)
                    s      = security_(view, Gb_C[i][z], B[i][j][z], params['reach'], params['delta'])
                    secure = And(secure, s)
                    pbar.update(1)
    return secure
# }}}
def security_(view, Cs, B, reach, delta):# {{{
    mat_const = And(*[ right_zeros(row, reach) for row in view.mul(B) ] )
    con_const = T
    for C in Cs:
        C_ = C.basis_change(B)
        p  = And(*[ right_zeros(v, reach) for v in C_.lhs ])
        q  = And(*[ right_zeros(v, reach) for v in C_.rhs ])
        con_const = And( con_const, Implies(p, q) )
    basis_const = Not( right_zeros( B[delta], reach ))
    return And(*[ mat_const, con_const, basis_const ])
# }}}
def helper_bit_permuted( m ):# {{{
    p = And(m[0][0], m[1][1])
    q = And(m[0][1], m[1][0])
    return (Or(p,q), q)
# }}}
def correctness(Gb, Gb_C, B, Ev, Ev_C, params):# {{{
    accum = T
    zijs  = {}
    with tqdm.tqdm(total=2**(params['input_bits']+params['color_bits']), desc="correctness") as pbar:
        for i in range(2**params['color_bits']):
            for j in range(2**params['input_bits']):
                z_assns = []
                for z_gb in range(2**params['helper_bits']):
                    if 'helper_gate' in params:
                        z_ev = params['helper_gate'](i,j,z_gb)
                        p = correctness_(Gb, Gb_C, B, Ev, Ev_C, i, j, z_gb, z_ev, params)
                        z_assns.append([F,T] if z_ev else [T,F])
                    else:
                        qs = []
                        for z_ev in range(2**params['helper_bits']):
                            q = correctness_(Gb, Gb_C, B, Ev, Ev_C, i, j, z_gb, z_ev, params)
                            qs.append(q)
                        z_assns.append(qs)
                        p = Or(*qs)
                    accum = And(accum, p)
                if params['helper_bits'] == 1: # TODO expand to general case
                    (q,zij) = helper_bit_permuted(z_assns)
                    accum = And(accum, q)
                    zijs[(i,j)] = zij
                pbar.update(1)
    return (accum, zijs)

# }}}
def correctness_(Gb, Gb_C, B, Ev, Ev_C, i, j, z_gb, z_ev, params):# {{{
    # concat the output wires to the view, check that the top part is id, bottom eq to ev
    view = get_view(Gb, params, i, j, z_gb)
    outs = Gb[i][z_gb].with_rows(params['output_rows'])
    for k in range(params['output_bits']):
        if params['gate'](i^j)[k]:
            outs[k][params['delta']] = Not( outs[k][params['delta']] )
    checkL = view.concat_rows(outs).mul(B[i][j][z_gb])
    checkR = id_matrix(view.nrows, view.ncols).concat_rows(Ev[j][z_ev])
    ev_correct = checkL.eq(checkR)
    # ev_correct = outs.mul(B[i][j][z_gb]).eq(Ev[j][z_ev])

    # each evaluator oracle query equals one in the basis changed garble constraints
    Gb_C_ = [ c.basis_change(B[i][j][z_gb]) for c in Gb_C[i][z_gb] ]
    matched_oracles = T
    for ev_c in Ev_C[j][z_ev]:
        c = Or( *map(lambda d: ev_c.eq(d), Gb_C_))
        matched_oracles = And(matched_oracles, c)

    return And(ev_correct, matched_oracles)
# }}}
def generate_gb(params, check_security=True, check_correct=True, check_inv=True):# {{{
    input_bits  = params['input_bits']
    output_bits = params['output_bits']
    h_arity     = params['h_arity']
    h_calls_gb  = params['h_calls_gb']
    h_calls_ev  = params['h_calls_ev']
    gate        = params['gate']
    size        = params['size']
    reach       = params['reach']       = size + input_bits + h_calls_ev
    gb_width    = params['gb_width']    = input_bits + 1 + h_calls_gb
    ev_width    = params['ev_width']    = size + input_bits + h_calls_ev
    delta       = params['delta']       = input_bits
    if not 'adaptive' in params:
        params['adaptive'] = 1
    adaptive = params['adaptive']
    if not 'helper_bits' in params:
        params['helper_bits'] = 0
    if not 'privacy_free' in params:
        params['privacy_free'] = False
    helper_bits = params['helper_bits']
    params['output_rows'] = range( size, size + output_bits )
    if params['privacy_free']:
        color_bits = params['color_bits'] = 0
    else:
        color_bits = params['color_bits'] = input_bits
    # print "params =", params
    ################################################################################
    ## variables
    # a garbling scheme for each i
    gb = []
    cs = []
    lex_gb = T
    with tqdm.tqdm(total=2**(color_bits+helper_bits), desc="gb") as pbar:
        for i in range(2**color_bits):
            gb.append([])
            cs.append([])
            for z in range(2**helper_bits):
                g = smatrix( size + output_bits, gb_width )
                (c,lex) = generate_constraints( h_calls_gb, h_arity, input_bits+1, adaptive)
                lex_gb = And(lex_gb, lex)
                gb[i].append(g)
                cs[i].append(c)
                pbar.update(1)
    # a basis change for each (i,j)
    bs = []
    bi = []
    with tqdm.tqdm(total=2**(color_bits+helper_bits+input_bits), desc="bs") as pbar:
        for i in range(2**color_bits):
            bs.append([])
            bi.append([])
            for j in range(2**input_bits):
                bs[i].append([])
                bi[i].append([])
                for z in range(2**helper_bits):
                    b    = smatrix( gb_width, gb_width, { delta:[F]*(gb_width-1)+[T] })
                    view = get_view(gb, params, i, j, z)
                    b_   = view.concat_rows(smatrix(view.ncols - view.nrows, gb_width))
                    bs[i][j].append(b)
                    bi[i][j].append(b_)
                    pbar.update(1)
    # an evaluation scheme for each j
    ev = []
    ec = []
    lex_ev = T
    with tqdm.tqdm(total=2**(input_bits+helper_bits), desc="ev") as pbar:
        for j in range(2**input_bits):
            ev.append([])
            ec.append([])
            for z in range(2**helper_bits):
                e = smatrix( output_bits, ev_width )
                (c, lex) = generate_constraints( h_calls_ev, h_arity, size + input_bits )
                lex_ev = And(lex_ev, lex)
                ev[j].append(e)
                ec[j].append(c)
                pbar.update(1)
    ################################################################################
    ## constraints
    # bs_invertable = And(*[ And(*[ b.det() for b in bi ]) for bi in bs ])
    bs_invertable = T
    if check_inv:
        I = id_matrix( gb_width, gb_width )
        with tqdm.tqdm(total=2**(color_bits+input_bits+helper_bits), desc="inv") as pbar:
            for i in range(2**color_bits):
                for j in range(2**input_bits):
                    for z in range(2**helper_bits):
                        p = I.eq( bs[i][j][z].mul(bi[i][j][z]) )
                        bs_invertable = And(bs_invertable, p)
                        pbar.update(1)
    
    if check_security:
        secure = security(gb, cs, bs, params)
    else: 
        secure = T

    if check_correct:
        (correct, zijs) = correctness(gb, cs, bs, ev, ec, params)
    else:
        correct = T
        zijs = {}

    ham_gb = T
    if 'hamming_weight_gb' in params:
        print "max hamming weight (gb):", params['hamming_weight_gb']
        ham_gb = mapall(lambda outer: \
            mapall(lambda e: e.max_hamming_weight(params['hamming_weight_gb']), outer), gb)
    ham_ev = T
    if 'hamming_weight_ev' in params:
        print "max hamming weight (ev):", params['hamming_weight_ev']
        ham_ev = mapall(lambda outer: \
            mapall(lambda e: e.max_hamming_weight(params['hamming_weight_ev']), outer), ev)
    lex = And(lex_gb, lex_ev)
    ################################################################################
    ## the formula
    return { 'formula' : And(*[ bs_invertable, secure, correct, ham_gb, ham_ev, lex ])
           , 'params'  : params
           , 'bs'      : bs
           , 'gb'      : gb
           , 'cs'      : cs
           , 'ev'      : ev
           , 'ec'      : ec
           , 'zijs'    : zijs
           }
# }}}
################################################################################
## solver
def check_scheme(scheme, solver='z3'):# {{{
    s = Solver(name=solver)
    s.add_assertion(scheme['formula'])
    ok = s.solve()
    if ok:
        m = s.get_model()
        s.exit()
        return m
    else:
        s.exit()
# }}}
def get_assignment_func(scheme):# {{{
    variables = []
    for i in range(2**scheme['params']['input_bits']):
        for z in range(2**scheme['params']['helper_bits']):
            variables.extend(scheme['gb'][i][z].get_variables())
            variables.extend(scheme['ev'][i][z].get_variables())
            for c in scheme['cs'][i][z]:
                variables.extend(c.get_variables())
            for c in scheme['ec'][i][z]:
                variables.extend(c.get_variables())
    variables = filter(lambda x: not x.is_true() and not x.is_false(), variables)
    def assignment_func(model):
        ret = [ Not(Xor(x, model.get_value(x))) for x in variables ]
        return And(*ret)
    return assignment_func
# }}}
def enumerate_scheme(scheme, solver='z3', verbose=False, pretty=False, limit=999999):# {{{
    assignment = get_assignment_func(scheme)
    i = 0
    s = Solver(name=solver)
    if verbose:
        enumerate_start = start = time.time()
    s.add_assertion(scheme['formula'])
    ok = s.solve()
    if not ok:
        print "unsat"
        sys.exit(1)
    while ok and (i < int(limit) if limit else True):
        if verbose:
            print "smt took {0:.2f}s".format(time.time() - start)
            start = time.time()
        print "enumerate: {}".format(i)
        i += 1
        m = s.get_model()
        print_model(scheme, m, pretty)
        p = assignment(m)
        s.add_assertion(Not(p))
        ok = s.solve()
    if verbose:
        print "enumeration took {:.2f}s".format(time.time() - enumerate_start)
    s.exit()
    sys.exit(0)
# }}}
def reverse_mapping( scheme, model ):# {{{
    scheme_ = {}
    scheme_['params'] = scheme['params']
    scheme_['gb'] = []
    scheme_['ev'] = []
    scheme_['cs'] = []
    scheme_['ec'] = []
    scheme_['bs'] = []
    scheme_['zijs'] = {}

    # find out values of zijs
    if scheme['params']['helper_bits']:
        for k in scheme['zijs']:
            v = scheme['zijs'][k]
            scheme_['zijs'][k] = 1 if model.get_value(v).is_true() else 0

    for i in range(2**scheme['params']['color_bits']):
        scheme_['bs'].append([])
        for j in range(2**scheme['params']['input_bits']):
            scheme_['bs'][i].append([])
            for z in range(2**scheme['params']['helper_bits']):
                scheme_['bs'][i][j].append( scheme['bs'][i][j][z].reverse_mapping(model) )

    for i in range(2**scheme['params']['color_bits']):
        scheme_['gb'].append([])
        scheme_['cs'].append([])
        for z in range(2**scheme['params']['helper_bits']):
            scheme_['gb'][i].append( scheme['gb'][i][z].reverse_mapping(model) )
            scheme_['cs'][i].append( [] )
            for c in scheme['cs'][i][z]:
                scheme_['cs'][i][z].append( c.reverse_mapping(model) )

    for j in range(2**scheme['params']['input_bits']):
        scheme_['ev'].append([])
        scheme_['ec'].append([])
        for z in range(2**scheme['params']['helper_bits']):
            scheme_['ev'][j].append( scheme['ev'][j][z].reverse_mapping(model) )
            scheme_['ec'][j].append( [] )
            for c in scheme['ec'][j][z]:
                scheme_['ec'][j][z].append( c.reverse_mapping(model) )

    return scheme_
# }}}
def mapping_to_str( scheme ):# {{{
    s = ""
    params = scheme['params']
    def args_str(row, names):
        args = []
        for col in range(len(row)):
            if row[col]: 
                args.append(names[col])
        return " + ".join(args)

    # print values of zijs
    if scheme['params']['helper_bits']:
        for i in range(len(scheme['gb'])):
            for j in range(len(scheme['ev'])):
                s += "i={} j={} z={}\n".format(i,j, scheme['zijs'][(i,j)])

    for i in range(len(scheme['gb'])):
        for z in range(len(scheme['gb'][i])):
            s += "---i={},z={}---\n".format(i,z)
            s += "Gb:\n"
            gb = scheme['gb'][i][z]
            cs = scheme['cs'][i][z]
            gb_names = []
            cur_inp = 'A'
            for row in range(params['input_bits']):
                gb_names.append(cur_inp)
                cur_inp = chr(ord(cur_inp)+1)
            gb_names.append('delta')
            cur_inp = 0
            for row in range(params['h_calls_gb']):
                args = map(lambda a: args_str(a, gb_names), cs[row].lhs)
                var = "H({})".format(", ".join(args))
                gb_names.append(var)
            for row in range(len(gb)):
                if row < params['size']:
                    name = 'F' + str(row)
                else:
                    name = 'C' + str(row - params['size'])
                s += "\t{} = {}\n".format( name, args_str(gb[row], gb_names) )

    for j in range(len(scheme['ev'])):
        for z in range(len(scheme['ev'][j])):
            s += "---j={},z={}---\n".format(j,z)
            s += "Ev:\n"
            ev = scheme['ev'][j][z]
            ec = scheme['ec'][j][z]
            ev_names = []
            cur_inp = 'A'
            for row in range(params['input_bits']):
                ev_names.append(cur_inp + "'")
                cur_inp = chr(ord(cur_inp)+1)
            cur_inp = 0
            for row in range(params['size']):
                ev_names.append('F' + str(cur_inp))
                cur_inp += 1
            cur_inp = 0
            for row in range(params['h_calls_ev']):
                args = map(lambda a: args_str(a, ev_names), ec[row].lhs)
                var = "H({})".format(", ".join(args))
                ev_names.append(var)
            for row in range(len(ev)):
                name = 'C' + str(row)
                s += "\t{} = {}\n".format( name, args_str(ev[row], ev_names) )
    return s
# }}}
def mapping_to_pretty_str( scheme ):# {{{
    s = ""
    params = scheme['params']
    def args_str(row, names):
        args = []
        for col in range(len(row)):
            if row[col]: 
                args.append(names[col])
        return " + ".join(args)

    # print values of zijs
    if scheme['params']['helper_bits']:
        for i in range(len(scheme['gb'])):
            for j in range(len(scheme['ev'])):
                s += "i={} j={} z={}\n".format(i,j, scheme['zijs'][(i,j)])

    # returns a list of hashes, where each line corresponds to F0, F1, C, or Ev0
    # each hash is a mapping of each argument and which combinations of i/j,z call it
    def make_nonlinear(scheme, is_ev, adaptive):
        h_calls = scheme['params']['h_calls_ev' if is_ev else 'h_calls_gb']
        size    = scheme['params']['output_bits'] if is_ev else scheme['params']['size']+1
        ms      = scheme['ev' if is_ev else 'gb']
        cs      = scheme['ec' if is_ev else 'cs']
        fresh_names = {} # { (i,z) : [ fresh_names ] }

        h_strs     = {} # { "h1" : "H(A + B)" }
        h_strs_rev = {} # { "H(A + B)" : "h1" }
        h_ctr      = 0

        for i in range(len(ms)):
            for z in range(len(ms[i])):
                fresh_names[(i,z)] = []
                # add names for garbled inputs, delta, and ciphertexts
                cur_inp = 'A'
                for row in range(params['input_bits']):
                    if is_ev:
                        fresh_names[(i,z)].append(cur_inp + "'")
                    else:
                        fresh_names[(i,z)].append(cur_inp)
                    cur_inp = chr(ord(cur_inp)+1)
                if is_ev:
                    # add F0, F1, etc
                    cur_inp = 0
                    for row in range(params['size']):
                        fresh_names[(i,z)].append('F' + str(cur_inp))
                        cur_inp += 1
                else:
                    # add delta
                    fresh_names[(i,z)].append('delta')
                # add names for the oracle queries
                for row in range(h_calls):
                    args = map(lambda a: args_str(a, fresh_names[(i,z)]), cs[i][z][row].lhs)
                    if adaptive:
                        h_str = "H({})".format(", ".join(args))
                        if h_str in h_strs_rev:
                            var = h_strs_rev[h_str]
                        else:
                            var = "h" + str(h_ctr)
                            h_ctr += 1
                            h_strs[var] = h_str
                            h_strs_rev[h_str] = var
                    else: 
                        var = "H({})".format(", ".join(args))
                    fresh_names[(i,z)].append(var)
        # loop through each line of the Gb/Ev and figure out which
        # fresh vars are shared across i/j,z combinations 
        mapping = []
        for row in range(size):
            args = {} # { name: [(i,z)] }
            for i in range(2**(params['input_bits'] if is_ev else params['color_bits'])):
                for z in range(2**params['helper_bits']):
                    m = ms[i][z]
                    for fresh, fresh_is_set in enumerate(m[row]):
                        if fresh_is_set:
                            name = fresh_names[(i,z)][fresh]
                            if not name in args:
                                args[name] = set()
                            if params['helper_bits']:
                                args[name].add((i,z))
                            else:
                                args[name].add((i))
            mapping.append(args)
        return (mapping, h_strs)

    if params['helper_bits']:
        all_gb_combinations = \
            set(itertools.product(range(2**params['color_bits']), range(2**params['helper_bits'])))
    else:
        all_gb_combinations = set(range(2**params['color_bits']))

    (gb, h_calls) = make_nonlinear(scheme, False, params['adaptive'])
    s += "Gb:\n"
    if params['adaptive']:
        for h_var in sorted(h_calls.keys()):
            s += "\t{} = {}\n".format(h_var, h_calls[h_var])
    for i, row in enumerate(gb):
        if i < params['size']:
            name = 'F' + str(i)
        else:
            name = 'C' + str(i - params['size'])
        s += "\t{} = ".format(name)
        args = []
        for argname in sorted(row.keys()):
            izs = row[argname]
            if izs == all_gb_combinations:
                args.append(argname)
            else:
                izs_str = "[" + ",".join(map(str,izs)) + "]"
                args.append(izs_str + argname)
        s += " + ".join(args) + "\n"

    if params['helper_bits']:
        all_ev_combinations = \
            set(itertools.product(range(2**params['input_bits']), range(2**params['helper_bits'])))
    else:
        all_ev_combinations = set(range(2**params['input_bits']))

    (ev, h_calls) = make_nonlinear(scheme, True, params['adaptive'])
    s += "Ev:\n"
    if params['adaptive']:
        for h_var in sorted(h_calls.keys()):
            s += "\t{} = {}\n".format(h_var, h_calls[h_var])
    for i, row in enumerate(ev):
        name = 'C' + str(i)
        s += "\t{} = ".format(name)
        args = []
        for argname in sorted(row.keys()):
            izs = row[argname]
            if izs == all_ev_combinations:
                args.append(argname)
            else:
                izs_str = "[" + ",".join(map(str,izs)) + "]"
                args.append(izs_str + argname)
        s += " + ".join(args) + "\n"

    return s
# }}}
def print_model( scheme, model, pretty=False ):# {{{
    s = reverse_mapping(scheme, model)
    if pretty:
        print mapping_to_pretty_str(s),
    else:
        print mapping_to_str(s),
# }}}
################################################################################
## command line interface
def gate_to_str(gate, input_bits, output_bits):# {{{
    outs = ["gate in={} out={} tt=[ ".format(input_bits, output_bits)]
    for i in range(2**(input_bits)):
        outs.append( "".join(["1" if b else "0" for b in gate(i) ]))
        outs.append( " " )
    outs.append(']')
    return ''.join(outs)
# }}}
def gate_from_str(s):# {{{
    m = re.match('gate in=(\d+) out=(\d+) tt=\[ ([01 ]+) \]', s)
    if not m:
        warn('invalid gate provided')
        sys.exit(1)
    input_bits  = int(m.group(1))
    output_bits = int(m.group(2))
    def to_bool(int_str):
        return int(int_str) > 0
    tt = m.group(3).split(' ')
    tt = map(lambda s: map(to_bool, list(s)), tt)
    def gate(x, tt=tt):
        return tt[x]
    return gate, input_bits, output_bits
# }}}
def print_truth_table(gate, input_bits, output_bits):# {{{
    print gate_to_str(gate, input_bits, output_bits)
# }}}
def get_args():# {{{
    parser = argparse.ArgumentParser()
    parser.add_argument('shortcut', nargs='?', help='which shortcut to use')
    parser.add_argument('-L', '--list', action='store_true', help='list shortcuts and parameters')
    parser.add_argument('-l', '--shortlist', action='store_true', help='list shortcut names only')
    parser.add_argument('-C', '--nocorrect', action='store_true', help='skip correctness check')
    parser.add_argument('-S', '--nosecure', action='store_true', help='skip security check')
    parser.add_argument('-I', '--noinv', action='store_true', help='skip invertibility check')
    parser.add_argument('-s', '--solver', default='z3', help='which solver to use')
    parser.add_argument('--nocheck', action='store_true', help='skip checking altoether')
    parser.add_argument('--csv', action='store_true', help='show formula info as csv')
    parser.add_argument('--csvheader', action='store_true', help='show csv column names')
    parser.add_argument('-v', '--verbose', action='count', help='show timing information')
    parser.add_argument('-e', '--enumerate', action='store_true', help='enumerate solutions')
    parser.add_argument('-E', '--limitedenumerate', help='enumerate N solutions')
    parser.add_argument('-p', '--pretty', action='store_true', help='pretty print solutions')
    parser.add_argument('-g', '--all-gates', action='store_true', help='try all possible gates')
    parser.add_argument('-G', '--read-gate', action='store_true', help='read gate from stdin')
    parser.add_argument('-F', '--privacy-free', action='store_true', help='synthesize privacy free schemes')
    args = parser.parse_args()
    return args
# }}}
def print_shortcuts(namesonly=False):# {{{
    names = shortcuts().keys()
    names.sort()
    for name in names:
        print name
        if not namesonly:
            for param,val in shortcuts()[name].iteritems():
                print "\t{}: {}".format(param, val)
            print
# }}}
def print_column_names():# {{{
    print "name, size, input_bits, output_bits, helper_bits, h_arity, " +\
          "h_calls_gb, h_calls_ev, adaptive, free_vars, formula_size"
# }}}
def print_info(name, scheme, extra_info=False, csv=False):# {{{
    params = scheme['params']

    if extra_info or csv:
        free_vars    = len(scheme['formula'].get_free_variables())
        formula_size = scheme['formula'].size()

    size        = params['size']
    input_bits  = params['input_bits']
    output_bits = params['output_bits']
    helper_bits = params['helper_bits']
    h_arity     = params['h_arity']
    h_calls_gb  = params['h_calls_gb']
    h_calls_ev  = params['h_calls_ev']
    adaptive    = params['adaptive']

    if csv:
        print "{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}".format(
                name, size, input_bits, output_bits, helper_bits,
                h_arity, h_calls_gb, h_calls_ev, adaptive,
                free_vars, formula_size)
    else:
        print name
        print "\tsize         : {}".format(size)
        print "\tinput_bits   : {}".format(input_bits)
        print "\toutput_bits  : {}".format(output_bits)
        print "\thelper_bits  : {}".format(helper_bits)
        print "\th_arity      : {}".format(h_arity)
        print "\th_calls_gb   : {}".format(h_calls_gb)
        print "\th_calls_ev   : {}".format(h_calls_ev)
        print "\tadaptive     : {}".format(adaptive)
        if extra_info:
            print "\tfree_vars    : {}".format(free_vars)
            print "\tformula_size : {}".format(formula_size)
# }}}
def run_shortcut(shortcut, args):# {{{
    if args.read_gate or args.all_gates or args.verbose >= 2:
        print_truth_table(shortcut['gate'], shortcut['input_bits'], shortcut['output_bits'])
    scheme = generate_gb( shortcut
                        , check_security = not args.nocorrect
                        , check_correct  = not args.nosecure
                        , check_inv      = not args.noinv
                        )
    if args.verbose:
        if args.verbose > 2:
            print scheme['params']
        print_info(args.shortcut, scheme, extra_info=args.verbose > 1)
        print "formula generation took {0:.2f}s".format(time.time() - start)
        smt_start = time.time()
    if args.csv:
        print_info(args.shortcut, scheme, extra_info=True, csv=True)
    if args.nocheck:
        return
    else:
        if args.enumerate or args.limitedenumerate:
            if args.verbose:
                print "enumerating formula with {}...".format(args.solver)
            enumerate_scheme(scheme, args.solver, args.verbose, args.pretty, args.limitedenumerate)
        else:
            if args.verbose:
                print "checking formula with {}...".format(args.solver)
            m = check_scheme(scheme, args.solver)
            if args.verbose:
                end = time.time()
                print "smt took {0:.2f}s".format(end - smt_start)
                print "total time was {0:.2f}s".format(end - start)
            if m:
                print_model(scheme, m, pretty=args.pretty)
                return
            else:
                print "unsat"
                return
# }}}
if __name__ == "__main__":# {{{
    args = get_args()
    if args.verbose:
        start = time.time()
    if args.shortlist:
        print_shortcuts(True)
        sys.exit(0)
    if args.csvheader:
        print_column_names()
        sys.exit(0)
    if args.list:
        print_shortcuts()
        sys.exit(0)
    if not args.shortcut:
        print "error: no shortcut provided"
        sys.exit(1)
    if args.all_gates:
        s = shortcuts()[args.shortcut]
        if args.privacy_free:
            s['privacy_free'] = 1
        shortcuts = []
        for gate in all_gates(s["input_bits"], s["output_bits"]):
            s_ = copy.copy(s)
            s_['gate'] = gate
            shortcuts.append(s_)
        for s in shortcuts:
            run_shortcut(s,args) 
    else:
        shortcut = shortcuts()[args.shortcut]
        if args.privacy_free:
            shortcut['privacy_free'] = 1
        if args.read_gate:
            s = sys.stdin.readline()
            (gate, input_bits, output_bits) = gate_from_str(s)
            shortcut['gate'] = gate
            if shortcut['input_bits'] != input_bits:
                warn("input bits in gate do not equal input bits in shortcut")
            if shortcut['output_bits'] != output_bits:
                warn("output bits in gate do not equal output bits in shortcut")
        run_shortcut(shortcut, args)

# }}}
