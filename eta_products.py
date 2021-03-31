r"""
This is Sage code for computing eta products and for identifying eta products from their q-series. Run Sage in the folder where this file is sage and type 'from eta_products import *' to load everything below.

AUTHORS:
- Brandon Williams
"""


import math
from re import sub

from sage.arith.functions import lcm
from sage.functions.generalized import sgn
from sage.functions.log import log
from sage.functions.other import floor, frac
from sage.misc.functional import isqrt
from sage.modular.modform.eis_series import eisenstein_series_qexp
from sage.rings.all import CC
from sage.rings.infinity import Infinity
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

class EtaProduct:
    r"""
    Construct an Eta product (or quotient).

    INPUT:

    - ``L`` -- a list of lists or tuples of the form [[n_1, a_1], [n_2, a_2], ..., [n_r, a_r]]. This represents the eta product \eta(n_1 z)^(a_1) * ... * \eta(n_r z)^(a_r).

    - ``prec`` -- the precision of the q-expansion (default 20)

    - ``data`` -- for constructing an EtaProduct from a given q-expansion. This should be left alone.

    ALGORITHM:
    use Jacobi's identity to write \eta(z)^3 as the derivative of a theta function.

    EXAMPLES::

        sage: from eta_products import *
        sage: EtaProduct([[1, 2], [3, 4]], 30) #eta product \eta(z)^2 * \eta(3z)^4
        q^(7/12) - 2*q^(19/12) - q^(31/12) - 2*q^(43/12) + 9*q^(55/12) + 6*q^(67/12) - 8*q^(79/12) - 8*q^(91/12) - 12*q^(103/12) + 18*q^(115/12) - 13*q^(127/12) + 4*q^(139/12) + 15*q^(151/12) + 16*q^(163/12) + 20*q^(175/12) - 36*q^(187/12) - q^(199/12) - 34*q^(211/12) - 16*q^(223/12) + 18*q^(235/12) + 16*q^(247/12) + 2*q^(259/12) - 3*q^(271/12) + 10*q^(283/12) + 36*q^(295/12) - 12*q^(307/12) + 18*q^(319/12) + 38*q^(331/12) - 37*q^(343/12) - 36*q^(355/12) + O(q^(367/12))
    """
    def __init__(self, L, prec=20, data = None):
        if data is None:
            r, q = PowerSeriesRing(ZZ, 'q', default_prec = prec).objgen()
            f = r(1).add_bigoh(prec)
            offset = 0
            weight = 0
            levels = [0]*len(L)
            for k, (n, exponent) in enumerate(L):
                levels[k] = n
                offset += exponent * n
                weight = weight + exponent / 2
                sign = sgn(exponent)
                abs_exponent = abs(exponent)
                exp_remainder = abs_exponent % 3
                jacobi_exponent = (abs_exponent - exp_remainder) // 3
                g = prec // n + 2
                jacobi_bound = (isqrt(1 + 8 * g) - 1) // 2 + 1
                jacobi_kfactor = [0] * prec
                jacobi_kfactor[0] = 1
                eps = -1
                for l in range(1, jacobi_bound):
                    try:
                        jacobi_kfactor[n*l*(l+1) // 2] = eps * (l + l + 1)
                    except IndexError:
                        pass
                    eps = -eps
                f *= r(jacobi_kfactor) ** (sign*jacobi_exponent)
                if exp_remainder:
                    bound = isqrt(1 + 24*g)//6 + 1
                    kfactor = [0] * prec
                    kfactor[0] = 1
                    eps = -1
                    for l in range(1, bound):
                        nl = n * l
                        u = nl * (3 * l - 1) // 2
                        try:
                            kfactor[u] = eps
                        except IndexError:
                            pass
                        try:
                            kfactor[u + nl] = eps
                        except IndexError:
                            pass
                        eps = -eps
                    f *= r(kfactor) ** (sign * exp_remainder)
            offset /= 24
            offset_floor = floor(offset)
            offset = frac(offset)
            if offset_floor < 0:
                f *= q ** offset_floor
            elif offset_floor:
                f = f.shift(offset_floor)
            self.__level = lcm(levels)
            self.__qexp = f
            self.__shift = offset
            self.__weight = weight
        else:
            self.__level, self.__qexp, self.__shift, self.__weight = data

    def __repr__(self):
        try:
            return self.__string
        except AttributeError:
            s = str(self.__qexp)
            shift = self.__shift
            if shift:
                r = r'((?<!\w)q(?!\w)(\^-?\d+)?)|((?<!\^)\d+\s)'
                def m(y):
                    y = y.string[slice( * y.span() )]
                    if y[0] != 'q':
                        return '%sq^(%s) '%([y[:-1]+'*',''][y == '1 '], shift)
                    try:
                        return 'q^(%s)'%(QQ(y[2:]) + shift)
                    except TypeError:
                        return 'q^(%s)'%(1 + shift)
                s = sub(r, m, s)
            return s

    def __add__(self, other):
        self_shift = self.__shift
        other_shift = other.__shift
        self_weight = self.__weight
        other_weight = other.__weight
        if self_shift != other_shift or self_weight != other_weight:
            raise ValueError
        return EtaProduct(None, data = [lcm(self.__level, other.__level), self.__qexp + other.__qexp, self_shift, self.__weight])

    def __div__(self, other):
        return self *~ other
    __truediv__ = __div__

    def __invert__(self):
        f = ~self.__qexp
        offset = self.__shift
        if offset:
            q, = f.parent().gens()
            f *= ~q
            offset = 1 - offset
        return EtaProduct(None, data = [self.__level, f, offset, -self.__weight])

    def __mul__(self, other):
        if other in CC:
            return EtaProduct(None, data = [self.__level, other * self.__qexp, self.__shift, self.__weight])
        f = self.__qexp * other.__qexp
        offset = self.__shift + other.__shift
        if offset >= 1:
            offset -= 1
            f = f.shift(1)
        return EtaProduct(None, data = [lcm(self.__level, other.__level), f, offset, self.__weight + other.__weight])

    __rmul__ = __mul__

    def __neg__(self):
        return EtaProduct(None, data = [self.__level, -self.__qexp, self.__shift, self.__weight])

    def __pow__(self, other):
        if other in ZZ:
            if other >= 1:
                if other == 1:
                    return self
                elif other == 2:
                    return self * self
                else:
                    nhalf = other // 2
                    return (self ** nhalf) * (self ** (other - nhalf))
            else:
                return ~(self.__pow__(-other))
        raise ValueError

    def __sub__(self, other):
        self_shift = self.__shift
        other_shift = other.__shift
        self_weight = self.__weight
        other_weight = other.__weight
        if self_shift != other_shift or self_weight != other_weight:
            raise ValueError
        return EtaProduct(None, data = [lcm(self.__level, other.__level), self.__qexp - other.__qexp, self_shift, self.__weight])

    def prec(self):
        return self.__qexp.prec()

    def qexp(self):
        return self.__qexp

    def valuation(self):
        return self.__qexp.valuation()

    def weight(self):
        return self.__weight

def identify_eta_product(f, output = False):
    r"""
    Attempt to identify a q-series as an eta product.

    INPUT:

    - ``f`` -- The function to be identified. This can be given as (1) a power series; (2) a Puiseux series; (3) a modular form; (4) an EtaProduct

    - ``output`` -- boolean (default False). If True then we output the data to produce f as an EtaProduct (i.e. a list of lists [N, exponent]). If False then we print the output and return None.

    ALGORITHM: subtract away Eichler integrals of Eisenstein series of weight 2 from the logarithm log(f)
    """
    try:
        f = f.qexp()
    except AttributeError:
        pass
    e = 1
    try:
        e = f.ramification_index()
        f = f.laurent_part()
    except AttributeError:
        pass
    try:
        prec = f.prec()
    except AttributeError:
        if f in CC:
            if output:
                return []
            print('This appears to be %s.'%f)
            print('Weight: 0')
            print('Level: 1')
            return None
        raise ValueError
    fval = f.valuation()
    q, = f.parent().gens()
    f = f * q ** (-fval)
    try:
        f = f.power_series()
    except AttributeError:
        pass
    if prec is Infinity:
        prec = f.degree() + 1
    prefactor = f[0]
    f /= prefactor
    L = []
    logf = f.log(prec = prec)
    e2 = ((eisenstein_series_qexp(2, prec + 1) + Integer(1)/24).shift(-1)).integral() #not really e2
    level = 1
    shift = Integer(fval) / e
    wt = 0
    while logf:
        N = logf.valuation()
        if N >= prec - fval:
            logf = 0
            break
        level = lcm(level, N)
        if math.log(level) > prec / 2:
            print("This is probably not an eta product.")
            return
        exponent = -logf[N]
        if not exponent.is_integer():
            print( "This is not an eta product.")
            return
        L.append([N / e,exponent])
        logf += exponent * e2.V(N)
        shift -= N * exponent / (24 * e)
        wt += exponent / 2
    if output:
        return L
    s = "This appears to be "
    if prefactor != 1:
        s += str(prefactor)
        if L:
            s += "*"
    if not L:
        s += "1"
        wt = 0
    elif shift:
        t = ''
        if shift - 1:
            t = '^'
            if shift < 0 or not shift.is_integer():
                t1, t2 = '(', ')'
            else:
                t1 = t2 = ''
            t += t1 + str(shift) + t2
        s += ('q' + t + '*')
    def a(x):
        N, exponent = x
        s1 = s2 = s3 = s4 = ''
        if N - 1:
            if N.is_integer():
                s1 = str(N)
            else:
                s1 = '(%s)'%N
        if exponent - 1:
            s2 = '^'
            s3 = str(exponent)
            if exponent < 0:
                s2, s4 = '^(', ')'
        return 'eta(%sz)%s'%(s1, s2 + s3 + s4)
    print (s + '*'.join(map(a, L)) + '.')
    print('Weight: %s'%(wt))
    print('Level: %s'%lcm([x[0] for x in L]))