r"""
Dedekind zeta function for totally real number fields.

Please run Sage where this file is saved and type 'from dedekind_zeta import *' to use the dedekind_zeta() function below.

AUTHORS:
 - Brandon Williams
"""

from sage.functions.gamma import gamma
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.matrix.constructor import matrix
from sage.modular.modform.constructor import ModularForms
from sage.modules.free_module_element import vector
from sage.rings.integer import Integer
from sage.rings.real_mpfr import RR
from sage.symbolic.constants import pi

def dedekind_zeta(n, K): #Computes the exact value of the Dedekind zeta function of a totally real number field K at the integer n. (n should not be positive and odd)
    r"""
    Compute exact values of Dedekind zeta functions for totally real number fields at integers.

    INPUT:

    - ``n`` -- an integer. This should not be both positive and odd (in which case the exact value is unknown)

    - ``K`` -- a NumberField

    ALGORITHM: following the proof of the Klingen--Siegel theorem, compute the Hilbert modular form Eisenstein series associated to `K` and evaluate it along the diagonal.

    EXAMPLES::

        sage: from dedekind_zeta import *
        sage: K.<a> = QuadraticField(5)
        sage: dedekind_zeta(-1, K)
        1/30
    """
    n = Integer(n)
    one_half = Integer(1) / 2
    degK = K.degree()
    if degK == 1:
        return zeta(n)
    dK = K.different()
    GalK = K.embeddings(RR)
    if degK != len(GalK):
        raise ValueError('Not a totally real number field')
    if n >= 0:
        if n % 2:
            raise ValueError("n should not be positive and odd.")
        return dedekind_zeta(1-n,K) * abs(dK.norm()) ** (one_half - n) * (pi ** (n - one_half) * gamma((1 - n)/2) / gamma(n / 2)) ** degK
    if not n % 2:
        return 0
    DK = dK ** (-1)
    DKBasis = DK.basis()
    k = (1 - n) * degK
    q, r = k.quo_rem(12)
    bound = q + 2 - (r == 2)
    mf = ModularForms(1, k, prec = bound).basis()
    def divisor_power_sum(K, I, n): #returns sum of N(a)**n where a runs through ideals dividing I.
        X = I.factor()
        p = Integer(1)
        for x, y in X:
            u = x.norm()
            u_n = u ** n
            p *= (1 - u_n ** (1 + y)) / (1 - u_n)
        return p
    w = matrix([[x[j] for j in range(1,bound)] for x in mf]).solve_left(vector( [sum([divisor_power_sum(K, dK*K.ideal(sum(u[i]*x for i, x in enumerate(DKBasis))),-n) for u in Polyhedron(ieqs=[[0]+[sigma(x) for x in DKBasis] for sigma in GalK], eqns=[[l+1] + [-x.trace() for x in DKBasis]]).integral_points()]) for l in range(bound-1)] ))
    return sum(w[i]*x for i, x in enumerate(mf))[0] * 2 ** degK