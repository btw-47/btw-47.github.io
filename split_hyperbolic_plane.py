def extend_vector(v):
    r"""
    Compute a matrix in GL_n(ZZ) whose first row is the given vector "v".
    """
    return matrix(ZZ, v).transpose().hermite_form(transformation = True)[1].inverse()

def splitter(S):
    r"""
    Attempt to split off a hyperbolic plane that is defined over ZZ.
    This guesses vectors which are likely to split off a hyperbolic plane.
    It often raises a RuntimeError.
    """
    Q = QuadraticForm(QQ, S)
    v = Q.solve(0)
    if denominator(v) != 1:
        raise RuntimeError('Failed')
    v = v / gcd(v)
    N = gcd(S*v)
    _, h = xgcd_list(v)
    h = N * S.inverse() *vector(h)
    A = matrix(QQ, [S*v]).transpose().integer_kernel().basis_matrix()
    for a in A.rows():
        i = next(i for i, x in enumerate(a) if x)
        h -= frac(h[i]) * a / a[i]
    if S.nrows() > 2:
        A = matrix(QQ, [S*v, S*h]).transpose().integer_kernel().basis_matrix()
        try:
            h_norm_N = ZZ(h * S * h / (2*N))
        except TypeError:
            raise RuntimeError('Failed') from None
        Q0 = QuadraticForm(QQ, A * S * A.transpose())
        denom = True
        i = -1
        while denom and abs(i) < 100:
            i += 1
            if (-h_norm_N - i) % N == 0:
                try:
                    x = Q0.solve(ZZ((-h_norm_N - i)/N))
                    sgn = 1
                    denom = (denominator(x) != 1)
                except ArithmeticError:
                    pass
            if denom and (-h_norm_N + i) % N == 0:
                try:
                    x = Q0.solve(ZZ((-h_norm_N + i)/N))
                    sgn = -1
                    denom = (denominator(x) != 1)
                except ArithmeticError:
                    pass
        if denom:
            raise RuntimeError('Failed')
        f = h + N*x*A + sgn * i*v
        A = matrix(QQ, [S*v, S*f]).transpose().integer_kernel().basis_matrix()
        try:
            U = matrix(ZZ, [v, f] + A.rows()).transpose()
        except TypeError:
            raise RuntimeError('Failed') from None
    else:
        try:
            h_norm_N = ZZ(h * S * h / (2*N))
        except TypeError:
            raise RuntimeError('Failed') from None
        f = h - v*h_norm_N
        U = matrix(ZZ, [v, f]).transpose()
    if abs(U.determinant()) > 1:
        raise RuntimeError('Failed')
    return U

def randomized_splitter(S, ntries = 100):
    r"""
    Try the "splitter" method repeatedly.
    pari qfsolve always returns the same vector given the same input.
    This gets random values out of pari qfsolve by choosing a first basis vector at random to start the LLL algorithm
    """
    for _ in range(ntries):
        v = random_vector(ZZ, S.nrows())
        U = extend_vector(v)
        S1 = U.transpose() * S * U
        try:
            J = splitter(S1)
            return U*J
        except ArithmeticError:
            raise RuntimeError('Failed') from None
        except RuntimeError:
            pass
    raise RuntimeError('Failed')

def xgcd_list(L):
    r"""
    xgcd for list
    """
    if len(L) == 1:
        return [L[0], [1]]
    g, v = xgcd_list(L[:-1])
    g, a, b = xgcd(g, L[-1])
    return [g, [a*x for x in v] + [b]]

def split(S, ntries = 100):
    r"""
    """
    Q = QuadraticForm(ZZ, S)
    n = S.nrows()
    if Q.signature() == n:
        return matrix(n, n, pari.qflllgram(S, flag = 1))
    if S.nrows() > 1:
        try:
            U = randomized_splitter(S, ntries = ntries)
            S = (U.transpose() * S * U)[2:, 2:]
            return U * block_diagonal_matrix([identity_matrix(2), split(S)])
        except RuntimeError:
            L0 = IntegralLattice(S)
            L1 = L0.lll()
            return L0.lll().basis_matrix().transpose()
    return identity_matrix(S.nrows())