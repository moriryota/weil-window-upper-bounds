"""Weil quadratic form Q on the orthonormal Legendre basis of L^2(-L, L), in Arb ball arithmetic.

Q(f) = h0 ||f||^2 + 1/4 ∬_{R^2} K(|x-y|) |f(x)-f(y)|^2 + 2 (∫ f cosh(x/2))^2 - 2 (∫ f sinh(x/2))^2
       - 2 Σ_{n < e^{2L}} Λ(n)/√n Re ∫ f(t) f(t - log n) dt                       (real f)
K(u) = e^{u/2}/sinh u,  h0 = ψ(1/4) - log π.   Same Q as python/weil_pc.py (validated against zeros).

Basis φ_j(x) = sqrt((2j+1)/(2L)) P_j(x/L), j < N. Hardy part split as
  interior:  1/4 ∬_{I^2} K(|x-y|)(φ_i(x)-φ_i(y))(φ_j(x)-φ_j(y))
           = 1/2 ∬_{y<x} k1(u) u D_i D_j,   u = x-y, k1(u) = u K(u) (analytic), D_i = divided difference,
             computed on the triangle by the Duffy map x = -L+2Ls, y = -L+2Lsr and Gauss–Legendre in (s, r);
  exterior:  1/2 ∫_I φ_i φ_j [G(L-x) + G(L+x)],  G(d) = ∫_d^∞ K = 2 artanh(e^{-d/2}) + 2 arctan(e^{-d/2}),
             by tanh-sinh quadrature (log singularities at ±L).
The balls account for rounding only, not for quadrature truncation; convergence in the number of
nodes is checked separately (see check_spectral.py). Results are numerical, not certified.
"""
import math
from flint import arb, arb_mat, ctx


def von_mangoldt(n):
    if n < 2:
        return None
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return p if m == 1 else None
        p += 1
    return n


def gauss_legendre(n):
    """Nodes and weights on [-1, 1]."""
    xs, ws = [], []
    for k in range(n):
        x, w = arb.legendre_p_root(n, k, weight=True)
        xs.append(x)
        ws.append(w)
    return xs, ws


def legendre_values(xi, N):
    """P_0..P_{N-1} at xi (arb)."""
    P = [arb(1), xi]
    for n in range(1, N - 1):
        P.append(((2 * n + 1) * xi * P[n] - n * P[n - 1]) / (n + 1))
    return P[:N]


def legendre_dd(x, y, N):
    """Divided differences (P_n(x) - P_n(y))/(x - y), n < N, by the stable recurrence
    DD_{n+1} = ((2n+1)(P_n(y) + x DD_n) - n DD_{n-1})/(n+1)."""
    Py = legendre_values(y, N)
    D = [arb(0), arb(1)]
    for n in range(1, N - 1):
        D.append(((2 * n + 1) * (Py[n] + x * D[n]) - n * D[n - 1]) / (n + 1))
    return D[:N]


def G_ext(d):
    """G(d) = ∫_d^∞ K(u) du for d > 0, via 2 artanh(e^{-d/2}) + 2 arctan(e^{-d/2});
    artanh(y) = ½ log((1+y)/(1-y)) with 1 - y = -expm1(-d/2) computed without cancellation."""
    y = (-d / 2).exp()
    one_minus_y = -((-d / 2).expm1())
    return ((1 + y) / one_minus_y).log() + 2 * y.atan()


class WeilSpectral:
    def __init__(self, L, N, prec=256, n_tri=None, ts_h=None, ts_n=None):
        ctx.prec = prec
        self.L = arb(L) if not isinstance(L, arb) else L
        self.N = N
        self.n_tri = n_tri or (N + 40)
        self.ts_h = ts_h if ts_h is not None else 1.0 / 64
        self.ts_n = ts_n or 1000
        self.norm = [((2 * j + 1) / (2 * self.L)).sqrt() for j in range(N)]
        self.n_ext = N + 60

    # --- pieces -------------------------------------------------------------------------------
    def hardy_interior(self):
        L, N = self.L, self.N
        xs, ws = gauss_legendre(self.n_tri)
        acc = [[arb(0)] * N for _ in range(N)]
        rows, wts = [], []
        for a in range(self.n_tri):
            s = (xs[a] + 1) / 2
            ws_ = ws[a] / 2
            for b in range(self.n_tri):
                r = (xs[b] + 1) / 2
                wr = ws[b] / 2
                x = -L + 2 * L * s
                y = -L + 2 * L * s * r
                u = x - y
                k1 = u * K_of(u)
                weight = ws_ * wr * (2 * L) ** 2 * s * k1 * u / 2
                D = legendre_dd(x / L, y / L, N)          # in ξ-variables; D_x = D_ξ / L
                rows.append([D[j] * self.norm[j] / L for j in range(N)])
                wts.append(weight)
        return gram(rows, wts, N)

    def hardy_exterior(self):
        """1/2 ∫ φ_i φ_j W, W(x) = G(L-x) + G(L+x) = -log(L-x) - log(L+x) + W_reg(x), W_reg analytic.
        Log part exact via log(1-ξ) = (ln2 - 1) - Σ_{n≥1} (2n+1)/(n(n+1)) P_n(ξ) and Gaunt integrals
        ∫P_iP_jP_n = 2 (i j n; 0 0 0)^2; W_reg part by Gauss–Legendre."""
        L, N = self.L, self.N
        # log part
        lgm = log_moment_matrix(N)                     # ∫_{-1}^{1} P_i P_j log(1-ξ) dξ
        logL = L.log()
        M = arb_mat(N, N)
        for i in range(N):
            for j in range(N):
                par = 2 if (i + j) % 2 == 0 else 0
                val = par * lgm[i][j] + (2 * logL * 2 / (2 * i + 1) if i == j else 0)
                M[i, j] = -self.norm[i] * self.norm[j] * L * val / 2
        # regular part
        xs, ws = gauss_legendre(self.n_ext)
        rows, wts = [], []
        for xi, w in zip(xs, ws):
            dm, dp = L * (1 - xi), L * (1 + xi)
            Wr = G_reg(dm) + G_reg(dp)
            P = legendre_values(xi, N)
            rows.append([P[j] * self.norm[j] for j in range(N)])
            wts.append(w * L * Wr / 2)
        return M + gram(rows, wts, N)

    def l2_and_poles(self):
        L, N = self.L, self.N
        h0 = arb(0.25).digamma() - arb.pi().log()
        xs, ws = gauss_legendre(N + 40)
        c = [arb(0)] * N
        s = [arb(0)] * N
        for xi, w in zip(xs, ws):
            x = L * xi
            P = legendre_values(xi, N)
            ch, sh = (x / 2).cosh(), (x / 2).sinh()
            for j in range(N):
                v = P[j] * self.norm[j] * w * L
                c[j] += v * ch
                s[j] += v * sh
        M = arb_mat(N, N)
        for i in range(N):
            for j in range(N):
                M[i, j] = 2 * c[i] * c[j] - 2 * s[i] * s[j] + (h0 if i == j else 0)
        return M, s

    def primes(self):
        L, N = self.L, self.N
        M = arb_mat(N, N)
        nmax = int(math.floor(math.exp(2 * float(L.mid()))))
        xs, ws = gauss_legendre(N + 2)
        for n in range(2, nmax + 1):
            p = von_mangoldt(n)
            if p is None:
                continue
            ell = arb(n).log()
            if not (ell < 2 * L):
                continue
            lo, hi = -L + ell, L
            half = (hi - lo) / 2
            mid = (hi + lo) / 2
            ra, rb, wt = [], [], []
            for xi, w in zip(xs, ws):
                t = mid + half * xi
                Pa = legendre_values(t / L, N)
                Pb = legendre_values((t - ell) / L, N)
                ra.append([Pa[i] * self.norm[i] for i in range(N)])
                rb.append([Pb[j] * self.norm[j] for j in range(N)])
                wt.append(w * half)
            S = cross(ra, rb, wt, N)
            coef = 2 * arb(p).log() / arb(n).sqrt()
            for i in range(N):
                for j in range(N):
                    M[i, j] -= coef * (S[i, j] + S[j, i]) / 2
        return M

    def matrix(self, verbose=False):
        import time
        t0 = time.time()
        Hi = self.hardy_interior()
        t1 = time.time()
        He = self.hardy_exterior()
        t2 = time.time()
        Mp, s = self.l2_and_poles()
        Pr = self.primes()
        t3 = time.time()
        if verbose:
            print(f'  timing: interior {t1-t0:.1f}s exterior {t2-t1:.1f}s rest {t3-t2:.1f}s')
        self.polar = s
        return Hi + He + Mp + Pr


def G_reg(d):
    """G(d) + log d, analytic at d = 0: log(1+y) - log((1-y)/d) + 2 atan(y), y = e^{-d/2}."""
    y = (-d / 2).exp()
    q = -((-d / 2).expm1()) / d
    return (1 + y).log() - q.log() + 2 * y.atan()


_LGM_CACHE = {}


def log_moment_matrix(N):
    """∫_{-1}^{1} P_i P_j log(1-ξ) dξ for i, j < N (arb, exact up to rounding)."""
    if N in _LGM_CACHE and _LGM_CACHE[N][0] == ctx.prec:
        return _LGM_CACHE[N][1]
    from fractions import Fraction
    from math import factorial
    fac = [factorial(k) for k in range(2 * 2 * N + 5)]
    ln2 = arb(2).log()
    out = [[arb(0)] * N for _ in range(N)]
    for i in range(N):
        for j in range(i, N):
            acc = Fraction(0)
            for n in range(max(1, abs(i - j)), i + j + 1):
                s2 = i + j + n
                if s2 % 2:
                    continue
                g = s2 // 2
                if g < i or g < j or g < n:
                    continue
                w3 = Fraction(fac[s2 - 2*i] * fac[s2 - 2*j] * fac[s2 - 2*n], fac[s2 + 1]) * \
                     Fraction(fac[g], fac[g - i] * fac[g - j] * fac[g - n]) ** 2
                acc += Fraction(2 * n + 1, n * (n + 1)) * 2 * w3
            val = -arb(acc.numerator) / arb(acc.denominator)
            if i == j:
                val += (ln2 - 1) * 2 / (2 * i + 1)
            out[i][j] = val
            out[j][i] = val
    _LGM_CACHE[N] = (ctx.prec, out)
    return out


def K_of(u):
    return (u / 2).exp() / u.sinh()


def gram(rows, wts, N):
    """Σ_k w_k r_k r_k^T via arb_mat products."""
    R = arb_mat(len(rows), N)
    RW = arb_mat(len(rows), N)
    for k, (r, w) in enumerate(zip(rows, wts)):
        for j in range(N):
            R[k, j] = r[j]
            RW[k, j] = r[j] * w
    return R.transpose() * RW


def cross(rows_a, rows_b, wts, N):
    """Σ_k w_k a_k b_k^T."""
    A = arb_mat(len(rows_a), N)
    B = arb_mat(len(rows_b), N)
    for k in range(len(rows_a)):
        for j in range(N):
            A[k, j] = rows_a[k][j] * wts[k]
            B[k, j] = rows_b[k][j]
    return A.transpose() * B


def parity_block(M, parity):
    idx = [j for j in range(M.nrows()) if j % 2 == parity]
    B = arb_mat(len(idx), len(idx))
    for a, i in enumerate(idx):
        for b, j in enumerate(idx):
            B[a, b] = M[i, j]
    return B, idx
