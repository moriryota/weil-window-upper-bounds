"""Theorem A with explicit constants.

Test function (polynomial cut-offs, C^2 and piecewise polynomial, so every constant is explicit):
  h(x)  = (pi/2) x^2 (2 pi x^2 - 3) e^{-pi x^2}              (Riemann; h^ = h)
  S5(t) = 10t^3 - 15t^4 + 6t^5  (C^2 smoothstep), M_j = sup_[0,1] |S5^(j)| = 15/8, 10/sqrt3, 60
  chi   = 1 on |x| <= b := lam - 2 delta,  1 - S5((|x| - b)/delta) on b <= |x| <= b + delta,  0 beyond
  psi   = (315/32) x^2 (1 - x^2)^3 on [-1,1]   (C^2, psi(0) = 0, int psi = 1)
  phi   = h chi + eps psi,  eps = int h (1 - chi);  supp phi in [-(lam - delta), lam - delta].
With g = h(1 - chi):  phi^ = h - g^ + eps psi^, and for t > 0
  |g^(t)|    <= ||g''||_1 / (2 pi t)^2,       |t g^'(t)|    <= ||(x g)'''||_1 / (2 pi t)^2,
  |psi^(t)|  <= ||psi''||_1 / (2 pi t)^2,     |t psi^'(t)|  <= ||(x psi)'''||_1 / (2 pi t)^2
(two integrations by parts; t g^'(t) = -FT[(x g)'](t)).  Norms of g are bounded through
  U_i(b) = sum_k |q_ik| b^k e^{-pi b^2}  >= sup_{x>=b} |h^(i)(x)|   (h^(i) = Q_i e^{-pi x^2}; valid for b >= sqrt(deg/2pi)),
  I_k(s) = int_s^oo t^k e^{-pi t^2} dt <= s^{k-1} e^{-pi s^2} / (2 pi (1 - (k-1)/(2 pi s^2)))   (k >= 1),
  I_0(s) <= e^{-pi s^2} / (2 pi s).
Output: the explicit bound B(lam) >= A0 + A1 (Lemma 3.2 + Corollary 3.3 of Theorem A), the resulting bound
2 S B^2 >= |W(k)|, and, as a check of the direction, A0 + A1 computed from their definitions for the same phi."""
import sys; sys.path.insert(0, 'python')
import sympy as sp
import mpmath as mp
from smooth_A_check import A_values

mp.mp.dps = 60
X = sp.symbols('x')
hs = sp.pi / 2 * X**2 * (2 * sp.pi * X**2 - 3) * sp.exp(-sp.pi * X**2)
Q = []
for i in range(4):
    q = sp.expand(sp.simplify(sp.diff(hs, X, i) * sp.exp(sp.pi * X**2)))
    Q.append([abs(complex(q.coeff(X, k)).real) for k in range(0, sp.degree(q, X) + 1)])
DEG = max(len(c) for c in Q)          # x h''' has degree <= DEG
M1, M2, M3 = mp.mpf(15) / 8, 10 / mp.sqrt(3), mp.mpf(60)
ZETA2 = mp.pi**2 / 6
S_BOUND = 2 * (1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2)

def Ik(k, s):
    if k == 0: return mp.e**(-mp.pi * s * s) / (2 * mp.pi * s)
    assert 2 * mp.pi * s * s > k - 1
    return s**(k - 1) * mp.e**(-mp.pi * s * s) / (2 * mp.pi * (1 - (k - 1) / (2 * mp.pi * s * s)))
def U(i, b):  # sup_{x >= b} |h^(i)(x)|
    return mp.fsum(mp.mpf(c) * b**k for k, c in enumerate(Q[i])) * mp.e**(-mp.pi * b * b)
def tail(i, s, extra=0):  # >= int_s^oo x^extra |h^(i)(x)| dx
    return mp.fsum(mp.mpf(c) * Ik(k + extra, s) for k, c in enumerate(Q[i]) if c)

# psi norms (exact polynomial on [-1,1], zero outside)
psi_s = sp.Rational(315, 32) * X**2 * (1 - X**2)**3
def l1(poly):
    f = sp.lambdify(X, poly, 'mpmath')
    roots = sorted(set([mp.mpf(-1), mp.mpf(1)] + [mp.re(r) for r in mp.polyroots([float(c) for c in sp.Poly(poly, X).all_coeffs()], maxsteps=200, extraprec=200)
                                                   if abs(mp.im(r)) < 1e-20 and -1 < mp.re(r) < 1]))
    return mp.fsum(mp.quad(lambda x: abs(f(x)), [lo, hi]) for lo, hi in zip(roots[:-1], roots[1:]))
PSI2 = l1(sp.diff(psi_s, X, 2)); XPSI3 = l1(sp.diff(X * psi_s, X, 3))

def bound(lam, delta):
    b = lam - 2 * delta
    assert b >= mp.sqrt(mp.mpf(DEG) / (2 * mp.pi)) and b >= 1
    eps = 2 * tail(0, b)                                                   # |eps| <= int_{|x|>=b} |h|
    g2 = 2 * (tail(2, b) + 2 * M1 * U(1, b) + M2 * U(0, b) / delta)       # ||g''||_1
    xg3 = 2 * (tail(3, b, 1) + lam * (3 * M1 * U(2, b) + 3 * M2 * U(1, b) / delta + M3 * U(0, b) / delta**2)) + 3 * g2
    D0 = g2 + eps * PSI2; D1 = xg3 + eps * XPSI3
    ms = range(1, 60)   # m = 1..59; the m >= 60 tail is added below
    sT0 = mp.fsum(tail(0, m * lam) / m for m in ms) + D0 * ZETA2 / (4 * mp.pi**2 * lam)
    sT1 = mp.fsum(tail(1, m * lam, 1) / m for m in ms) + D1 * ZETA2 / (4 * mp.pi**2 * lam)
    bnd = lam * mp.fsum(U(0, m * lam) for m in ms) + D0 * ZETA2 / (4 * mp.pi**2 * lam)
    # m-tail (m >= 60) of the Gaussian parts: each bracket is <= P(m lam) e^{-pi m^2 lam^2} (P of degree <= 6), and
    # sum_{m >= M} <= 2 * (bracket bound at m = M) for M >= 2, lam^2 >= 5 (ratio of consecutive terms < 1/2).
    M = 60
    br = mp.mpf(3) / 2 * tail(0, M * lam) / M + tail(1, M * lam, 1) / M + lam * U(0, M * lam)
    B = mp.mpf(3) / 2 * sT0 + sT1 + bnd + 2 * br
    return B, dict(eps=eps, g2=g2, xg3=xg3, D0=D0, D1=D1, mtail=2 * br)

def make_phi_poly(lam, delta):
    b = lam - 2 * delta
    h = lambda x: (mp.pi / 2) * x**2 * (2 * mp.pi * x**2 - 3) * mp.e**(-mp.pi * x**2)
    hp = lambda x: (-2 * mp.pi**3 * x**5 + 7 * mp.pi**2 * x**3 - 3 * mp.pi * x) * mp.e**(-mp.pi * x**2)
    S5 = lambda t: 10 * t**3 - 15 * t**4 + 6 * t**5
    S5p = lambda t: 30 * t**2 * (1 - t)**2
    def chi(x):
        u = (abs(x) - b) / delta
        return mp.mpf(1) if u <= 0 else (mp.mpf(0) if u >= 1 else 1 - S5(u))
    def chip(x):
        u = (abs(x) - b) / delta
        return mp.mpf(0) if u <= 0 or u >= 1 else -mp.sign(x) * S5p(u) / delta
    psi = lambda x: mp.mpf(315) / 32 * x**2 * (1 - x**2)**3 if abs(x) < 1 else mp.mpf(0)
    psip = lambda x: mp.mpf(315) / 32 * (2 * x * (1 - x**2)**3 - 6 * x**3 * (1 - x**2)**2) if abs(x) < 1 else mp.mpf(0)
    eps = 2 * mp.quad(lambda x: h(x) * (1 - chi(x)), [b, b + delta, lam, lam + 6, mp.inf])
    phi = lambda x: h(x) * chi(x) + eps * psi(x)
    phip = lambda x: hp(x) * chi(x) + h(x) * chip(x) + eps * psip(x)
    return phi, phip, eps

if __name__ == '__main__':
    print(f"|Q_i| coefficient lists: {[[float(c) for c in q] for q in Q]}")
    print(f"||psi''||_1 = {mp.nstr(PSI2,10)}   ||(x psi)'''||_1 = {mp.nstr(XPSI3,10)}")
    print("\n(1) explicit bound B >= A0 + A1 and 2 S B^2 >= |W(k)|; scaled by e^{pi lam^2}")
    for mu in [5, 7, 9, 11, 13, 16, 20, 25, 36, 49, 64, 100]:
        lam = mp.sqrt(mu); row = []
        for name, delta in [('1/lam', 1 / lam), ('1/lam^2', 1 / lam**2)]:
            B, _ = bound(lam, delta)
            row.append(f"delta={name}: B={mp.nstr(B,5)}  B e^(pi mu)={mp.nstr(B*mp.e**(mp.pi*mu),5)}  2SB^2={mp.nstr(2*S_BOUND*B*B,5)}")
        print(f"mu={mu:>3}: " + " | ".join(row), flush=True)
    print("\n(2) direction check: A0 + A1 from the definitions (same phi, delta = 1/lam^2) <= B")
    for mu in [5, 7, 11, 13]:
        lam = mp.sqrt(mu); delta = 1 / lam**2
        phi, phip, eps = make_phi_poly(lam, delta)
        xt = lam - 1.5 * delta; fd = (phi(xt + mp.mpf('1e-30')) - phi(xt - mp.mpf('1e-30'))) / mp.mpf('2e-30')
        A0, A1, bd, cut = A_values(lam, phi, phip, 5, mp.mpf('0.05'), 24)
        B, parts = bound(lam, delta)
        print(f"mu={mu}: eps={mp.nstr(eps,5)} (bound {mp.nstr(parts['eps'],5)})  phi' check {mp.nstr(phip(xt),8)} vs {mp.nstr(fd,8)}  "
              f"A0+A1={mp.nstr(A0+A1,6)}  B={mp.nstr(B,6)}  B/(A0+A1)={mp.nstr(B/(A0+A1),5)}  (integrand at cut {mp.nstr(cut,3)})", flush=True)
