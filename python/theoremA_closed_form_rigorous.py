"""rigorous closed form for Theorem A:  F(lam) := B(lam) e^{pi lam^2} / lam^8 <= K for all mu = lam^2 >= 5.

B(lam) is the explicit bound of theoremA_explicit.bound (delta = 1/lam^2), i.e. (3.4) of the consolidated proof.
We rewrite every Gaussian factor together with e^{pi lam^2}:
  U_i(s) e^{pi lam^2} = P_i(s) e^{-pi (s^2 - lam^2)},
  I_k(s) e^{pi lam^2} <= s^{k-1} e^{-pi (s^2 - lam^2)} / (2 pi (1 - (k-1)/(2 pi s^2)))    (k >= 1),
  I_0(s) e^{pi lam^2} <= e^{-pi (s^2 - lam^2)} / (2 pi s),
with s^2 - lam^2 = -4/lam + 4/lam^4 for s = b = lam - 2/lam^2, and (m^2 - 1) lam^2 for s = m lam.
Part 1 (5 <= mu <= 1e4): ball arithmetic (python-flint arb) over lam-intervals of width 0.002.
Part 2 (mu >= 1e4, lam >= 100): b <= lam, e^{pi(lam^2 - b^2)} <= e^{4 pi/100}, 1/(1-(k-1)/(2 pi s^2)) <= its value at s = 99.9, 1/b <= 1/99.9;
  then F(lam) <= Pi(lam)/lam^8 + (m >= 2 terms), with Pi a Laurent polynomial with nonnegative coefficients and top degree <= 8,
  so Pi(lam)/lam^8 is nonincreasing and F(lam) <= Pi(100)/100^8 + tiny.
Constants: q_ik exact (sympy), ||psi''||_1 and ||(x psi)'''||_1 exact (sympy, algebraic endpoints), zeta(2) = pi^2/6."""
import sympy as sp
from flint import arb, ctx
ctx.prec = 200

X = sp.symbols('x')
hs = sp.pi / 2 * X**2 * (2 * sp.pi * X**2 - 3) * sp.exp(-sp.pi * X**2)
Qexact = []
for i in range(4):
    q = sp.expand(sp.simplify(sp.diff(hs, X, i) * sp.exp(sp.pi * X**2)))
    Qexact.append([sp.Abs(q.coeff(X, k)) for k in range(0, sp.degree(q, X) + 1)])
DEG = max(len(c) for c in Qexact)

def to_arb(expr):
    """Exact sympy number (polynomial in pi with rational coefficients, or algebraic) -> arb ball (contains it)."""
    e = sp.nsimplify(expr) if not expr.free_symbols else expr
    s = sp.N(e, 80)
    return arb(str(s)) + arb(0, sp.N(sp.Abs(e) * sp.Rational(1, 10**70) + sp.Rational(1, 10**70), 5))

Qarb = [[to_arb(c) for c in row] for row in Qexact]

psi = sp.Rational(315, 32) * X**2 * (1 - X**2)**3
def exact_l1(p):
    rts = sorted([r for r in sp.real_roots(sp.Poly(p, X)) if -1 < r < 1], key=lambda r: float(r))
    pts = [sp.Integer(-1)] + rts + [sp.Integer(1)]
    tot = 0
    for lo, hi in zip(pts[:-1], pts[1:]):
        mid = (lo + hi) / 2
        sgn = 1 if p.subs(X, mid) > 0 else -1
        tot += sgn * sp.integrate(p, (X, lo, hi))
    return sp.N(tot, 60)
PSI2 = arb(str(exact_l1(sp.diff(psi, X, 2)))) + arb(0, 1e-40)
XPSI3 = arb(str(exact_l1(sp.diff(X * psi, X, 3)))) + arb(0, 1e-40)
PI = arb.pi()
M1, M2, M3 = arb(15) / 8, 10 / arb(3).sqrt(), arb(60)
ZETA2 = PI**2 / 6

def Pi_poly(i, s):   # P_i(s) = sum |q_ik| s^k
    return sum((c * s**k for k, c in enumerate(Qarb[i])), arb(0))

def I_scaled(k, s, d):   # I_k(s) e^{pi lam^2}, d = s^2 - lam^2
    if k == 0:
        return (-PI * d).exp() / (2 * PI * s)
    return s**(k - 1) * (-PI * d).exp() / (2 * PI * (1 - (k - 1) / (2 * PI * s**2)))

def tail_scaled(i, s, d, extra=0):
    return sum((c * I_scaled(k + extra, s, d) for k, c in enumerate(Qarb[i])), arb(0))

def U_scaled(i, s, d):
    return Pi_poly(i, s) * (-PI * d).exp()

def F(lam):
    """B(lam) e^{pi lam^2} / lam^8, as an arb ball (lam may be a ball)."""
    delta = 1 / lam**2
    b = lam - 2 * delta
    db = -4 / lam + 4 / lam**4                     # b^2 - lam^2
    eps = 2 * tail_scaled(0, b, db)
    g2 = 2 * (tail_scaled(2, b, db) + 2 * M1 * U_scaled(1, b, db) + M2 * U_scaled(0, b, db) / delta)
    xg3 = 2 * (tail_scaled(3, b, db, 1) + lam * (3 * M1 * U_scaled(2, b, db) + 3 * M2 * U_scaled(1, b, db) / delta
                                                  + M3 * U_scaled(0, b, db) / delta**2)) + 3 * g2
    D0 = g2 + eps * PSI2
    D1 = xg3 + eps * XPSI3
    sT0 = sum((tail_scaled(0, m * lam, (m * m - 1) * lam**2) / m for m in range(1, 60)), arb(0)) + D0 * ZETA2 / (4 * PI**2 * lam)
    sT1 = sum((tail_scaled(1, m * lam, (m * m - 1) * lam**2, 1) / m for m in range(1, 60)), arb(0)) + D1 * ZETA2 / (4 * PI**2 * lam)
    bnd = lam * sum((U_scaled(0, m * lam, (m * m - 1) * lam**2) for m in range(1, 60)), arb(0)) + D0 * ZETA2 / (4 * PI**2 * lam)
    M = 60
    br = arb(3) / 2 * tail_scaled(0, M * lam, (M * M - 1) * lam**2) / M + tail_scaled(1, M * lam, (M * M - 1) * lam**2, 1) / M \
         + lam * U_scaled(0, M * lam, (M * M - 1) * lam**2)
    B = arb(3) / 2 * sT0 + sT1 + bnd + 2 * br
    return B / lam**8

if __name__ == '__main__':
    # sanity: point values against theoremA_explicit (B e^{pi mu}/mu^4 = 12163.9 at mu = 5)
    print("F(sqrt 5) =", F(arb(5).sqrt()).str(10), "  F(10) =", F(arb(10)).str(10), "  F(100) =", F(arb(100)).str(10), flush=True)
    # Part 1: lam in [sqrt 5, 100], intervals of width h
    h = arb(1) / 500
    lo = arb(5).sqrt()
    worst = arb(0); worst_at = None; n = 0
    x = lo
    while True:
        hi = x + h
        if hi > 100:
            hi = arb(100)
        ball = arb((x + hi) / 2) .union(x).union(hi)
        val = F(ball)
        if val.upper() > worst.upper():
            worst, worst_at = val, (x.str(6), hi.str(6))
        n += 1
        if hi >= 100:
            break
        x = hi
    print(f"Part 1: {n} intervals; sup F over mu in [5, 1e4] <= {worst.upper().str(12)} (at lam in {worst_at})", flush=True)
    # Part 2: lam >= 100, Laurent-polynomial bound (monotone), evaluated at lam = 100 with conservative constants
    L = arb(100)
    Eb = (4 * PI / 100).exp()                       # e^{pi(lam^2 - b^2)} <= e^{4 pi / lam}
    Ci = 1 / (1 - arb(8) / (2 * PI * arb('99.9')**2))  # (1 - (k-1)/(2 pi s^2))^{-1}, k <= 9, s >= 99.9
    def P(i, s): return Pi_poly(i, s)
    def Tb(i, extra=0):    # tail at b, scaled: <= sum |q| lam^{k+extra-1} Eb Ci/(2pi), k+extra=0 term: Eb/(2 pi * 99.9)
        tot = arb(0)
        for k, c in enumerate(Qarb[i]):
            kk = k + extra
            tot += c * (Eb / (2 * PI * arb('99.9')) if kk == 0 else L**(kk - 1) * Eb * Ci / (2 * PI))
        return tot
    def T1(i, extra=0):   # tail at s = lam (m = 1), scaled factor e^0 = 1
        tot = arb(0)
        for k, c in enumerate(Qarb[i]):
            kk = k + extra
            tot += c * (1 / (2 * PI * L) if kk == 0 else L**(kk - 1) * Ci / (2 * PI))
        return tot
    delta_inv = L**2
    eps = 2 * Tb(0)
    g2 = 2 * (Tb(2) + 2 * M1 * P(1, L) * Eb + M2 * P(0, L) * Eb * delta_inv)
    xg3 = 2 * (Tb(3, 1) + L * (3 * M1 * P(2, L) * Eb + 3 * M2 * P(1, L) * Eb * delta_inv + M3 * P(0, L) * Eb * delta_inv**2)) + 3 * g2
    D0 = g2 + eps * PSI2; D1 = xg3 + eps * XPSI3
    sT0 = T1(0) + D0 * ZETA2 / (4 * PI**2 * L)
    sT1 = T1(1, 1) + D1 * ZETA2 / (4 * PI**2 * L)
    bnd = L * P(0, L) + D0 * ZETA2 / (4 * PI**2 * L)
    Bm1 = arb(3) / 2 * sT0 + sT1 + bnd
    # m >= 2 Gaussian terms (scaled): each <= poly(m lam) e^{-pi (m^2-1) lam^2} <= e^{-3 pi 10^4} * 10^{40}, summed over m <= 60 plus tail
    tiny = (-3 * PI * L**2).exp() * arb(10)**40 * 200
    print(f"Part 2: for lam >= 100, F(lam) <= Pi(100)/100^8 + tiny = {(Bm1 / L**8).upper().str(12)} + {tiny.upper().str(3)}", flush=True)
    # Degree check of the Laurent polynomial (symbolic): top power of lam is 8
    print("Degree check: xg3 contains lam * P_0(lam) * lam^4 with deg P_0 = %d -> lam^%d, divided by lam in D1 zeta2/(4 pi^2 lam): lam^%d"
          % (len(Qexact[0]) - 1, len(Qexact[0]) - 1 + 5, len(Qexact[0]) - 1 + 4))
