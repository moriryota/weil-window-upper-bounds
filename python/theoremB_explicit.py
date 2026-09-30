"""Explicit constants for Theorem B (Kaiser-Bessel window phi_B), valid for all mu = lam^2 >= 5.

Everything that enters the proof is computed in ball arithmetic (python-flint / Arb):
  * g(z) = sqrt(z) e^{-z} I_2(z) at the points used (Lemma 5.5: g is nondecreasing, g <= 1/sqrt(2 pi));
  * the integrals D_low and c_B^2 (acb.integral; the fractional power (1 - x^2/5)^{3/4} is written with
    square roots that receive the analytic flag, so that Arb verifies that no branch cut is touched);
  * the coefficients of Q(lam) = sum_k q_k lam^k (Lemma 5.8), as Arb balls, power by power.
The rounded constants printed in the paper are then compared with these balls, in the safe direction:
  lower bounds (g, D, c_B^2) must lie below the ball, upper bounds (sigma, Q/lam^23, K_B) above it.
A final part compares the bounds with the true functions numerically (not part of the proof)."""
from flint import arb, acb, ctx
ctx.prec = 200
PI = arb.pi()

def g(z):  # z: arb > 0
    return z.sqrt() * (-z).exp() * acb(z).bessel_i(2).real

def integral(f, a, b):
    return acb.integral(f, a, b).real

def pow34(u, an):  # u^{3/4} = sqrt(u) * sqrt(sqrt(u)), principal branch, analytic flag forwarded
    r = u.sqrt(analytic=an)
    return r * r.sqrt(analytic=an)

def check(name, ball, claim, kind):
    """kind 'lower': claim <= ball; kind 'upper': ball <= claim."""
    ok = (arb(claim) <= ball.lower()) if kind == 'lower' else (ball.upper() <= arb(claim))
    print(f"  {name}: ball = {ball.str(12)};  paper: {'>=' if kind == 'lower' else '<='} {claim}  -> {'OK' if ok else 'FAIL'}")
    assert ok
    return ok

LAM0SQ = arb(5); LAM0 = LAM0SQ.sqrt(); BETA0 = 2 * PI * LAM0SQ
ETA = arb(1) / 10
S_BOUND = arb('0.046192')
# constants as printed in the paper
SIGMA_BAR = '0.66096'; GD_LOW = '0.9210599'; D_LOW = '0.1149707'; GS_LOW = '0.93246'
CB2 = '6.549e-6'; G0_LOW = '0.375467'; QRATIO = '310.72'; KB = '1.362e9'

print("Lemma 5.7 (sigma_bar, c_B^2), ball arithmetic:")
X = arb(3) / 2
zD = 2 * PI * LAM0 * (LAM0SQ - X * X).sqrt()
print(f"  z_D = {zD.str(10)}")
check("sqrt(2pi) g(z_D)", (2 * PI).sqrt() * g(zD), GD_LOW, 'lower')
gD = arb(GD_LOW)
D = integral(lambda x, an: x**2 * pow34(1 - x**2 / 5, an) * (-acb.pi() * x**2 - acb.pi() * x**4 / 5).exp(), -X, X) * gD
check("D (denominator of sigma, lower bound)", D, D_LOW, 'lower')
N_up = 3 / (4 * PI**2)
check("sigma <= (3/(4 pi^2)) / D_low", N_up / arb(D_LOW), SIGMA_BAR, 'upper')
print(f"  e^(-2 eta) = {(-2 * ETA).exp().str(8)} > sigma_bar: {(-2 * ETA).exp().lower() > arb(SIGMA_BAR)}")
zs = 2 * PI * LAM0 * (LAM0SQ - (2 * ETA).exp()).sqrt()
print(f"  z_* = {zs.str(10)}")
check("sqrt(2pi) g(z_*)", (2 * PI).sqrt() * g(zs), GS_LOW, 'lower')
sb = acb(SIGMA_BAR); gs = acb(GS_LOW)
def integrand_cB(y, an):
    x = y.exp()
    phi_low = gs * x**2 * (x**2 - sb) * pow34(1 - x**2 / 5, an) * (-acb.pi() * x**2 - acb.pi() * x**4 / 5).exp()
    return y.exp() * phi_low**2
cB2 = integral(integrand_cB, -ETA, ETA)
check("c_B^2 (lower bound for ||k_B||^2)", cB2, CB2, 'lower')

print("Lemma 5.8 (Q), ball arithmetic:")
check("g(beta0), beta0 = 10 pi", g(BETA0), G0_LOW, 'lower')
# polynomial in lam: dict power -> arb coefficient; beta^p = (2 pi)^p lam^(2p)
def mono(coef, beta_pow, lam_pow=0):
    k2 = 2 * beta_pow + lam_pow          # beta_pow may be a half-integer (as a Fraction-like float * 2)
    k = int(round(k2))
    assert abs(k2 - k) < 1e-12
    return {k: coef * (2 * PI) ** arb(beta_pow)}
def add(*ds):
    out = {}
    for d in ds:
        for k, v in d.items():
            out[k] = out.get(k, arb(0)) + v
    return out
def scale(d, c, lam_pow=0):
    return {k + lam_pow: v * c for k, v in d.items()}
H = arb(1) / 2
G2 = [(-1, 0, 7), (1, 2, 9)]                 # a stored as 2a (half-integers)
G4 = [(3, 0, 9), (-6, 2, 11), (1, 4, 13)]
def wd(terms):
    out = []
    for c, i, a2 in terms:
        if i: out.append((c * i, i, a2))
        out.append((-c, i + 2, a2 + 2))
    return out
def fa(a): return 1 / (2**a * (a + 1).gamma())
def ka(a): return (2 / arb(3).sqrt()) ** a
def R(terms):
    parts = []
    for c, i, a2 in terms:
        a = arb(a2) / 2; c = abs(c)
        parts.append(mono(c * fa(a) * (2 ** (i + 1) - 1) / (i + 1), i + 1))
        parts.append(mono(c * ka(a) * 2 ** (i - a + 1) / (a - i - 1), i - a2 / 2 + 1))
        parts.append(mono(c * ka(a) * ((a - i).zeta() - 1) / (a - i - 1), i - a2 / 2 + 1))
    return add(*parts)
def P(terms):
    parts = []
    for c, i, a2 in terms:
        a = arb(a2) / 2; c = abs(c)
        parts.append(mono(c * fa(a), i))
        parts.append(mono(c * ka(a) * ((a - i).zeta() - 1), i - a2 / 2))
    return add(*parts)
sig = arb(SIGMA_BAR); G0 = arb(G0_LOW)
inner = add(scale(add(scale(R(G4), 1, 4), scale(R(G2), sig, 2)), 3 / (4 * PI), -1),
            scale(add(scale(R(wd(G4)), 1, 4), scale(R(wd(G2)), sig, 2)), 1 / (2 * PI), -1),
            scale(add(scale(P(G4), 1, 4), scale(P(G2), sig, 2)), arb(1), 1))
pre_c = (2 * PI).sqrt() * (2 * PI) ** (arb(5) / 2) / G0      # pre = pre_c * lam^6
Q = scale(inner, pre_c, 6)
powers = sorted(Q)
print(f"  powers of lam in Q: {powers}")
for k in powers:
    print(f"    q_{k:2d} = {Q[k].str(15)}   positive: {Q[k].lower() > 0}")
assert all(Q[k].lower() > 0 for k in powers) and max(powers) == 23
def Qval(lam): return sum((Q[k] * lam**k for k in powers), arb(0))
ratio = Qval(LAM0) / LAM0**23
check("Q(sqrt5)/5^11.5 (= max of Q/lam^23 over lam >= sqrt5)", ratio, QRATIO, 'upper')
for mu in [7, 11, 17, 30]:
    lam = arb(mu).sqrt(); print(f"    mu={mu:2d}: Q/lam^23 = {(Qval(lam) / lam**23).str(10)}")
print("Theorem B:")
K = 2 * S_BOUND * arb(QRATIO)**2 / arb(CB2)
check("K_B = 2 S (310.72)^2 / 6.549e-6", K, KB, 'upper')
r = arb('1.362') / arb('1.563') * arb(5)**15 * (-10 * PI).exp()
check("Theorem B / Theorem A at mu = 5", r, '0.001', 'upper')

# ---- direction checks against the true functions (numerical, not part of the proof) ----
import mpmath
mpmath.mp.dps = 40
def Fa(a, zz): return mpmath.hyp0f1(a + 1, zz / 4) / (2**a * mpmath.gamma(a + 1))
G2n = [(-1, 0, 3.5), (1, 2, 4.5)]; G4n = [(3, 0, 4.5), (-6, 2, 5.5), (1, 4, 6.5)]
def wdn(ts):
    out = []
    for c, i, a in ts:
        if i: out.append((c * i, i, a))
        out.append((-c, i + 2, a + 1))
    return out
def ev(ts, w, b): return sum(c * w**i * Fa(mpmath.mpf(a), b**2 - w**2) for c, i, a in ts)
def env(ts, w, b):
    tot = 0
    for c, i, a in ts:
        a = mpmath.mpf(a)
        tot += abs(c) * abs(w)**i * (1 / (2**a * mpmath.gamma(a + 1)) if abs(w) <= 2 * b else (2 / mpmath.sqrt(3))**a * abs(w)**(-a))
    return tot
print("direction checks against the true functions (numerical; omega in [beta, 50 beta], 801 points):")
for mu in [5, 11, 25, 60]:
    lam = mpmath.sqrt(mu); b = 2 * mpmath.pi * mu; Ib = mpmath.besseli(2, b)
    Phi = lambda t: (1 - t**2) * mpmath.besseli(2, b * mpmath.sqrt(1 - t**2)) / Ib
    sigt = lam**2 * mpmath.quad(lambda t: t**4 * Phi(t), [0, 1]) / mpmath.quad(lambda t: t**2 * Phi(t), [0, 1])
    pre_true = lam * mpmath.sqrt(2 * mpmath.pi) * b**2 / Ib
    pre_bd = lam * mpmath.sqrt(2 * mpmath.pi) * b**2.5 * mpmath.e**(-b) / mpmath.mpf(G0_LOW)
    s_bar = mpmath.mpf(SIGMA_BAR); w0 = w1 = 0
    for j in range(801):
        w = b * (1 + 49 * mpmath.mpf(j) / 800)
        t0 = abs(pre_true * (lam**4 * ev(G4n, w, b) + sigt * lam**2 * ev(G2n, w, b)))
        t1 = abs(pre_true * (lam**4 * ev(wdn(G4n), w, b) + sigt * lam**2 * ev(wdn(G2n), w, b)))
        w0 = max(w0, t0 / (pre_bd * (lam**4 * env(G4n, w, b) + s_bar * lam**2 * env(G2n, w, b))))
        w1 = max(w1, t1 / (pre_bd * (lam**4 * env(wdn(G4n), w, b) + s_bar * lam**2 * env(wdn(G2n), w, b))))
    phiB = lambda x: x**2 * (x**2 - sigt) * Phi(x / lam) if abs(x) < lam else 0
    eB = lambda y: mpmath.e**(y / 2) * sum(phiB(n * mpmath.e**y) for n in range(1, int(lam * mpmath.e**0.1) + 2))
    kk = mpmath.quad(lambda y: eB(y)**2, [-0.1, 0, 0.1])
    print(f"  mu={mu:2d}: sigma = {mpmath.nstr(sigt, 6)} (<= {SIGMA_BAR});  max |phihat|/envelope = {mpmath.nstr(w0, 4)};  "
          f"max |xi phihat'|/envelope = {mpmath.nstr(w1, 4)};  int e_B^2 = {mpmath.nstr(kk, 6)} (>= {CB2})")
