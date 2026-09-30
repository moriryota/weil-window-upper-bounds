"""numerical check of Proposition 3.1 of Theorem A for the admissible smooth test function of §4,
phi = h*chi + eps*psi (delta = 1/lam).  Same phi on both sides:
  left : |W(k)| from the spectral Weil form (Legendre basis, as in gauss_kvector.py), k = E(phi)|[-a,a];
  right: 2 S (A0 + A1)^2 with S <= 2(1 + gamma/2 - log(4 pi)/2), A0, A1 from their definitions
         (real-space sums r(y) = e^{y/2} sum_n phi(n e^y) for y < -a; integral over y in [-a-U, -a]).
Self-checks: phi' against a central difference quotient; A0, A1 at two quadrature resolutions and two U.
Truncation direction: cutting the y-integral at -a-U under-estimates A0, A1; the size of the
integrand at the cut is printed so that the omitted part can be judged (it decays super-exponentially)."""
import sys, time; sys.path.insert(0, 'python')
import mpmath as mp
from flint import arb, ctx
from weil_spectral import WeilSpectral, gauss_legendre
from prolate_kvector import legendre_norm_vals

def f(x): return mp.e**(-1 / x) if x > 0 else mp.mpf(0)
def fp(x): return f(x) / x**2 if x > 0 else mp.mpf(0)
def S(x):  # smooth step: 0 for x <= 0, 1 for x >= 1
    if x <= 0: return mp.mpf(0)
    if x >= 1: return mp.mpf(1)
    return f(x) / (f(x) + f(1 - x))
def Sp(x):
    if x <= 0 or x >= 1: return mp.mpf(0)
    d = f(x) + f(1 - x)
    return (fp(x) * f(1 - x) + f(x) * fp(1 - x)) / d**2
def chi0(t): return S(2 - abs(t))            # 1 on [-1,1], 0 outside (-2,2)
def chi0p(t): return -mp.sign(t) * Sp(2 - abs(t))

def make_phi(lam):
    d = 1 / lam; c = lam - 2 * d
    h = lambda x: (mp.pi / 2) * x**2 * (2 * mp.pi * x**2 - 3) * mp.e**(-mp.pi * x**2)
    hp = lambda x: (-2 * mp.pi**3 * x**5 + 7 * mp.pi**2 * x**3 - 3 * mp.pi * x) * mp.e**(-mp.pi * x**2)
    def chi(x):
        return mp.mpf(1) if abs(x) <= c else chi0((x - mp.sign(x) * c) / d)
    def chip(x):
        return mp.mpf(0) if abs(x) <= c else chi0p((x - mp.sign(x) * c) / d) / d
    g = lambda x: x**2 * mp.e**(-1 / (1 - x**2)) if abs(x) < 1 else mp.mpf(0)
    gp = lambda x: (2 * x - 2 * x**3 / (1 - x**2)**2) * mp.e**(-1 / (1 - x**2)) if abs(x) < 1 else mp.mpf(0)
    cg = 2 * mp.quad(g, [0, 0.5, 1])
    eps = 2 * mp.quad(lambda x: h(x) * (1 - chi(x)), [c, lam - d, lam, lam + 5, mp.inf])
    phi = lambda x: h(x) * chi(x) + eps * g(x) / cg
    phip = lambda x: hp(x) * chi(x) + h(x) * chip(x) + eps * gp(x) / cg
    return phi, phip, eps, c, d

def A_values(lam, phi, phip, U, panel, nodes):
    a = mp.log(lam)
    def sums(y):
        ey = mp.e**y; nmax = int(mp.floor(lam / ey))
        s0 = mp.fsum(phi(n * ey) for n in range(1, nmax + 1))
        s1 = mp.fsum(n * ey * phip(n * ey) for n in range(1, nmax + 1))
        r = mp.e**(y / 2) * s0
        return r, r / 2 + mp.e**(y / 2) * s1
    xs, ws = mp.gauss_quadrature(nodes, 'legendre') if hasattr(mp, 'gauss_quadrature') else (None, None)
    if xs is None:
        gx, gw = gauss_legendre(nodes)
        xs = [mp.mpf(x.mid().str(mp.mp.dps, radius=False)) for x in gx]; ws = [mp.mpf(w.mid().str(mp.mp.dps, radius=False)) for w in gw]
    A0 = mp.mpf(0); I1 = mp.mpf(0); last = None
    npan = int(mp.ceil(U / panel))
    for p in range(npan):
        lo, hi = p * panel, min((p + 1) * panel, U); half, mid = (hi - lo) / 2, (hi + lo) / 2
        for x, w in zip(xs, ws):
            u = mid + half * x; r, rp = sums(-a - u); wt = mp.e**((a + u) / 2)
            A0 += w * half * abs(r) * wt; I1 += w * half * abs(rp) * wt
    rEnd, rpEnd = sums(-a - U)
    r0, _ = sums(-a)
    A1 = abs(r0) * mp.e**(a / 2) + I1
    return A0, A1, abs(r0) * mp.e**(a / 2), (abs(rEnd) + abs(rpEnd)) * mp.e**((a + U) / 2)

def W_of_k(mu, phi, N, prec, nq):
    lam = mp.sqrt(mu); a = mp.log(lam)
    g = lambda y: mp.e**(y / 2) * mp.fsum(phi(n * mp.e**y) for n in range(1, int(mp.floor(lam / mp.e**y)) + 1))
    breaks = sorted(set([-a, a] + [a - mp.log(n) for n in range(2, int(mu) + 1) if a - mp.log(n) > -a]))
    gx, gw = gauss_legendre(nq)
    xs = [mp.mpf(x.mid().str(mp.mp.dps, radius=False)) for x in gx]; ws = [mp.mpf(w.mid().str(mp.mp.dps, radius=False)) for w in gw]
    coef = [mp.mpf(0)] * N
    for lo, hi in zip(breaks[:-1], breaks[1:]):
        half, mid = (hi - lo) / 2, (hi + lo) / 2
        for x, w in zip(xs, ws):
            y = mid + half * x; gy = g(y); P = legendre_norm_vals(y / a, N - 1)
            for j in range(N):
                coef[j] += w * half * gy * P[j] / mp.sqrt(a)
    M = WeilSpectral(arb(mu).sqrt().log(), N, prec=prec).matrix()
    cb = [arb(mp.nstr(x, mp.mp.dps - 5)) for x in coef]
    Qv = sum((cb[i] * sum((M[i, j] * cb[j] for j in range(N)), arb(0)) for i in range(N)), arb(0))
    W = mp.mpf(Qv.mid().str(mp.mp.dps, radius=False)); nrm2 = mp.fsum(x**2 for x in coef)
    return W, nrm2

if __name__ == '__main__':
    prec = 480; mp.mp.dps = int(prec * 0.30103) + 10; ctx.prec = prec
    Sb = 2 * (1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2)
    jobs = [(5, 140), (7, 140), (11, 140), (13, 140), (13, 180)] if len(sys.argv) < 2 else [(int(sys.argv[1]), int(sys.argv[2]))]
    for mu, N in jobs:
        t = time.time(); lam = mp.sqrt(mu)
        phi, phip, eps, c, d = make_phi(lam)
        xt = lam - 1.5 * d; fd = (phi(xt + mp.mpf('1e-30')) - phi(xt - mp.mpf('1e-30'))) / mp.mpf('2e-30')
        intphi = 2 * mp.quad(phi, [0, 1, c, lam - d, lam])
        print(f"μ={mu} λ={mp.nstr(lam,6)} δ={mp.nstr(d,4)} ε={mp.nstr(eps,6)} ∫φ={mp.nstr(intphi,3)} "
              f"φ'(λ-1.5δ): formula={mp.nstr(phip(xt),10)} diff-quot={mp.nstr(fd,10)}", flush=True)
        res = {}
        for (U, panel, nodes) in [(4, mp.mpf("0.1"), 16), (5, mp.mpf("0.05"), 24)]:
            A0, A1, bd, tail = A_values(lam, phi, phip, U, panel, nodes)
            res[(U, nodes)] = (A0, A1)
            print(f"   U={U} panel={panel} nodes={nodes}: A0={mp.nstr(A0,8)} A1={mp.nstr(A1,8)} (boundary {mp.nstr(bd,4)}) "
                  f"integrand at cut={mp.nstr(tail,3)}  2S(A0+A1)^2={mp.nstr(2*Sb*(A0+A1)**2,8)}", flush=True)
        W, nrm2 = W_of_k(mu, phi, N, prec, N + 40)
        A0, A1 = res[(5, 24)]; bound = 2 * Sb * (A0 + A1)**2
        print(f"   N={N}: W(k)={mp.nstr(W,8)} ||k||²={mp.nstr(nrm2,8)} W/||k||²={mp.nstr(W/nrm2,6)}  "
              f"bound/|W|={mp.nstr(bound/abs(W),6)}  W/||k||² / e^(-2πμ)={mp.nstr(W/nrm2/mp.e**(-2*mp.pi*mu),5)}  ({time.time()-t:.0f}s)", flush=True)
