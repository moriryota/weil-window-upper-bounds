"""numerical check of Theorem A (easy version): φ = Riemann's h(x) = (π/2) x² (2πx² − 3) e^{−πx²},
sharply truncated to [−λ, λ]; k = ℰ(φ)|[λ^{-1},λ]. Expect W(k)/||k||² ≈ poly · e^{−2πμ}."""
import sys; sys.path.insert(0, 'python')
import mpmath as mp
from flint import arb, ctx
from weil_spectral import WeilSpectral, gauss_legendre
from prolate_kvector import legendre_norm_vals

def run(mu, N=140, prec=480, nq=180):
    mp.mp.dps = int(prec * 0.30103) + 10; ctx.prec = prec
    lam = mp.sqrt(mu); a = mp.log(lam)
    h = lambda x: (mp.pi / 2) * x**2 * (2 * mp.pi * x**2 - 3) * mp.e**(-mp.pi * x**2) if abs(x) < lam else mp.mpf(0)
    g = lambda y: mp.e**(y / 2) * sum(h(n * mp.e**y) for n in range(1, int(mp.floor(lam / mp.e**y)) + 1))
    breaks = sorted(set([-a, a] + [a - mp.log(n) for n in range(2, int(mu) + 1) if a - mp.log(n) > -a]))
    xs, ws = gauss_legendre(nq)
    xs = [mp.mpf(x.mid().str(mp.mp.dps, radius=False)) for x in xs]; ws = [mp.mpf(w.mid().str(mp.mp.dps, radius=False)) for w in ws]
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
    return mp.mpf(Qv.mid().str(mp.mp.dps, radius=False)) / sum(x**2 for x in coef)

for mu in (5, 7, 11, 13):
    w = run(mu)
    print(f"μ={mu:>3}: W(k_h)/||k_h||² = {mp.nstr(w,6)}   e^(-2πμ) = {mp.nstr(mp.e**(-2*mp.pi*mu),4)}   ratio = {mp.nstr(w/mp.e**(-2*mp.pi*mu),4)}   ln W = {mp.nstr(mp.log(w),6)}", flush=True)
