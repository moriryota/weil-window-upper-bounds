"""Theorem B via Kaiser–Bessel windows. φ(x) = x²(x² − s) (1 − x²/λ²)^{ν/2} I_ν(β √(1 − x²/λ²)) on [−λ, λ],
β = 2πλ² (band edge at ξ = λ), s fixed by ∫φ = 0 (φ(0) = 0 automatic). k = ℰ(φ)|[λ^{-1},λ].
Expect W(k)/||k||² ≈ poly(μ) e^{−4πμ} (same exponent as the prolate k_λ; Section 6 of the paper)."""
import sys; sys.path.insert(0, 'python')
import mpmath as mp
from flint import arb, ctx
from weil_spectral import WeilSpectral, gauss_legendre
from prolate_kvector import legendre_norm_vals

def run(mu, nu=2, N=180, prec=480, nq=220):
    mp.mp.dps = int(prec * 0.30103) + 10; ctx.prec = prec
    lam = mp.sqrt(mu); a = mp.log(lam); beta = 2 * mp.pi * mu
    I0 = mp.besseli(nu, beta)
    def Phi(x):
        t = 1 - (x / lam)**2
        return t**(mp.mpf(nu) / 2) * mp.besseli(nu, beta * mp.sqrt(t)) / I0 if t > 0 else mp.mpf(0)
    m2 = mp.quad(lambda x: x**2 * Phi(x), [0, 1, lam]); m4 = mp.quad(lambda x: x**4 * Phi(x), [0, 1, lam])
    s = m4 / m2
    phi = lambda x: x**2 * (x**2 - s) * Phi(x)
    g = lambda y: mp.e**(y / 2) * sum(phi(n * mp.e**y) for n in range(1, int(mp.floor(lam / mp.e**y)) + 1))
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

for mu, N in ((5, 140), (7, 140), (11, 180)):
    w = run(mu, N=N)
    ref = mp.e**(-4 * mp.pi * mu)
    print(f"μ={mu:>3} N={N}: W(k_KB)/||k||² = {mp.nstr(w,6)}   e^(-4πμ) = {mp.nstr(ref,4)}   W/e^(-4πμ) = {mp.nstr(w/ref,4)}   ln W = {mp.nstr(mp.log(w),6)}", flush=True)
