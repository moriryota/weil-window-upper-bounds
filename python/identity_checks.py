"""numerical checks of the EQUALITIES used in Theorem A (verification layer 2 of the ledger).
  (a) h^ = h  with  phi^(xi) = int phi(x) e^{2 pi i x xi} dx.
  (b) Lemma 2.1(ii) Poisson form: e^{y/2} sum_n phi(n e^y) = e^{-y/2} sum_m phi^(m e^{-y})   (phi = h).
  (c) Lemma 2.2: e^(z) = zeta(1/2 + i z) Phi(z),  f^(z) = int f(y) e^{izy} dy,  Phi(z) = int_0^oo phi(v) v^{-1/2+iz} dv
      (phi = h; z real, complex in the strip, and z = gamma_1 where both sides vanish).
  (d) Proposition 3.1 identity for the smooth phi of §4 (mu = 5):  W(k) = sum_rho r^(g) r^(-g) = 2 sum_n |r^(t_n)|^2
      (zeros on the line up to height T, as returned by mpmath), compared with W(k) from the spectral Weil form
      (smooth_A_check.out: W(k) = 1.3836706e-9 at N = 140).  The tail beyond T is estimated by the boundary-term
      model |r^(t)| ~ |r(-a)| e^{a/2} / t."""
import sys, time; sys.path.insert(0, 'python')
import mpmath as mp
from weil_spectral import gauss_legendre
from smooth_A_check import make_phi

mp.mp.dps = 40
h = lambda x: (mp.pi / 2) * x**2 * (2 * mp.pi * x**2 - 3) * mp.e**(-mp.pi * x**2)

def ft(phi, xi, lim):
    return 2 * mp.quad(lambda x: phi(x) * mp.cos(2 * mp.pi * x * xi), mp.linspace(0, lim, 9))

print("(a) h^ = h")
for xi in ['0.3', '1', '1.7', '2.5']:
    xi = mp.mpf(xi); print(f"   xi={xi}: h^={mp.nstr(ft(h, xi, 12), 15)}  h={mp.nstr(h(xi), 15)}")

print("(b) Poisson form of e (phi = h)")
for y in ['-2', '-0.5', '0', '0.7']:
    y = mp.mpf(y)
    L = mp.e**(y / 2) * mp.nsum(lambda n: h(n * mp.e**y), [1, mp.inf])
    R = mp.e**(-y / 2) * mp.nsum(lambda m: h(m * mp.e**(-y)), [1, mp.inf])
    print(f"   y={y}: real-space={mp.nstr(L, 15)}  Poisson={mp.nstr(R, 15)}")

print("(c) e^(z) = zeta(1/2+iz) Phi(z)   (phi = h)")
eh = lambda y: mp.e**(y / 2) * mp.nsum(lambda n: h(n * mp.e**y), [1, mp.inf]) if y > -1 else \
     mp.e**(-y / 2) * mp.nsum(lambda m: h(m * mp.e**(-y)), [1, mp.inf])
g1 = mp.im(mp.zetazero(1))
for z in [mp.mpf(3), mp.mpc(5, '0.3'), mp.mpc(2, '-0.45'), g1]:
    L = mp.quad(lambda y: eh(y) * mp.e**(1j * z * y), mp.linspace(-4, 3, 29))
    Phi = mp.quad(lambda v: h(v) * v**(-mp.mpf(1) / 2 + 1j * z), [0, 1, 2, 4, 8])
    R = mp.zeta(mp.mpf(1) / 2 + 1j * z) * Phi
    print(f"   z={mp.nstr(z, 8)}: e^={mp.nstr(L, 12)}  zeta*Phi={mp.nstr(R, 12)}")

print("(d) W(k) = 2 sum_n |r^(t_n)|^2, smooth phi of §4, mu = 5")
t0 = time.time(); mu = 5; lam = mp.sqrt(mu); a = mp.log(lam)
phi, phip, eps, c, d = make_phi(lam)
gx, gw = gauss_legendre(16)
xs = [mp.mpf(x.mid().str(40, radius=False)) for x in gx]; ws = [mp.mpf(w.mid().str(40, radius=False)) for w in gw]
U, panel = mp.mpf('4.5'), mp.mpf('0.01'); nodes = []
for p in range(int(U / panel)):
    lo, hi = p * panel, (p + 1) * panel; half, mid = (hi - lo) / 2, (hi + lo) / 2
    for x, w in zip(xs, ws):
        y = -a - (mid + half * x); ey = mp.e**y
        r = mp.e**(y / 2) * mp.fsum(phi(n * ey) for n in range(1, int(mp.floor(lam / ey)) + 1))
        nodes.append((y, w * half * r))
ra = mp.e**(-a / 2) * mp.fsum(phi(n / lam) for n in range(1, int(mp.floor(lam * lam)) + 1))
print(f"   r sampled at {len(nodes)} nodes ({time.time()-t0:.0f}s); |r(-a)| e^(a/2) = {mp.nstr(abs(ra) * mp.e**(a / 2), 6)}")
rhat = lambda t: mp.fsum(wr * mp.expj(t * y) for y, wr in nodes)
mp.mp.dps = 20
zeros = [mp.im(mp.zetazero(n)) for n in range(1, 1001)]
mp.mp.dps = 40
s = mp.mpf(0); B = abs(ra) * mp.e**(a / 2)
for n, t in enumerate(zeros, 1):
    s += 2 * abs(rhat(t))**2
    if n in (10, 100, 250, 500, 1000):
        tail = 2 * B**2 * mp.quad(lambda x: mp.log(x / (2 * mp.pi)) / (2 * mp.pi) / x**2, [t, mp.inf])
        print(f"   zeros<= {n} (T={mp.nstr(t, 6)}): partial sum = {mp.nstr(s, 10)}   + tail model {mp.nstr(tail, 3)} = {mp.nstr(s + tail, 10)}", flush=True)
print(f"   spectral W(k) (N=140) = 1.3836706e-9   ({time.time()-t0:.0f}s)")
