"""large-xi decay of phi^ and xi*phi^' for the Kaiser-Bessel phi of Theorem B (nu = 2, mu = 5).
An earlier draft claimed |phi^| + |xi phi^'| <= C (1+|xi|)^{-3}.  Expected from phi ~ (lam - x)^2 at the
endpoint: phi^ ~ xi^{-3} but xi phi^' ~ xi^{-2}.  Closed forms (Lemma 2.1) from Lemma B1 (Sonine-Gegenbauer); re-checked here against a direct Fourier transform at xi = 3 lam.
Printed: max over a window of one oscillation period of xi^3 |phi^| and xi^2 |xi phi^'|."""
import mpmath as mp
mp.mp.dps = 50
mu = mp.mpf(5); lam = mp.sqrt(mu); beta = 2 * mp.pi * mu; I_beta = mp.besseli(2, beta)
Phi = lambda t: (1 - t**2) * mp.besseli(2, beta * mp.sqrt(1 - t**2)) / I_beta
s_val = lam**2 * mp.quad(lambda t: t**4 * Phi(t), [0, 1]) / mp.quad(lambda t: t**2 * Phi(t), [0, 1])
phi = lambda x: x**2 * (x**2 - s_val) * Phi(x / lam)
def F(arg, al):
    w = mp.sqrt(-arg); return mp.besselj(al, w) / w**al
def hat_phi(xi):
    om = 2 * mp.pi * lam * xi; arg = beta**2 - om**2
    d2 = mp.sqrt(2 * mp.pi) * beta**2 * (-F(arg, 3.5) + om**2 * F(arg, 4.5))
    d4 = mp.sqrt(2 * mp.pi) * beta**2 * (3 * F(arg, 4.5) - 6 * om**2 * F(arg, 5.5) + om**4 * F(arg, 6.5))
    return (lam / I_beta) * (lam**4 * d4 + s_val * lam**2 * d2)
def xi_dhat(xi):
    om = 2 * mp.pi * lam * xi; arg = beta**2 - om**2
    d3 = mp.sqrt(2 * mp.pi) * beta**2 * (3 * om * F(arg, 4.5) - om**3 * F(arg, 5.5))
    d5 = mp.sqrt(2 * mp.pi) * beta**2 * (-15 * om * F(arg, 5.5) + 10 * om**3 * F(arg, 6.5) - om**5 * F(arg, 7.5))
    return om * (lam / I_beta) * (lam**4 * d5 + s_val * lam**2 * d3)
xi0 = 3 * lam
direct = 2 * mp.quad(lambda x: phi(x) * mp.cos(2 * mp.pi * x * xi0), mp.linspace(0, lam, 9))
h = mp.mpf('1e-15'); fd = xi0 * (hat_phi(xi0 + h) - hat_phi(xi0 - h)) / (2 * h)
print(f"check at xi=3 lam: closed={mp.nstr(hat_phi(xi0),15)} direct={mp.nstr(direct,15)};  xi phi^'={mp.nstr(xi_dhat(xi0),15)} diff-quot={mp.nstr(fd,15)}")
for K in [5, 20, 80, 320, 1280]:
    xs = [K * lam + lam * j / (40 * 1) / lam for j in range(0, 41)]   # one period in xi is 1/lam; sample it
    a = max(x**3 * abs(hat_phi(x)) for x in xs); b = max(x**2 * abs(xi_dhat(x)) for x in xs); c = max(x**3 * abs(xi_dhat(x)) for x in xs)
    print(f"xi ~ {K:5d} lam:  max xi^3|phi^| = {mp.nstr(a,6)}   max xi^2|xi phi^'| = {mp.nstr(b,6)}   max xi^3|xi phi^'| = {mp.nstr(c,6)}")
