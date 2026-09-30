"""checks for B2 (two-sided bounds for I_nu, nu = 2) and B5 (domination constant).
B2 upper: I_nu(z) <= e^z / sqrt(2 pi z)  (nu >= 1/2, z > 0)
B2 lower: I_nu(z) >= c_nu e^z / sqrt(z)  (z >= 1),  c_nu = e^{-1} 2^{-nu} / (sqrt(pi) Gamma(nu + 3/2))
B5: for beta >= 2 and 0 <= d <= beta/2:  I_2(beta - d)/I_2(beta) <= e^{-d} sqrt(beta/(beta-d)) / (sqrt(2 pi) c_2) <= C_dom e^{-d},
    C_dom = sqrt(2) / (sqrt(2 pi) c_2)."""
import mpmath as mp
mp.mp.dps = 30
nu = 2
c2 = mp.e**-1 * mp.mpf(2)**-nu / (mp.sqrt(mp.pi) * mp.gamma(nu + mp.mpf(3) / 2))
Cdom = mp.sqrt(2) / (mp.sqrt(2 * mp.pi) * c2)
print(f"c_2 = {mp.nstr(c2,8)}   C_dom = {mp.nstr(Cdom,8)}")
zs = [mp.mpf(k) / 20 for k in range(1, 40001)]
up = max(mp.besseli(nu, z) * mp.sqrt(2 * mp.pi * z) * mp.e**(-z) for z in zs)
lo = min(mp.besseli(nu, z) * mp.sqrt(z) * mp.e**(-z) for z in zs if z >= 1)
print(f"z in (0,2000]: max I_2 sqrt(2 pi z) e^-z = {mp.nstr(up,10)} (<= 1)   min_(z>=1) I_2 sqrt(z) e^-z = {mp.nstr(lo,10)} (>= c_2)")
worst = mp.mpf(0)
for beta in [2, 5, 10, 31.4, 100, 1000]:
    beta = mp.mpf(beta)
    for j in range(0, 201):
        d = beta / 2 * j / 200
        worst = max(worst, mp.besseli(nu, beta - d) / mp.besseli(nu, beta) * mp.e**d)
print(f"max over beta in {{2,...,1000}}, d in [0, beta/2] of I_2(beta-d)/I_2(beta) e^d = {mp.nstr(worst,8)} (<= C_dom)")
