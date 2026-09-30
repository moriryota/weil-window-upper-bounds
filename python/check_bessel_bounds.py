"""checks for Theorem B.
(1) Test of the (false) uniform bound |J_a(w)| <= sqrt(2/pi) w^{-1/2} for all a >= 1/2: compute sup_w sqrt(w)|J_a(w)|.
(2) Replacement bounds (DLMF 10.14.1: |J_a(x)| <= 1 for a >= 0; 10.14.4: |J_a(x)| <= (x/2)^a / Gamma(a+1) for a >= -1/2): test.
(3) Lemma 3.3 domination: sup_{|x|<=lam} Phi_beta(x/lam)/I_2(beta) * e^{pi x^2} (draft: bounded)
    versus the simpler bound sup I_2(beta - pi x^2)/I_2(beta) * e^{pi x^2} (grows like sqrt(beta))."""
import mpmath as mp
mp.mp.dps = 30
print("(1),(2)")
for al in [0.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5]:
    ws = [mp.mpf(i) / 50 for i in range(1, 5001)]  # w in (0, 100]
    s1 = max(mp.sqrt(w) * abs(mp.besselj(al, w)) for w in ws)
    s2 = max(abs(mp.besselj(al, w)) for w in ws)
    s3 = max(abs(mp.besselj(al, w)) / ((w / 2)**al / mp.gamma(al + 1)) for w in ws)
    print(f"   a={al}: sup sqrt(w)|J| = {mp.nstr(s1,6)} (claimed <= {mp.nstr(mp.sqrt(2/mp.pi),6)})   sup|J| = {mp.nstr(s2,6)}   "
          f"sup |J|/((w/2)^a/Gamma(a+1)) = {mp.nstr(s3,6)}", flush=True)
print("(3)")
for mu in [5, 13, 50, 200, 1000]:
    lam = mp.sqrt(mu); beta = 2 * mp.pi * mu; I0 = mp.besseli(2, beta)
    xs = [lam * k / 400 for k in range(0, 401)]
    d = max((1 - (x / lam)**2) * mp.besseli(2, beta * mp.sqrt(1 - (x / lam)**2)) / I0 * mp.e**(mp.pi * x * x) for x in xs)
    g = max(mp.besseli(2, beta - mp.pi * x * x) / I0 * mp.e**(mp.pi * x * x) for x in xs)
    print(f"   mu={mu}: sup Phi/I*e^(pi x^2) = {mp.nstr(d,6)}   sup I(beta-pi x^2)/I(beta)*e^(pi x^2) = {mp.nstr(g,6)}   "
          f"sqrt(beta)={mp.nstr(mp.sqrt(beta),4)}", flush=True)
print("(4) monotonicity of g(z) = e^{-z} sqrt(z) I_2(z) (needed for I_2(beta-d)/I_2(beta) <= sqrt(2) e^{-d}, 0 <= d <= beta/2)")
zs = [mp.mpf(k) / 20 for k in range(1, 40001)]   # z in (0, 2000]
gs = [mp.e**(-z) * mp.sqrt(z) * mp.besseli(2, z) for z in zs]
bad = [zs[i] for i in range(1, len(zs)) if gs[i] < gs[i - 1]]
print(f"   z in (0,2000], step 0.05: decreasing steps = {len(bad)};  g(2000) = {mp.nstr(gs[-1],10)}, 1/sqrt(2 pi) = {mp.nstr(1/mp.sqrt(2*mp.pi),10)}")
