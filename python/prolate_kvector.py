"""numerical study. Build the CCM/Connes educated guess k_λ = ℰ(h_λ)|[λ^{-1},λ] from prolate
spheroidal functions and evaluate the Weil form on it with the spectral tool (weil_spectral.py).

Conventions (CCM 2025 §7, Connes 2026 §6): μ = λ², c = 2πμ,
  h_{n,λ}(x) = ψ_n(x/λ)/√λ on [-λ, λ], ψ_n the n-th PSWF of bandwidth c (eigenfunctions of
  -d/dz((1-z²)d/dz) + c² z² on [-1, 1]), normalised in L², sign with ψ_n(0) > 0 (n = 0, 4);
  h_λ = α h_{0,λ} + β h_{4,λ} with ∫ h_λ = 0;  k_λ(u) = u^{1/2} Σ_{n≥1} h_λ(n u),  u ∈ [λ^{-1}, λ].
In the logarithmic coordinate y = log u ∈ [-a, a], a = log λ = ½ log μ, the function is
  g(y) = e^{y/2} Σ_{n ≤ λ e^{-y}} h_λ(n e^y),
and the Weil form is our Q (L²(dy) = L²(d*u)). g has (tiny) jumps at y = a - log n; the projection onto
Legendre polynomials is computed with Gauss–Legendre on the pieces between these points."""
import sys, math
sys.path.insert(0, 'python')
import mpmath
from flint import arb, arb_mat, ctx
from weil_spectral import WeilSpectral, gauss_legendre, legendre_values

mp = mpmath


def pswf_even(c, K, which=(0, 2)):
    """Even PSWFs ψ_{2m} for m in `which` (m=0 → ψ_0, m=2 → ψ_4): coefficients in normalised Legendre
    polynomials P̄_k (k even, k < 2K), from the symmetric tridiagonal matrix of the prolate operator."""
    ks = [2 * i for i in range(K)]
    def a(k):  # z P̄_k = a(k+1) P̄_{k+1} + a(k) P̄_{k-1}
        return mp.mpf(k) / mp.sqrt((2 * k - 1) * (2 * k + 1)) if k > 0 else mp.mpf(0)
    A = mp.matrix(K, K)
    for i, k in enumerate(ks):
        A[i, i] = k * (k + 1) + c**2 * (a(k + 1)**2 + a(k)**2)
        if i + 1 < K:
            A[i, i + 1] = A[i + 1, i] = c**2 * a(k + 1) * a(k + 2)
    E, V = mp.eigsy(A)
    order = sorted(range(K), key=lambda i: E[i])
    out = {}
    for m in which:
        j = order[m]
        coef = [V[i, j] for i in range(K)]
        # sign: ψ(0) > 0;  P̄_k(0) = sqrt((2k+1)/2) P_k(0)
        val0 = sum(coef[i] * mp.sqrt((2 * ks[i] + 1) / mp.mpf(2)) * mp.legendre(ks[i], 0) for i in range(K))
        if val0 < 0:
            coef = [-x for x in coef]
        out[m] = (E[j], coef)
    return ks, out


def legendre_norm_vals(z, kmax):
    """P̄_k(z) for k ≤ kmax (mpmath)."""
    P = [mp.mpf(1), z]
    for n in range(1, kmax):
        P.append(((2 * n + 1) * z * P[n] - n * P[n - 1]) / (n + 1))
    return [P[k] * mp.sqrt((2 * k + 1) / mp.mpf(2)) for k in range(kmax + 1)]


def run(mu, N=140, K=None, prec=480, nq=60):
    mp.mp.dps = int(prec * 0.30103) + 10
    ctx.prec = prec
    lam = mp.sqrt(mu); a = mp.log(lam); c = 2 * mp.pi * mu
    K = K or int(float(c) / 2) + 60
    ks, ps = pswf_even(c, K)
    # h_{n,λ}(x) = ψ(x/λ)/√λ ;  ∫ h_{n,λ} dx = √λ ∫_{-1}^{1} ψ = √λ · coef_0 · √2   (P̄_0 = 1/√2)
    I0 = mp.sqrt(lam) * ps[0][1][0] * mp.sqrt(2)
    I4 = mp.sqrt(lam) * ps[2][1][0] * mp.sqrt(2)
    alpha, beta = I4, -I0                      # α I0 + β I4 = 0
    kmax = ks[-1]

    def h_lam(x):
        if abs(x) >= lam:
            return mp.mpf(0)
        Pz = legendre_norm_vals(x / lam, kmax)
        s0 = sum(ps[0][1][i] * Pz[k] for i, k in enumerate(ks))
        s4 = sum(ps[2][1][i] * Pz[k] for i, k in enumerate(ks))
        return (alpha * s0 + beta * s4) / mp.sqrt(lam)

    def g(y):
        u = mp.e**y
        nmax = int(mp.floor(lam / u))
        return mp.e**(y / 2) * sum(h_lam(n * u) for n in range(1, nmax + 1))

    # projection onto φ_j(y) = sqrt((2j+1)/(2a)) P_j(y/a), piecewise Gauss between jump points a - log n
    breaks = sorted(set([-a, a] + [a - mp.log(n) for n in range(2, int(mu) + 1) if a - mp.log(n) > -a]))
    xs, ws = gauss_legendre(nq)
    xs = [mp.mpf(x.mid().str(mp.mp.dps, radius=False)) for x in xs]
    ws = [mp.mpf(w.mid().str(mp.mp.dps, radius=False)) for w in ws]
    coef = [mp.mpf(0)] * N
    norm2 = mp.mpf(0)
    for lo, hi in zip(breaks[:-1], breaks[1:]):
        half, mid = (hi - lo) / 2, (hi + lo) / 2
        for x, w in zip(xs, ws):
            y = mid + half * x
            gy = g(y)
            P = legendre_norm_vals(y / a, N - 1)
            for j in range(N):
                coef[j] += w * half * gy * P[j] / mp.sqrt(a)   # φ_j = P̄_j(y/a)/sqrt(a)
            norm2 += w * half * gy**2
    proj2 = sum(x**2 for x in coef)
    # Weil form on the projection
    W = WeilSpectral(arb(mu).sqrt().log(), N, prec=prec)   # exact window (a float here spoils near-radical vectors)
    M = W.matrix()
    cb = [arb(mp.nstr(x, mp.mp.dps - 5)) for x in coef]
    Qv = arb(0)
    for i in range(N):
        row = arb(0)
        for j in range(N):
            row += M[i, j] * cb[j]
        Qv += cb[i] * row
    Qv = mp.mpf(Qv.mid().str(mp.mp.dps, radius=False))
    rq = Qv / proj2
    # lowest even eigenpair of Q for comparison, and overlap with the projected k_λ
    idx = [j for j in range(N) if j % 2 == 0]
    B = mp.matrix(len(idx), len(idx))
    for p, i in enumerate(idx):
        for q, j in enumerate(idx):
            B[p, q] = mp.mpf(M[i, j].mid().str(mp.mp.dps, radius=False))
    E, V = mp.eigsy(B)
    k0 = min(range(len(idx)), key=lambda t: E[t])
    ov = sum(V[p, k0] * coef[i] for p, i in enumerate(idx)) / mp.sqrt(proj2)
    odd_mass = sum(coef[j]**2 for j in range(N) if j % 2 == 1) / proj2
    fuchs = (mp.mpf(2)**14 / 3) * mp.sqrt(2) * mp.pi**5 * mp.e**(-4 * mp.pi * mu + mp.mpf(9) / 2 * mp.log(mu))
    return dict(mu=mu, a=float(a), rayleigh=rq, lam_min=E[k0], overlap=ov, proj_loss=1 - proj2 / norm2,
                odd_mass=odd_mass, one_minus_chi2_fuchs=fuchs, chi_eigs=(ps[0][0], ps[2][0]))


if __name__ == '__main__':
    for mu in (5, 7, 11):
        r = run(mu)
        print(f"μ={r['mu']:>3}  a={r['a']:.4f}  W(k)/||k||²={mp.nstr(r['rayleigh'],6)}  λ_min(even,N=140)={mp.nstr(r['lam_min'],6)}  "
              f"ratio={mp.nstr(r['rayleigh']/r['lam_min'],4)}  |<k,ξ>|={mp.nstr(abs(r['overlap']),12)}  "
              f"1-χ₂(Fuchs)={mp.nstr(r['one_minus_chi2_fuchs'],4)}  odd mass={mp.nstr(r['odd_mass'],3)}  proj loss={mp.nstr(r['proj_loss'],3)}", flush=True)
