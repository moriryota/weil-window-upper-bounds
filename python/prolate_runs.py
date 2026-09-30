"""Prolate-vector numerics for larger μ, with two basis sizes each (convergence check)."""
import sys, time; sys.path.insert(0, 'python')
import mpmath as mp
from prolate_kvector import run
jobs = [(13, 260, 480), (15, 220, 480), (15, 260, 480), (17, 260, 560), (17, 300, 560), (20, 300, 640), (20, 340, 640)]
for mu, N, prec in jobs:
    t = time.time()
    r = run(mu, N=N, prec=prec, nq=N + 40)
    print(f"μ={mu:>3} N={N} prec={prec}  W(k)/||k||²={mp.nstr(r['rayleigh'],6)}  λ_min(even)={mp.nstr(r['lam_min'],6)}  ratio={mp.nstr(r['rayleigh']/r['lam_min'],5)}  "
          f"1-|<k,ξ>|²={mp.nstr(1-r['overlap']**2,4)}  1-χ₂(Fuchs)={mp.nstr(r['one_minus_chi2_fuchs'],4)}  W(k)/(1-χ₂)={mp.nstr(r['rayleigh']/r['one_minus_chi2_fuchs'],4)}  ({time.time()-t:.0f}s)", flush=True)
