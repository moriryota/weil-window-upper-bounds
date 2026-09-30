"""rigorous lower bound for ||k|| (Theorem A, §4) with ball arithmetic (python-flint arb).

||k||^2 >= int_{-eta}^{eta} |e(y)|^2 dy  (eta <= a),  and on [-eta, eta]:
  |e(y) - e_h(y)| <= E := e^{eta/2} ( |eps| sup|psi| + U_0(b) + e^{eta} int_b^oo |h| ),
  e_h(y) = e^{y/2} sum_n h(n e^y).
Reason: phi - h = -h(1 - chi) + eps psi.  psi lives on |x| < 1, where for |y| <= eta only n = 1 can enter (and only if e^y < 1);
h(1 - chi) lives on |x| >= b, and the points n e^y (spacing e^y >= e^{-eta}) there contribute <= U_0(b) + e^{eta} int_b^oo |h|.
e_h is enclosed on balls covering [-eta, eta] (n <= 12; the tail n >= 13 is bounded by 12 * sup_{x >= 11} |h| crude,
i.e. sum_{n>=13} |h(n e^y)| <= sum_{n>=13} 20 n^4 e^{-pi n^2 e^{-2 eta}}, added as a ball radius).
Output: c0^2 = sum over balls of width * (max(0, min|e_h| - E))^2, rigorous given E (E from theoremA_explicit.bound's pieces)."""
import sys; sys.path.insert(0, 'python')
from flint import arb, ctx
import mpmath as mp
from theoremA_explicit import U, tail

ctx.prec = 200
def h_arb(x):
    pi = arb.pi()
    return pi / 2 * x**2 * (2 * pi * x**2 - 3) * (-pi * x**2).exp()

def c0sq(eta=0.1, nballs=400):
    eta_a = arb(eta)
    width = 2 * eta_a / nballs
    tail_n = sum(20 * arb(n)**4 * (-arb.pi() * n * n * (-2 * eta_a).exp()).exp() for n in range(13, 60))
    # n >= 60: consecutive ratios are < 1/2 there, so the rest is <= 2 x (term at n = 60)
    tail_n += 2 * 20 * arb(60)**4 * (-arb.pi() * 3600 * (-2 * eta_a).exp()).exp()
    tot = arb(0); mins = []
    for i in range(nballs):
        mid = -eta_a + (i + arb(0.5)) * width
        y = arb(mid.mid(), (width / 2).upper())          # ball covering the i-th subinterval
        ey = y.exp()
        s = sum((h_arb(n * ey) for n in range(1, 13)), arb(0))
        s = s + arb(0, tail_n.upper())
        eh = (y / 2).exp() * s
        lo = eh.lower() if eh.lower() > 0 else -eh.upper()   # lower bound of |e_h| on the ball (e_h has one sign here)
        mins.append(lo)
        tot += width * arb(max(lo, 0))**2
    return tot, min(mins)

if __name__ == '__main__':
    mp.mp.dps = 40
    eta = 0.1
    tot, m = c0sq(eta)
    print(f"eta={eta}: int_(-eta)^eta e_h^2 >= {tot.lower()}   (min |e_h| on [-eta,eta] >= {m})")
    for mu in [5, 7, 11, 13, 20]:
        lam = mp.sqrt(mu); delta = 1 / lam**2; b = lam - 2 * delta
        eps = 2 * tail(0, b); psimax = mp.mpf(315) / 32 * max(x**2 * (1 - x**2)**3 for x in [mp.mpf(k) / 1000 for k in range(1001)]) * mp.mpf('1.001')
        E = mp.e**(mp.mpf(eta) / 2) * (eps * psimax + U(0, b) + mp.e**mp.mpf(eta) * tail(0, b))
        # ||k||^2 >= sum width*(|e_h| - E)^2 >= (sqrt(int e_h^2) - sqrt(2 eta) E)^2  (Minkowski on [-eta, eta])
        c0 = (mp.sqrt(mp.mpf(tot.lower().str(50, radius=False))) - mp.sqrt(2 * eta) * E)**2
        print(f"mu={mu}: E={mp.nstr(E,4)}  ||k||^2 >= c0^2 = {mp.nstr(c0,6)}   (a = log lam = {mp.nstr(mp.log(lam),4)} >= eta: {mp.log(lam) >= eta})")
