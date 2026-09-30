"""Symbolic check of the derivative structure in the proof of Lemma 5.3 (Theorem B).
A term omega^i F_{5/2+l}(beta^2 - omega^2) is stored as the pair (i, l); by (5.1),
  d/domega [omega^i F_a] = i omega^(i-1) F_a - omega^(i+1) F_(a+1).
The rule itself is first checked with sympy on the (truncated) series of F_a.
Output: the term lists of G'' and G'''', of omega d/domega applied to them, and the resulting powers of lambda."""
import sympy as sp
from collections import defaultdict
w, b, z = sp.symbols('omega beta z', positive=True)
# (1) check rule d/dw F_a(b^2-w^2) = -w F_{a+1}(b^2-w^2) on truncated series
def Fser(a, arg, J=12):
    return sum((arg/4)**j/(2**a*sp.factorial(j)*sp.gamma(j+a+1)) for j in range(J))
a = sp.Rational(5, 2)
lhs = sp.diff(Fser(a, b**2-w**2, 12), w); rhs = -w*Fser(a+1, b**2-w**2, 11)
print("rule residual (truncated series, should be 0):", sp.simplify(sp.expand(lhs-rhs)))
# (2) derivative structure
def d(poly):  # poly: dict (i,l)->coeff
    out = defaultdict(int)
    for (i, l), c in poly.items():
        if i: out[(i-1, l)] += c*i
        out[(i+1, l+1)] -= c
    return {k: v for k, v in out.items() if v}
def wd(poly):  # omega * d/domega
    out = defaultdict(int)
    for (i, l), c in d(poly).items(): out[(i+1, l)] += c
    return dict(out)
G = {(0, 0): 1}
G2 = d(d(G)); G4 = d(d(G2))
print("G''  :", G2); print("G'''':", G4)
phihat = set(G2) | set(G4)
xiphi = set(wd(G2)) | set(wd(G4))
print("phihat terms (i,l):", sorted(phihat), " max i =", max(i for i, _ in phihat), " all i<=l:", all(i <= l for i, l in phihat))
print("xi phihat' terms  :", sorted(xiphi), " max i =", max(i for i, _ in xiphi), " all i<=l+1:", all(i <= l+1 for i, l in xiphi))
# (3) powers of lambda in the band-edge bound: prefactor lambda^5 * beta^{5/2}, times (2 beta)^{max i}; beta ~ lambda^2
for name, mi in [("phihat", max(i for i, _ in phihat)), ("xi phihat'", max(i for i, _ in xiphi))]:
    print(f"{name}: lambda power = 5 + 2*(5/2 + {mi}) = {5 + 2*(sp.Rational(5,2)+mi)}")
