"""Powers of lambda in Lemma 5.3 and the band-edge lower bound (Remark 5.4), Theorem B.
F_alpha(z) = 0F1(; alpha+1; z/4) / (2^alpha Gamma(alpha+1)) is entire, so no case distinction at the band edge.
hat(phi_B) and xi*hat(phi_B)' are evaluated from the exact term lists (see check_B3_structure.py):
  G''/(sqrt(2pi) b^2)   = -F_{7/2} + w^2 F_{9/2}
  G''''/(sqrt(2pi) b^2) = 3F_{9/2} - 6w^2 F_{11/2} + w^4 F_{13/2}
  w d/dw acts termwise: w^i F_a -> i w^i F_a - w^{i+2} F_{a+1}.
No numerical differentiation is used at xi = lam, where hat(phi_B) is not smooth.
Self-check: exact xi*hat(phi_B)' against a one-sided difference quotient at the smooth point xi = 1.3 lam."""
import mpmath as mp
mp.mp.dps = 50
def Fa(a, z): return mp.hyp0f1(a+1, z/4)/(2**a*mp.gamma(a+1))
G2 = [(-1, 0, mp.mpf(7)/2), (1, 2, mp.mpf(9)/2)]
G4 = [(3, 0, mp.mpf(9)/2), (-6, 2, mp.mpf(11)/2), (1, 4, mp.mpf(13)/2)]
def wd(terms):
    out = []
    for c, i, a in terms:
        if i: out.append((c*i, i, a))
        out.append((-c, i+2, a+1))
    return out
def ev(terms, w, b): return sum(c*w**i*Fa(a, b**2-w**2) for c, i, a in terms)
def setup(mu):
    lam = mp.sqrt(mu); b = 2*mp.pi*mu; Ib = mp.besseli(2, b)
    Phi = lambda t: (1-t**2)*mp.besseli(2, b*mp.sqrt(1-t**2))/Ib
    sig = lam**2*mp.quad(lambda t: t**4*Phi(t), [0, 1])/mp.quad(lambda t: t**2*Phi(t), [0, 1])
    pre = lam/Ib*mp.sqrt(2*mp.pi)*b**2
    ph = lambda xi: pre*(lam**4*ev(G4, 2*mp.pi*lam*xi, b)+sig*lam**2*ev(G2, 2*mp.pi*lam*xi, b))
    xph = lambda xi: pre*(lam**4*ev(wd(G4), 2*mp.pi*lam*xi, b)+sig*lam**2*ev(wd(G2), 2*mp.pi*lam*xi, b))
    return lam, b, ph, xph
lead22 = (2*mp.pi)**mp.mpf(9.5)/(2**mp.mpf(7.5)*mp.gamma(mp.mpf(8.5)))   # |xi phihat'(lam)| ~ lead22 lam^22 e^{-beta}
lead18 = (2*mp.pi)**mp.mpf(7.5)/(2**mp.mpf(6.5)*mp.gamma(mp.mpf(7.5)))   # |phihat(lam)|      ~ lead18 lam^18 e^{-beta}
print("leading constants at xi=lam:  phihat:", mp.nstr(lead18, 6), "  xi phihat':", mp.nstr(lead22, 6))
print("mu | phihat(lam)e^b/lam^18  sup/lam^18 | xiphihat'(lam)e^b/lam^22  sup/lam^22 | self-check rel.diff")
for mu in [5, 7, 9, 11, 13, 15, 17, 25, 40]:
    lam, b, ph, xph = setup(mp.mpf(mu)); E = mp.e**b
    xis = [lam*(1+mp.mpf(j)/40) for j in range(0, 161)]
    a0 = abs(ph(lam))*E/lam**18; a = max(abs(ph(x))*E*(x/lam)**2.5 for x in xis)/lam**18
    c0 = abs(xph(lam))*E/lam**22; c = max(abs(xph(x))*E*(x/lam)**1.5 for x in xis)/lam**22
    x0 = lam*mp.mpf('1.3'); h = mp.mpf('1e-15')
    fd = x0*(ph(x0+h)-ph(x0))/h
    print(f"{mu:2d} | {mp.nstr(a0,6):>9} {mp.nstr(a,6):>9} | {mp.nstr(c0,6):>9} {mp.nstr(c,6):>9} | {mp.nstr(abs(fd-xph(x0))/abs(xph(x0)),3)}", flush=True)
