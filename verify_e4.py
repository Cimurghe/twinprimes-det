"""Verify the finite algebra behind Theorem 1 (needs cypari2 and sympy).
h(P) = (P - 1)(zeta^2 - zeta) / ((P - zeta)(zeta^2 - 1)) for the 58 roots of unity P != zeta of order dividing 59.
Checks: every h(P) is fixed by zeta -> zeta^-1 (so lies in Q(zeta_59)^+), all 1653 pairwise differences have norm +-1,
and every prime ideal of Q(zeta_59)^+ has norm >= 59 (so any 54 of the 58 values form an admissible tuple)."""
import cypari2, sympy
pari = cypari2.Pari(); q = 59
Phi = pari.polcyclo(q); z = pari.Mod(pari('x'), Phi)
A, B, C = z**0, z, z**2
H = [(z**j - A) * (C - B) / ((z**j - B) * (C - A)) for j in range(q) if j != 1]
inv = lambda v: pari.Mod(pari.subst(pari.lift(v), 'x', pari('x^%d' % (q - 1))), Phi)
assert all(inv(v) == v for v in H), "not real"
bad = sum(1 for i in range(len(H)) for j in range(i + 1, len(H)) if abs(int(pari.norm(H[i] - H[j]))) != 1)
def fplus(r):
    o = sympy.n_order(r, q); return o // 2 if o % 2 == 0 else o
smallest = min(min(r ** fplus(r) for r in sympy.primerange(2, 3000) if r != q), q)
print(f"{len(H)} real values; non-unit differences: {bad} of {len(H)*(len(H)-1)//2}; smallest prime-ideal norm: {smallest}")
