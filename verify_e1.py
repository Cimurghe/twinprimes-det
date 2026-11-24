"""Verify E1 numerically (needs cypari2, sympy). Takes about a minute.
(1) W(E_n) = c(n mod 8) * lambda(n)lambda(n+2) for odd n <= N with n(n+2) squarefree, E_n: y^2 = x(x-n)(x+2).
(2) Chen class p = 5 mod 8, p+2 squarefree with Omega <= 2: PARI's 2-descent rank bound is 0 iff p+2 is prime."""
import cypari2, sympy
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
N = 20001; bad = tot = 0
for n in range(1, N + 1, 2):
    if not (pari.issquarefree(n) and pari.issquarefree(n + 2)): continue
    W = int(pari.ellrootno(pari.ellinit([0, 2 - n, 0, -2 * n, 0])))
    lam = (-1) ** (len(sympy.factorint(n)) + len(sympy.factorint(n + 2)))
    tot += 1; bad += W != (-1 if n % 8 in (1, 3) else 1) * lam
print(f"(1) identity checked on {tot} values of n <= {N}: {bad} exceptions")
tw = [0, 0]; sp = [0, 0]
for p in sympy.primerange(5, 6000):
    if p % 8 != 5: continue
    f = sympy.factorint(p + 2)
    if any(e > 1 for e in f.values()) or sum(f.values()) > 2: continue
    R = int(pari.ellrank(pari.ellinit([0, 2 - p, 0, -2 * p, 0]))[1])
    (tw if sympy.isprime(p + 2) else sp)[0 if R == 0 else 1] += 1
print(f"(2) twins: rank bound 0 in {tw[0]}/{sum(tw)};  semiprime p+2: rank bound 0 in {sp[0]}/{sum(sp)}")
