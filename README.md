# Twin prime elements from exceptional units, and a fake-world filter for twin-prime engines

Status: research notes, 24 November 2026. Not peer reviewed. No Lean formalization yet. Novelty of Theorem 1 is unverified:
we did not find it stated in the cited papers or elsewhere, but a full literature search has not been done.

Author: Roy Sulaiman. Ideas were generated and checked with AI assistance (Claude, including Claude Fable 5.2 for hypothesis generation;
a separate web-search assistant for literature). Every numerical claim below was computed by the included scripts.

## 1. Theorem (twin prime elements in a degree-29 field)

Let K = Q(ζ₅₉)⁺, the maximal real subfield of the 59th cyclotomic field (degree 29). There are infinitely many α ∈ O_K such that
α and α + 1 are both prime elements of O_K.

Proof sketch.
1. Fix A = 1, B = ζ, C = ζ² (ζ = e^{2πi/59}) and for each 59th root of unity P ≠ B put h(P) = (P − A)(C − B) / ((P − B)(C − A)).
   Each h(P) is fixed by ζ ↦ ζ⁻¹, so lies in K. There are 58 distinct values (including 0 = h(A)).
2. For P ≠ Q, h(P) − h(Q) = (A − B)(C − B)(P − Q) / ((C − A)(P − B)(Q − B)). Every difference of distinct 59th roots of unity
   generates the prime ideal (1 − ζ), so this quotient is a unit. Hence all pairwise differences of the 58 values are units of O_K
   (checked numerically: all 1653 norms are ±1, `verify_e4.py`).
3. Because the differences are units, the 58 values are distinct modulo every prime ideal of O_K; every prime ideal has norm ≥ 59.
   So any 54 of them form an admissible 54-tuple in O_K.
4. Castillo–Hall–Lemke Oliver–Pollack–Thompson, "Bounded gaps between primes in number fields and function fields"
   (Proc. AMS 2015), Corollary 2.6, with Hinz's Bombieri–Vinogradov theorem for totally real fields (level θ < 1/2, their
   Theorem 2.7) and Polymath's bound M₅₄ > 4.00238 (D.H.J. Polymath, Res. Math. Sci. 2014, Theorem 23(vii)): infinitely many
   translates α₀ + h_i contain at least two prime elements.
5. Some pair (i, j) recurs infinitely often. With u = h_j − h_i (a unit), β = (α₀ + h_i)/u and β + 1 = (α₀ + h_j)/u are both prime.

Over Z the same argument is impossible: the only units are ±1, so the longest list with all pairwise differences units is {0, 1}.
Descent (forcing the norms of β, β + 1 to differ by 2) is open; the twin prime conjecture is not claimed.

## 2. The filter that found it

Selberg's weight w(n) = 1 − λ(n)λ(n+2) (λ = Liouville) satisfies every sieve axiom and level-of-distribution input yet gives zero
mass to twin pairs. A method whose key input still holds in that world cannot prove twins. We screen every proposed starting
engine by computing its key input in both worlds (minutes of compute). Blind calibration: fakes pre-registered from target
statements only, two independent judges, 20 anonymised openings: 9/10 real breakthrough openings (GRH, Yang–Mills, FLT,
Friedlander–Iwaniec, Zhang, ...) kept, 1/10 dead programs kept.

In O_K with unit-difference triangles, a ±1 sign alternating on every unit-gap edge is impossible (three edge signs multiply to +1),
which is the structural reason the parity fake has no analogue there. Over Z the gap-2 graph is a path, with no triangles.

## 3. An exact restatement on Chen primes (root numbers)

For E_n: y² = x(x − n)(x + 2) with n(n+2) odd squarefree, the root number is W(E_n) = c(n mod 8)·λ(n)λ(n+2)
(c = −1 for n ≡ 1, 3; +1 for n ≡ 5, 7 mod 8), checked on 6,451 cases. On primes p ≡ 5 mod 8 with p + 2 squarefree and
Ω(p+2) ≤ 2, the 2-Selmer group is minimal exactly when p + 2 is prime (Qiu–Zhang for twins; the converse by the root-number
formula and the 2-parity theorem). PARI's 2-descent bound: rank 0 for 36/36 twins, rank 1 for 73/73 semiprime cases, p < 6000.
Related: K. Joshi, arXiv:2508.12340; Qiu–Zhang, arXiv:math/0103243.

## Files
- `verify_e4.py`: checks steps 1–3 of Theorem 1 (cypari2, sympy).
- SHA-256 of this README is posted separately as a timestamp.
