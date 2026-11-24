"""E6 check: identity, sign split, dichotomy firing rate, and the chi fakes.
Rough_z(n): no prime factor < z.  u = kt+1, v = k(t+2)+1, N = t*v, N+2 = (t+2)*u.
Usage: python verify_e6.py [T] [K] [z]"""
import sys
T = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
K = int(sys.argv[2]) if len(sys.argv) > 2 else 30
z = int(sys.argv[3]) if len(sys.argv) > 3 else 5
M = K * (T + 2) + 2
omega = [0] * (M + 1); rem = list(range(M + 1))
for p in range(2, M + 1):
    if rem[p] == p and omega[p] == 0 and all(p % q for q in range(2, int(p**0.5) + 1)):
        for m in range(p, M + 1, p):
            while rem[m] % p == 0:
                rem[m] //= p; omega[m] += 1
lam = lambda n: -1 if omega[n] % 2 else 1
small = [p for p in range(2, z) if all(p % q for q in range(2, p))]
rough = lambda n: all(n % p for p in small)
def chi4(n): return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)
def chi3(n): return 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)
tot = fire = c4 = c3 = 0
for t in range(1, T + 1):
    for k in range(1, K + 1):
        u, v = k * t + 1, k * (t + 2) + 1
        assert t * v + 2 == (t + 2) * u
        if not (rough(t) and rough(t + 2) and rough(u) and rough(v)): continue
        tot += 1
        b = lam(u) * lam(v)
        if b == -1: fire += 1
        if chi4(u) * chi4(v) == -1: c4 += 1
        if chi3(u) * chi3(v) == -1: c3 += 1
print(f"T={T} K={K} z={z}: rough configs {tot}, lambda fires {fire/tot:.4f}, chi_-4 fires {c4}, chi_-3 fires {c3}")
