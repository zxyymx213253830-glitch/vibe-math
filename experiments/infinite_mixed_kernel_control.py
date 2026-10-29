"""Reproducible mixed-series determinant and fixed-floor controls; not a proof."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps = 80
SEED = 2026102902
rng = random.Random(SEED)
checks = 0
for n in range(5):
    x = [mp.mpf(a) / 4 for a in sorted(rng.sample(range(1, 24), n))]
    for p in range(n + 1):
        L = n - p
        lam = [mp.mpf(a) / 5 for a in sorted(rng.sample(range(1, 20), L))]
        for q in range(3):
            w = lambda k: 1 / (mp.factorial(k) * mp.factorial(q + k))
            def kval(i, j, N):
                if j < p:
                    return x[i] ** j
                return mp.fsum(x[i] ** m * w(m) * lam[j-p] ** m for m in range(N))
            def matrix(N):
                return mp.matrix(n, n) if n == 0 else mp.matrix([[kval(i,j,N) for j in range(n)] for i in range(n)])
            # Independent analytic series reference via modified Bessel I.
            def exact(i, j):
                if j < p:
                    return x[i] ** j
                z = x[i] * lam[j-p]
                return mp.besseli(q, 2 * mp.sqrt(z)) / (z ** (mp.mpf(q)/2))
            def det(a):
                return mp.mpf(1) if n == 0 else mp.det(a)
            target = det(mp.matrix(n, n) if n == 0 else mp.matrix([[exact(i,j) for j in range(n)] for i in range(n)]))
            approx = det(matrix(100))
            assert mp.almosteq(target, approx, rel_eps=mp.mpf('1e-55'), abs_eps=mp.mpf('1e-65'))
            checks += 1
            lowest = det(matrix(n))
            assert lowest > 0 and mp.factorial(n) * target >= lowest * (1-mp.mpf('1e-55'))
            checks += 1
            if L >= 2:
                old = lam[-1]
                lam[-1] = lam[0]
                assert abs(det(matrix(60))) < mp.mpf('1e-60')
                lam[-1] = old
                checks += 1
out = {'seed': SEED, 'status': 'PASS', 'checks': checks,
       'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'not_a_proof': True, 'precision': 80,
       'scope': 'mixed coefficient/entire-series kernel, finite floor, independent Bessel reference; not actual law'}
p = Path(__file__).resolve().parents[1] / 'verification/sheaf_wishart/quota-20261022-0949/infinite-mixed-kernel-control.json'
p.write_text(json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print('PASS', checks, 'seed', SEED)
