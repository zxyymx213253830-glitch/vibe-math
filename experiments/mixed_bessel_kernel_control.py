"""Mixed central/Bessel kernel factorization checks, not a proof."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps = 70
rng = random.Random(2026102903)
checks = 0
for n in range(5):
    x = [mp.mpf(v) / 5 for v in sorted(rng.sample(range(1, 25), n))]
    for p in range(n + 1):
        L = n-p
        lam = [mp.mpf(v) / 6 for v in sorted(rng.sample(range(1, 24), L))]
        for q in range(4):
            rows = []
            factored = []
            for xi in x:
                rr = mp.sqrt(xi) ** q
                row, row2 = [], []
                for j in range(n):
                    if j < p:
                        row.append(rr * xi ** j)
                        row2.append(rr * xi ** j)
                    else:
                        lj = lam[j-p]
                        row.append(mp.besseli(q, 2*mp.sqrt(xi*lj)))
                        z = xi*lj
                        series = mp.fsum(z**m / (mp.factorial(m)*mp.factorial(q+m)) for m in range(100))
                        row2.append(rr * mp.sqrt(lj)**q * series)
                rows.append(row)
                factored.append(row2)
            if n:
                for i in range(n):
                    for j in range(n):
                        assert mp.almosteq(rows[i][j], factored[i][j], rel_eps=mp.mpf('1e-55'))
                        checks += 1
                assert mp.det(mp.matrix(rows)) > 0
            checks += 1
out = {'seed': 2026102903, 'status': 'PASS', 'checks': checks, 'precision': 70,
       'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'not_a_proof': True,
       'scope': 'row/column factorization for formula-side mixed Bessel kernel; no actual law'}
p = Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-bessel-kernel-control.json'
p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('PASS', checks, 'seed', 2026102903)
