"""Independent fixed-seed Psi tail ratio calibration; numerical evidence only."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps = 38
rng = random.Random(2026103010)
checks = 0
negative_controls = 0
for size in (1, 2, 3):
    for p in range(size + 1):
        ell = size - p
        lam = [mp.mpf(v) / 7 for v in sorted(rng.sample(range(2, 24), ell))]
        for q in (0, 2):
            def kernel(y, a):
                z = a * y
                return mp.besseli(q, 2 * mp.sqrt(z)) / z ** (mp.mpf(q) / 2)

            def candidate(x):
                return mp.matrix([[mp.quad(
                    lambda y: y ** (q + i) * mp.exp(-y) *
                    (y ** j if j < p else kernel(y, lam[j-p])),
                    [x, x + 1, mp.inf]) for j in range(size)] for i in range(size)])

            def paper(x):
                out = mp.matrix(size)
                for i in range(size):
                    k = size - i - 1
                    for j in range(size):
                        if j < ell:
                            a = lam[ell - j - 1]
                            low = mp.sqrt(2 * x)
                            out[i, j] = mp.power(2, -mp.mpf(q)/2-k) * mp.quad(
                                lambda r: r ** (q+2*k+1) * mp.exp(-(r*r+2*a)/2) *
                                mp.besseli(q, mp.sqrt(2*a)*r), [low, low+1, mp.inf])
                        else:
                            out[i, j] = mp.gammainc(q+k+size-j, x, mp.inf)
                return out

            base_c, base_p = mp.det(candidate(0)), abs(mp.det(paper(0)))
            assert base_c > 0 and base_p > 0
            checks += 1
            for x in (mp.mpf('0.4'), mp.mpf('1.3')):
                c, a = mp.det(candidate(x))/base_c, abs(mp.det(paper(x)))/base_p
                assert 0 < c < 1 and mp.almosteq(a, c, rel_eps=mp.mpf('1e-23'))
                checks += 1
                if abs(mp.det(paper(x))/base_c - c) > mp.mpf('1e-6'):
                    negative_controls += 1

assert negative_controls > 0
result = {'seed': 2026103010, 'status': 'PASS', 'checks': checks,
          'negative_controls': negative_controls, 'precision': mp.mp.dps,
          'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'not_a_proof': True, 'scope': 'formula-side Psi and candidate tail determinant ratios, not actual law'}
path = Path(__file__).resolve().parents[1] / 'verification/sheaf_wishart/quota-20261022-0949/psi-candidate-ratio-control.json'
path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print('PASS', checks, 'negative', negative_controls, 'seed', result['seed'])
