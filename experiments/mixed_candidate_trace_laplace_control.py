"""Fixed-seed independent trace-Laplace controls; numerical evidence only."""
from pathlib import Path
import hashlib
import json
import random
import mpmath as mp

mp.mp.dps = 35
rng = random.Random(2026103011)
checks = 0
negative_controls = 0
for n in (1, 2, 3):
    for p in range(n + 1):
        ell = n - p
        lambdas = [mp.mpf(v)/11 for v in sorted(rng.sample(range(2, 26), ell))]
        for q in (0, 2):
            def moment(s):
                def entry(i, j):
                    if j < p:
                        return mp.quad(lambda y: y**(q+i+j)*mp.exp(-(1+s)*y), [0, 1, mp.inf])
                    a = lambdas[j-p]
                    return mp.quad(lambda y: y**(q+i)*mp.exp(-(1+s)*y)*
                        mp.besseli(q, 2*mp.sqrt(a*y))/(a*y)**(mp.mpf(q)/2), [0, 1, mp.inf])
                return mp.det(mp.matrix([[entry(i, j) for j in range(n)] for i in range(n)]))
            base = moment(0)
            assert base > 0
            checks += 1
            for s in (mp.mpf('0.3'), mp.mpf('1.4')):
                ratio = moment(s)/base
                expected = (1+s)**(-n*(n+q))*mp.exp(-s*sum(lambdas)/(1+s))
                assert mp.almosteq(ratio, expected, rel_eps=mp.mpf('1e-20'))
                checks += 1
                wrong = (1+s)**(-n*(n+q))*mp.exp(-s*sum(lambdas))
                if abs(expected-wrong) > mp.mpf('1e-8'):
                    negative_controls += 1
assert negative_controls > 0
result = dict(seed=2026103011, status='PASS', checks=checks, negative_controls=negative_controls,
              precision=mp.mp.dps, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              not_a_proof=True, scope='candidate trace Laplace versus actual Wishart trace formula, not joint-law identification')
path = Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-candidate-trace-laplace-control.json'
path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print('PASS',checks,'negative',negative_controls,'seed',result['seed'])
