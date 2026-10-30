"""Exact finite exponent calibration for mixed candidate scaling; not proof."""
from pathlib import Path
import hashlib
import json
import random

rng = random.Random(2026103012)
checks = 0
negatives = 0
for p in range(13):
    for ell in range(13):
        for q in (0, 1, 3, rng.randrange(0, 20)):
            n = p + ell
            actual = sum(q+i+1 for i in range(n)) + sum(range(p)) + ell*p + sum(range(ell))
            assert actual == n*(n+q)
            checks += 1
            wrong = sum(q+i+1 for i in range(n)) + sum(range(p)) + sum(range(ell))
            if wrong != n*(n+q):
                negatives += 1
assert negatives > 0
result = dict(seed=2026103012,status='PASS',checks=checks,negative_controls=negatives,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              not_a_proof=True,scope='integer dimension exponent identity including zero')
out = Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/quota-20261022-0949/mixed-laplace-exponent-control.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',checks,'negative',negatives)
