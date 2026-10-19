"""Deterministic exact right-tail polynomial control; no probability proof."""
from pathlib import Path
import hashlib
import json
import math
import sympy as sp

root = Path(__file__).resolve().parents[1]
dep = root/'verification/central_mixed_moments/degree-control.json'
data = json.loads(dep.read_text(encoding='utf-8'))
assert data['status'].startswith('PASS')
x = sp.Symbol('x')
records = []
for row in data['factorial_functional_records']:
    d = row['d']
    polynomial = sp.sympify(row['polynomial'], locals={'x': x})
    normalized = polynomial/row['mass']
    target = sp.Rational(1, row['mass'])
    assert sp.limit(normalized/x**(2*d), x, sp.oo) == target
    ratios = [normalized.subs(x, 10**k)/(10**k)**(2*d) for k in (2, 4, 8)]
    errors = [abs(v/target-1) for v in ratios]
    assert errors[-1] <= errors[0] and errors[-1] < sp.Rational(1, 1000000)
    records.append(dict(n=2, d=d, target=str(target), ratios=[str(v) for v in ratios]))

# Independent scalar Gamma(d+1,1) upper tail: exp(-x)*sum_{j=0}^d x^j/j!.
for d in range(6):
    gamma_poly = sum(x**j/sp.factorial(j) for j in range(d+1))
    assert sp.limit(gamma_poly/x**d, x, sp.oo) == sp.Rational(1, math.factorial(d))

result = dict(seed=None, status='PASS exact polynomial leading-tail and scalar Gamma controls; not proof',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              degree_control_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(), records=records)
dest = root/'verification/central_mixed_moments/tail-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'])
