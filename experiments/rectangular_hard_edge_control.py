"""Exact symbolic hard-edge control, with the Gamma(2,1) case as baseline."""
from pathlib import Path
import hashlib
import json
import sympy as sp

root = Path(__file__).resolve().parents[1]
x = sp.Symbol('x')
records = []
for n in range(1, 13):
    p = sum(sp.binomial(n, l)*x**l/sp.factorial(l) for l in range(n+1))
    f = 1-sp.exp(-n*x)*p
    coefficient = sp.simplify(sp.diff(f, x, 2).subs(x, 0)/2)
    target = sp.Rational(n*(n+1), 4)
    assert f.subs(x, 0) == 0 and sp.diff(f, x).subs(x, 0) == 0
    assert coefficient == target
    for v in [sp.Rational(2, 5), sp.Rational(17, 10)]:
        scaled = f.subs(x, x/v)
        assert sp.simplify(sp.diff(scaled, x, 2).subs(x, 0)/2) == target/v**2
    records.append(dict(columns=n, coefficient=str(coefficient)))
assert sp.simplify((1-sp.exp(-x)*(1+x))-(1-sp.exp(-x)*sum(x**k/sp.factorial(k) for k in range(2)))) == 0
report = dict(status='PASS exact symbolic controls; not a general proof',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              seed=2026101802, baseline='n=1 Gamma(2,rate1) CDF', records=records)
(root/'verification/rectangular_minimum/hard-edge-control.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print('PASS exact hard-edge coefficients n=1..12, Gamma(2,1) baseline')
