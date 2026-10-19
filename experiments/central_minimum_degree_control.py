"""Exact fixed-seed polynomial degree/normalization controls, not proof."""
from pathlib import Path
import hashlib
import json
import math
import numpy as np
import sympy as sp

SEED = 2026101907
rng = np.random.default_rng(SEED)
x = sp.Symbol('x')
records = []
for n in range(6):
    A = sp.Matrix(rng.integers(-2, 3, size=(n, n)).tolist()) if n else sp.zeros(0)
    G = A.T*A
    determinant = (G+x*sp.eye(n)).det()
    for d in range(5):
        p = sp.Poly(determinant**d, x)
        assert p.degree() == n*d and p.LC() == 1
        records.append(dict(n=n, d=d, degree=int(p.degree()), leading_coefficient=str(p.LC())))

z = sp.symbols('z0:4')
w = sp.symbols('w0:4')
det = (z[0]*z[3]-z[1]*z[2])*(w[0]*w[3]-w[1]*w[2])
trace = sum(z[i]*w[i] for i in range(4))
moment_records = []
for d in range(5):
    moment = 0
    for powers, coefficient in sp.Poly(sp.expand((det+x*trace+x*x)**d), *(z+w)).terms():
        if powers[:4] == powers[4:]:
            moment += coefficient*math.prod(math.factorial(k) for k in powers[:4])
    p = sp.Poly(sp.expand(moment), x)
    mass = math.factorial(d)*math.factorial(d+1)
    assert p.degree() == 2*d and p.LC() == 1
    assert p.eval(0) == mass  # independent Gamma determinant moments for square2x2.
    moment_records.append(dict(n=2, d=d, polynomial=str(p.as_expr()), mass=mass))
result = dict(seed=SEED, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS exact determinant/functional degree and Gamma-factorial controls; not proof',
              matrix_records=records, factorial_functional_records=moment_records)
dest = Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/degree-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'])
