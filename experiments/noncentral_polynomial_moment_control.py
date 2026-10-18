"""Actual noncentral Gram moments: factorial contraction with known ncx2 control."""
from pathlib import Path
import hashlib
import json
import math
import numpy as np
import sympy as sp
from scipy.stats import ncx2

SEED, N = 2026101906, 200000
rng = np.random.default_rng(SEED)
z = sp.symbols('z0:4')
w = sp.symbols('w0:4')


def moment(expr):
    out = 0
    for powers, c in sp.Poly(sp.expand(expr), *(z+w)).terms():
        if powers[:4] == powers[4:]:
            out += c*math.prod(math.factorial(k) for k in powers[:4])
    return sp.expand(out)


def score(values, target):
    mean = float(np.mean(values))
    se = float(np.std(values, ddof=1)/np.sqrt(N))
    error = (mean-float(target))/se if se else 0.0
    assert abs(error) <= 6, (target, mean, error)
    return dict(target=float(target), empirical=mean, standard_errors=error)


samples = (rng.standard_normal((N, 4))+1j*rng.standard_normal((N, 4)))/np.sqrt(2)
mu = [1, sp.I, 0, 1]
Z = sp.Matrix(2, 2, [z[i]+mu[i] for i in range(4)])
Zstar = sp.Matrix(2, 2, [w[i]+sp.conjugate(mu[i]) for i in range(4)]).T
G = Zstar*Z
A = samples.reshape(N, 2, 2)+np.array([1, 1j, 0, 1]).reshape(2, 2)
gram = np.einsum('nri,nrj->nij', A.conj(), A)
records = {}
for d in (1, 2, 3):
    target = moment((G+sp.eye(2)/2).det()**d)
    records[f'shifted_det_power_{d}'] = score(np.linalg.det(gram+np.eye(2)/2).real**d, target)
trace = sum(G[i, i] for i in range(2))
for d in (1, 2, 3):
    target = moment(trace**d)
    # 2 trace ~ ncx2(df=8,nc=6), since ||M||_F^2=3.
    known = ncx2.moment(d, 8, 6)/2**d
    assert abs(float(target)-known) < 1e-8
    records[f'trace_ncx2_power_{d}'] = score(np.trace(gram, axis1=1, axis2=2).real**d, target)
result = dict(seed=SEED, samples=N, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              status='PASS actual noncentral polynomial moments with ncx2 trace controls; not proof',
              records=records)
dest = Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/noncentral-polynomial-control.json'
dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'])
