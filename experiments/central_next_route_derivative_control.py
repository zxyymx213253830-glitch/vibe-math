"""Reject the partner's missing-determinant derivative before formalizing it."""
from pathlib import Path
import hashlib
import json
import numpy as np
import scipy.special as sc
import sympy as sp

v, x = sp.symbols('v x', positive=True)
correct = sp.diff(v+x, x)
proposed = 1/(v+x)
assert correct.subs({v: 1, x: 1}) == 1
assert proposed.subs({v: 1, x: 1}) == sp.Rational(1, 2)
assert (v+x).subs({v: 0, x: 1}) == 1
seed = 2026101803
samples = np.random.default_rng(seed).exponential(size=200000)
closed_wrong = float(np.e * sc.exp1(1))
vals = 1/(samples+1)
se = float(vals.std(ddof=1)/np.sqrt(vals.size))
assert abs(float(vals.mean())-closed_wrong) < 6*se
assert abs(closed_wrong-1) > 0.4
report = dict(seed=seed, samples=200000,
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    status='PASS counterexample and Exp(1) closed control; reject proposed derivative',
    exact_counterexample=dict(d=1, s=1, v=1, x=1, actual_derivative='1', proposed='1/2'),
    integral_baseline='I(1,1,x)=1+x, derivative=1',
    proposed_integral_at_one=closed_wrong, empirical=float(vals.mean()),
    standard_errors=(float(vals.mean())-closed_wrong)/se,
    shifted_kernel_boundary_at_v0_x1='1, not zero',
    interpretation='Counterexample to partner proposal; no new general integral theorem')
root = Path(__file__).resolve().parents[1]
(root/'verification/rectangular_minimum/next-route-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('PASS exact counterexample: derivative 1 differs from proposed 1/2; Exp(1) integral control PASS')
