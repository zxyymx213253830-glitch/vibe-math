"""Reproducible root/product negative-log controls, not proofs.

stdGaussian(C) here has variance ONE per REAL coordinate; proper CN1 differs.
Central references are obtained by the Rayleigh energy substitution.
"""
from pathlib import Path
import hashlib
import json
import numpy as np
from scipy.integrate import quad
from scipy.special import exp1
from scipy.stats import ncx2

SEED = 2026102021
N = 200_000
rng = np.random.default_rng(SEED)
z = rng.normal(size=N) + 1j*rng.normal(size=N)
checks = []


def record(name, passed, **data):
    checks.append(dict(name=name, passed=bool(passed), **data))


def neglog(value):
    value = np.asarray(value)
    out = np.zeros_like(value, dtype=float)
    nonzero = value != 0
    out[nonzero] = np.maximum(0., -np.log(value[nonzero]))
    return out


central = .5*(np.euler_gamma + np.log(.5) + exp1(.5))
for radius in [0., .2, 1., 3., 8.]:
    tail = quad(lambda t: ncx2.cdf(np.exp(-2*t), 2, radius*radius),
                0, np.inf, epsabs=1e-11)[0]
    sample = neglog(np.abs(z-radius))
    mean, se = float(sample.mean()), float(sample.std(ddof=1)/np.sqrt(N))
    record(f'root-bound-{radius}', tail <= .25+1e-10, quadrature=tail, bound=.25)
    record(f'root-MC-{radius}', abs(mean-tail) <= 8*se+1e-5,
           empirical=mean, reference=tail, standard_error=se)
    if radius == 0:
        direct = quad(lambda r: -np.log(r)*r*np.exp(-r*r/2), 0, 1)[0]
        record('central-Rayleigh-reference', abs(tail-central) < 1e-10 and abs(direct-central) < 1e-10,
               tail=tail, polar_integral=direct, closed_form=float(central))
record('wrong-factor-two-detected', central > .125, correct_reference=float(central), wrong_bound=.125)
proper_reference = .5*(np.euler_gamma+exp1(1.))
record('proper-CN1-variance-detected', proper_reference > .25,
       proper_CN1_reference=float(proper_reference), invalid_stdGaussian_bound=.25)

for lead, roots in [(1., []), (.01, []), (1., [0.]), (1., [0., 0., 0.]),
                    (.2, [1., -2.+1j]), (2., [.3+2j, -.5j, 1.])]:
    value = np.full(N, complex(lead))
    dominant = np.full(N, float(neglog(np.array([abs(lead)]))[0]))
    for root in roots:
        value *= z-root
        dominant += neglog(np.abs(z-root))
    y = neglog(np.abs(value))
    bound = float(neglog(np.array([abs(lead)]))[0] + len(roots)/4)
    se = float(y.std(ddof=1)/np.sqrt(N))
    record(f'product-{lead}-{roots}', np.all(y <= dominant+1e-12) and y.mean() <= bound+8*se+1e-9,
           empirical=float(y.mean()), bound=bound, standard_error=se)
    if lead == 1 and roots and all(r == 0 for r in roots):
        record(f'known-monomial-{len(roots)}', abs(y.mean()-len(roots)*central) <= 8*se+1e-5,
               empirical=float(y.mean()), reference=float(len(roots)*central))

source = Path(__file__)
result = dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), seed=SEED,
              samples=N, model='stdGaussian(C): independent N(0,1) real/imaginary coordinates',
              status='PASS' if all(c['passed'] for c in checks) else 'FAIL', checks=checks,
              interpretation='Finite controls and known central closed forms; NOT a general polynomial proof')
target = source.resolve().parents[1]/'verification/sheaf_wishart/hour-20261020-1535/root-negative-log-control.json'
target.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(result['status'], len(checks), 'controls')
raise SystemExit(0 if result['status'] == 'PASS' else 1)
