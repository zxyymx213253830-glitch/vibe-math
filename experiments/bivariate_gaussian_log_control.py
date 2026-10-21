"""Bivariate polynomial root/leading-coefficient controls, not proofs."""
from pathlib import Path
import hashlib
import json
import numpy as np

SEED = 2026102022
N = 200_000
rng = np.random.default_rng(SEED)
a = rng.normal(size=N)+1j*rng.normal(size=N)
z = rng.normal(size=N)+1j*rng.normal(size=N)


def nl(x):
    out = np.zeros(x.shape, dtype=float)
    nz = np.abs(x) != 0
    out[nz] = np.maximum(0., -np.log(np.abs(x[nz])))
    return out


checks = []
def record(name, ok, **data):
    checks.append(dict(name=name, passed=bool(ok), **data))

cases = [('az', a*z, .5), ('az+1', a*z+1, .5),
         ('(a2+1)z2+a', (a*a+1)*z*z+a, 1.),
         ('a2z3', a*a*z**3, 1.25), ('constant', np.ones(N, dtype=complex), 0.)]
for name, value, bound in cases:
    y=nl(value); se=float(y.std(ddof=1)/np.sqrt(N))
    record(name, y.mean() <= bound+8*se+1e-9, empirical=float(y.mean()), bound=bound, se=se)
root=-1/a
dominant=nl(a)+nl(z-root)
record('az+1-factorization-pointwise', np.all(nl(a*z+1) <= dominant+1e-11))
log_product=np.log(np.abs(a*z))
reference=float(np.log(2)-np.euler_gamma)
se=float(log_product.std(ddof=1)/np.sqrt(N))
record('known-Rayleigh-product-log', abs(log_product.mean()-reference) <= 8*se,
       empirical=float(log_product.mean()), reference=reference, se=se)
record('degree-drop-fiber-control', (0*complex(3)+1)==1,
       meaning='At a=0, az+1 has degree0; formal leadingCoeff bridge must be AE, not pointwise')
result=dict(seed=SEED,samples=N,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            status='PASS' if all(c['passed'] for c in checks) else 'FAIL',checks=checks,
            interpretation='Reproducible controls including known Rayleigh log mean; not polynomial log-integrability proof')
path=Path(__file__).resolve().parents[1]/'verification/sheaf_wishart/hour-20261020-1535/bivariate-control.json'
path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'],len(checks),'controls')
raise SystemExit(0 if result['status']=='PASS' else 1)
