"""Actual CN(0,1) mixed monomial controls, not an orthogonality proof."""
from pathlib import Path
from math import factorial
import hashlib
import json
import numpy as np

seed=2026101904
samples=200000
rng=np.random.default_rng(seed)
z=(rng.normal(size=samples)+1j*rng.normal(size=samples))/np.sqrt(2)
energy=np.abs(z)**2
baseline=(float(energy.mean())-1)/np.sqrt(1/samples)
assert abs(baseline)<6
records=[]
for p in range(5):
    for q in range(5):
        vals=z**p*np.conj(z)**q
        target=factorial(p) if p==q else 0
        for part,expected in [(vals.real,target),(vals.imag,0)]:
            se=float(part.std(ddof=1)/np.sqrt(samples))
            err=float(part.mean())-expected
            if se>1e-14: assert abs(err/se)<6
            else: assert abs(err)<1e-10
        if p!=q:
            c=np.exp(1j*np.pi/(p-q))
            assert abs(c**p*np.conj(c)**q+1)<1e-12
        records.append(dict(p=p,q=q,target=target,empirical_real=float(vals.real.mean()),empirical_imag=float(vals.imag.mean())))
out=dict(seed=seed,samples=samples,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         status='PASS actual mixed monomials with Exp(1) energy/Gamma-factorial controls; not proof',
         Exp1_energy_se=baseline,records=records)
root=Path(__file__).resolve().parents[1]
(root/'verification/central_mixed_moments/complex-monomial-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS 25 CN mixed-moment controls, Exp(1) energy baseline and off-diagonal phase checks')
