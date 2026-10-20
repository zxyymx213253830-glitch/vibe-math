"""Zero-mode prelog controls, including infinite absolute log moment example."""
import hashlib,json
from pathlib import Path
import numpy as np
seed=2026102002;N=200000;rng=np.random.default_rng(seed);records=[]
for q in [0.0,0.3,1.0]:
 active=rng.random(N)<q
 f=active*rng.exponential(size=N)
 logs=np.array([10.,100.,1000.])
 # logaddexp avoids overflow in r and underflow in f. Exact zero atoms remain zero.
 vals=[np.where(active,np.logaddexp(0,L+np.log(np.maximum(f,1e-300)))/L,0) for L in logs]
 errs=[abs(v.mean()-active.mean()) for v in vals]
 assert errs[-1]<0.01
 assert np.all(vals[-1]>=0) and np.all(vals[-1]<=1+f+1e-12)
 if q==0: assert all(v.mean()==0 for v in vals)
 if q==0.3: assert abs(vals[-1].mean()-1)>0.5 # wrong strict-fullrank answer1 rejected.
 records.append(dict(case='Bernoulli-Gamma',q=q,empirical_active=float(active.mean()),logr=logs.tolist(),errors=errs))
# Y Pareto exponent1/2 has E Y=infinity; f=exp(-Y)>0, bounded1, E|logf|=infinity.
Y=rng.pareto(.5,N)+1
logs=np.array([100.,10000.,1000000.]);means=[]
for L in logs:
 ratio=np.logaddexp(0,L-Y)/L
 assert np.all(ratio>=0) and np.all(ratio<=1+np.exp(-np.minimum(Y,745))+1e-12)
 means.append(float(ratio.mean()))
assert means[0]<means[1]<means[2] and means[-1]>.99
records.append(dict(case='positive bounded f with infinite absolute log moment',logr=logs.tolist(),ratios=means,
 convention='Logspace evaluation; never represent exp(-Y) aszero to decide positivity. Infinite moment follows analytic Pareto tail, not sampling.'))
report=dict(seed=seed,samples=N,status='PASS zero-atom/Gamma and logspace infinite-logmoment prelog controls; NOT proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
Path('verification/central_mixed_moments/zero-spectrum-prelog-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'])
