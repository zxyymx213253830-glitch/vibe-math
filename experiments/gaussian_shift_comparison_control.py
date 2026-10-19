"""Fixed-seed pointwise shift-density and scalar ncx2 event controls; not proof."""
import hashlib,json
from pathlib import Path
import numpy as np
from scipy.stats import chi2,ncx2

rng=np.random.default_rng(2026101909);records=[]
for dim in (2,8,24):
 x=rng.standard_normal((200000,dim));mu=np.zeros(dim);mu[0]=1.25
 q=np.sum(x*x,axis=1);h=float(mu@mu);shift=np.sum((x-mu)**2,axis=1)
 # After cancellation of the SAME standard Gaussian normalization:
 # 2^-D exp(-h)*phi_{scale1/2}(x) <= phi(x-mu)
 # phi(x-mu) <= 2^D exp(h)*phi_{scale2}(x).
 lower_gap=(-shift/2)-(-h-2*q)
 upper_gap=(h-q/8)-(-shift/2)
 assert np.min(lower_gap)>-1e-10 and np.min(upper_gap)>-1e-10
 # Actual shifted standard Gaussian squared norm has ncx2(D,h),
 # independent known exact mean D+h and variance2(D+2h).
 samples=np.sum((x+mu)**2,axis=1)
 se=np.sqrt(2*(dim+2*h)/len(samples))
 assert abs(np.mean(samples)-(dim+h))<6*se
 for radius in (0.25,1,3,8):
  mass=ncx2.cdf(radius**2,dim,h)
  lo=2.0**(-dim)*np.exp(-h)*chi2.cdf(4*radius**2,dim)
  hi=2.0**dim*np.exp(h)*chi2.cdf(radius**2/4,dim)
  assert lo<=mass+1e-14 and mass<=hi+1e-14
 records.append(dict(dimension=dim,mean_norm_square=h,count=len(x),
    min_log_lower_gap=float(np.min(lower_gap)),min_log_upper_gap=float(np.min(upper_gap)),
    mean_error_SE=float((np.mean(samples)-dim-h)/se)))
# Equal-variance Gaussian densities cannot be globally bounded by a fixed
# constant: along the mean ray the shifted/central log ratio grows linearly.
assert 100*1.25-1.25**2/2>100
result=dict(seed=2026101909,status='PASS fixed-seed shift-density inequalities, ncx2/chi2 controls and equal-variance negative control; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
dest=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/shift-comparison-control.json'
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
