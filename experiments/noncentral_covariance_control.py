"""Actual CN covariance/mean scaling identity with ncx2 trace control; not proof."""
import hashlib,json
from pathlib import Path
import numpy as np
from scipy.stats import ncx2
rng=np.random.default_rng(2026101910);records=[]
for m,n in [(2,1),(3,2),(5,3)]:
 Z=(rng.standard_normal((200000,m,n))+1j*rng.standard_normal((200000,m,n)))/np.sqrt(2)
 M=np.zeros((m,n),complex);M[0,0]=0.7+0.2j;M[-1,-1]+=0.3j
 h=float(np.sum(abs(M)**2))
 for v in (0.25,3.):
  A=np.sqrt(v)*Z+M;B=Z+M/np.sqrt(v)
  eigA=np.linalg.eigvalsh(A.conj().transpose(0,2,1)@A)[:,0]
  eigB=np.linalg.eigvalsh(B.conj().transpose(0,2,1)@B)[:,0]
  err=float(np.max(abs(eigA-v*eigB)))
  assert err<1e-10
  tr=np.sum(abs(A)**2,axis=(1,2));mean=v*m*n+h;var=v*v*m*n+2*v*h
  z=float((np.mean(tr)-mean)/np.sqrt(var/len(tr)));assert abs(z)<6
  # Independent exact ncx2: 2*trace/v has df2mn, noncentrality2h/v.
  t=mean;exact=ncx2.cdf(2*t/v,2*m*n,2*h/v);emp=float(np.mean(tr<=t))
  se=np.sqrt(exact*(1-exact)/len(tr));assert abs(emp-exact)<6*se
  records.append(dict(m=m,n=n,v=v,count=len(Z),scaling_max_error=err,trace_mean_error_SE=z,
   trace_CDF_empirical=emp,trace_CDF_ncx2=float(exact)))
result=dict(seed=2026101910,status='PASS actual fixed-mean covariance scaling, ncx2 trace mean/CDF controls; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
(Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/noncentral-covariance-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
