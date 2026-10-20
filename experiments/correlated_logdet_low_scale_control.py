"""Fixed-seed actual correlated low-scale logdet controls, not a proof."""
import hashlib,json
from pathlib import Path
import numpy as np
seed=2026102001
rng=np.random.default_rng(seed); records=[]; samples=200000
cases=[(2,np.eye(2,dtype=complex),np.zeros((2,2),complex),'identity Gamma trace'),
 (2,np.array([[1+1j,2-1j]],complex)/3,np.array([[1,2j],[1j,-1]],complex)/5,'rank-one singular'),
 (2,np.array([[1,1j],[2-1j,1],[1+2j,-1]],complex)/4,np.array([[1,1j],[2,-1j]],complex)/7,'rectangular'),
 (2,np.zeros((0,2),complex),np.array([[1,1j],[2,-1j]],complex)/3,'deterministic zero source')]
for m,B,M,label in cases:
 p,n=B.shape
 Z=(rng.normal(size=(samples,m,p))+1j*rng.normal(size=(samples,m,p)))/np.sqrt(2)
 X=Z@B+M;W=X.conj().transpose(0,2,1)@X
 lam=np.linalg.eigvalsh(W)
 assert lam.min()>-1e-10
 lam=np.maximum(lam,0)
 S=B.conj().T@B;A=M.conj().T@M;K=m*S+A
 T=np.trace(K).real
 C2=(np.trace(K@K)+m*np.trace(S)**2+2*np.trace(S)*np.trace(A)).real/2
 tr=lam.sum(axis=1); half2=(lam*lam).sum(axis=1)/2
 def assert_mean(x,expect):
  se=x.std(ddof=1)/np.sqrt(samples)
  assert abs(x.mean()-expect)<=6*se+1e-10,(label,x.mean(),expect,se)
 assert_mean(tr,T);assert_mean(half2,C2)
 if label.startswith('identity'): assert T==4 and abs(C2-8)<1e-12 # Etrace=mn and Etrace(W^2)/2=mn(m+n)/2.
 rs=[1e-2,1e-3,1e-4];errors=[]
 for r in rs:
  logv=np.log1p(r*lam).sum(axis=1)
  gap=(r*lam-np.log1p(r*lam)).sum(axis=1)/(r*r)
  assert gap.min()>-1e-9
  errors.append(abs(gap.mean()-half2.mean()))
 assert errors[2]<errors[1]<errors[0]+1e-12
 assert errors[2]<=0.003*max(1,abs(half2.mean()))
 records.append(dict(case=label,shape=[m,p,n],T=float(T),half_second=float(C2),
  empirical_T=float(tr.mean()),empirical_half_second=float(half2.mean()),r=rs,curvature_errors=errors))
report=dict(seed=seed,samples=samples,status='PASS actual correlated low-scale trace/curvature, Gamma and singular/zero-source controls; NOT proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
Path('verification/central_mixed_moments/correlated-logdet-low-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'])
