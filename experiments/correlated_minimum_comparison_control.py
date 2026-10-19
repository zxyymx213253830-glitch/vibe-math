"""Fixed-seed invertible column covariance / Gram-minimum controls; not proof."""
import hashlib,json
from pathlib import Path
import numpy as np
rng=np.random.default_rng(2026101914);records=[]
for m,n in [(2,1),(3,2),(4,3)]:
 Z=(rng.standard_normal((200000,m,n))+1j*rng.standard_normal((200000,m,n)))/np.sqrt(2)
 M=np.zeros((m,n),complex);M[0,0]=0.7+0.2j
 for spread in (1.,4.):
  H=rng.standard_normal((n,n))+1j*rng.standard_normal((n,n));Q,_=np.linalg.qr(H)
  B=Q@np.diag(np.linspace(1.,spread,n))@Q.conj().T;Binv=np.linalg.inv(B)
  A=Z+M;AB=A@B
  lA=np.linalg.eigvalsh(A.conj().transpose(0,2,1)@A)[:,0]
  lAB=np.linalg.eigvalsh(AB.conj().transpose(0,2,1)@AB)[:,0]
  C=max(1.,np.linalg.norm(B,2)**2);Ci=max(1.,np.linalg.norm(Binv,2)**2)
  assert np.min(C*lA-lAB)>-1e-10 and np.min(Ci*lAB-lA)>-1e-10
  # Independent trace expectation/variance for CN rows with covariance B^H B.
  S=B.conj().T@B;MB=M@B
  tr=np.sum(abs(AB)**2,axis=(1,2));mean=m*np.trace(S).real+np.sum(abs(MB)**2)
  variance=m*np.trace(S@S).real+2*np.trace(MB@S@MB.conj().T).real
  z=float((tr.mean()-mean)/np.sqrt(variance/len(tr)));assert abs(z)<6
  # Fixed mean physical identity ZB+M = (Z+M B^-1)B.
  identity_error=float(np.max(abs((Z+M@Binv)@B-(Z@B+M))));assert identity_error<1e-11
  records.append(dict(m=m,n=n,count=len(Z),spread=spread,upper_constant=C,inverse_constant=Ci,
   min_upper_gap=float(np.min(C*lA-lAB)),min_lower_gap=float(np.min(Ci*lAB-lA)),
   trace_mean_error_SE=z,physical_mean_identity_max_error=identity_error))
result=dict(seed=2026101914,status='PASS invertible correlated-column minimum comparisons, fixed-mean identity and Gaussian trace controls; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
(Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/correlated-minimum-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
