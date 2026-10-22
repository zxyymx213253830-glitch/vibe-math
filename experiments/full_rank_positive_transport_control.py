"""Full small-side rank positive-coordinate sandwich controls, not proof."""
from pathlib import Path
import hashlib
import json,sys
import numpy as np
SEED=2026102225
rng=np.random.default_rng(SEED);checks=0;cases=0
for m in range(1,5):
 for n in range(1,5):
  for _ in range(3):
   cases+=1
   A=rng.integers(-3,4,(m,n))+1j*rng.integers(-3,4,(m,n))
   # Full rank is a theorem premise, enforced here by a known diagonal anchor.
   if np.linalg.matrix_rank(A)<min(m,n):
    A=np.eye(m,n,dtype=complex)
   T=np.eye(n,dtype=complex)+np.tril(rng.integers(-2,3,(n,n))+1j*rng.integers(-2,3,(n,n)),-1)
   AT=A@T; R=min(m,n)
   s=np.linalg.svd(A,compute_uv=False);t=np.linalg.svd(AT,compute_uv=False)
   la=float(s[R-1]**2);lb=float(t[R-1]**2)
   C=max(1.,float(np.linalg.norm(T,2)**2));D=max(1.,float(np.linalg.norm(np.linalg.inv(T),2)**2))
   assert la>0 and lb>0; checks+=1
   assert lb<=C*la+1e-8; checks+=1
   assert la<=D*lb+1e-8; checks+=1
   ea=np.linalg.eigvalsh(A.conj().T@A)[::-1]
   eb=np.linalg.eigvalsh(AT.conj().T@AT)[::-1]
   assert abs(ea[R-1]-la)<1e-8 and abs(eb[R-1]-lb)<1e-8;checks+=1
   if m<n:
    assert abs(ea[-1])<1e-8; checks+=1
    assert abs(np.linalg.eigvalsh(A@A.conj().T)[0]-la)<1e-8;checks+=1
# Known scalar exact scaling and rank-zero exclusion.
for z in [1.,2.+1j,-3j]:
 A=np.array([[2.+1j]]);T=np.array([[z]])
 assert abs(np.linalg.svd(A@T,compute_uv=False)[0]**2-5*abs(z)**2)<1e-10;checks+=1
assert np.linalg.matrix_rank(np.zeros((2,3)))!=min(2,3);checks+=1
out=dict(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seed=SEED,cases=cases,checks=checks,status='PASS',scope='Controls only; full-rank premise and ordinary-column-zero distinction enforced',known_controls=['scalar exact scaling','wide last-column zero','row/column positive match','rank-zero excluded'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
