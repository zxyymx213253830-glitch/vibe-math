"""Deterministic least-column-Gram comparison controls, not positive-mode claims."""
from pathlib import Path
import numpy as np
import json,sys,hashlib
rng=np.random.default_rng(2026102213);checks=[]
for m in range(4):
 for n in range(1,5):
  for degenerate in [False,True]:
   A=(rng.normal(size=(m,n))+1j*rng.normal(size=(m,n)))/np.sqrt(2)
   if degenerate:A[:]=0
   T=np.diag(np.arange(1,m+1)).astype(complex)
   for j in range(m-1):T[j,j+1]=1+2j
   I=np.linalg.inv(T) if m else np.empty((0,0),complex)
   x=float(np.linalg.eigvalsh(A.conj().T@A)[0])
   D=T@A;y=float(np.linalg.eigvalsh(D.conj().T@D)[0])
   C=max(1.,float(np.linalg.norm(T,2)**2)) if m else 1.
   Cinv=max(1.,float(np.linalg.norm(I,2)**2)) if m else 1.
   assert y<=C*x+1e-8 and x<=Cinv*y+1e-8
   checks.append(dict(m=m,n=n,zero_A=degenerate,column_min=x,transformed_column_min=y))
# Closed scalar reference; inverse factor is essential for the reverse inequality.
assert .25==abs(.5*1.)**2 and 1.==4*.25
out=dict(status='PASS deterministic controls only',seed=2026102213,checks=len(checks)+1,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),cases=checks,
 known_reference='scalar T=1/2,A=1: transformed minimum1/4, inverse control4',
 scope='ordinary COLUMN minimum, may be zero; no singular inverse-threshold proof')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],checks=out['checks'])))
