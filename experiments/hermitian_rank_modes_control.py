"""Exact Hermitian/Gram rank controls and floating spectral cross-check."""
import hashlib,json
from pathlib import Path
import sympy as s
import numpy as np
records=[]
matrices=[s.zeros(0,0),s.diag(-2,0,1),s.Matrix([[1,s.I],[-s.I,1]]),
 s.Matrix([[1,2,s.I],[0,1,1-s.I]]).conjugate().T*s.Matrix([[1,2,s.I],[0,1,1-s.I]])]
for A in matrices:
 assert A==A.conjugate().T
 rank=A.rank();n=A.rows
 vals=np.linalg.eigvalsh(np.array(A.tolist(),complex)) if n else np.array([])
 nz=int(np.count_nonzero(np.abs(vals)>1e-9));positive=int(np.count_nonzero(vals>1e-9))
 assert rank==nz
 psd=all(x>=-1e-9 for x in vals)
 if psd:assert rank==positive
 records.append(dict(n=n,rank=rank,nonzero_modes=nz,positive_modes=positive,psd=psd))
assert records[1]['rank']!=records[1]['positive_modes'] # PSD premise required for positive count.
report=dict(seed=None,status='PASS exact Hermitian/Gram rank and positive-mode controls incl empty/indefinite negative; NOT general proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
Path('verification/central_mixed_moments/hermitian-rank-modes-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'])
