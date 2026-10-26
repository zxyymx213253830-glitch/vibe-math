"""Finite exact zero-confluent coefficient blocks; calibration only."""
from pathlib import Path
import sympy as S
import numpy as np
import json,hashlib
SEED=2026102607;rng=np.random.default_rng(SEED);checks=[]
def ck(n,b):
 assert b,n
 checks.append(n)
def A(p,lam):
 L=len(lam)
 return S.Matrix(p+L,p+L,lambda i,j:(S.Integer(i==j) if j<p else lam[j-p]**i))
for p in range(6):
 for L in range(6):
  lam=[S.Integer(j+2)*(-1)**j for j in range(L)]
  M=A(p,lam)
  v=S.prod(lam[j]-lam[i] for i in range(L) for j in range(i+1,L))
  d=S.prod(z**p for z in lam)*v
  ck(f'coefficient-zero confluent block determinant {p,L}',M.det()==d)
  ck(f'nonzero distinct roots invertibility including empty {p,L}',M.det()!=0)
  c=S.Matrix(1,p+L,[S.Integer(int(a)) for a in rng.integers(-5,6,size=p+L)])
  out=c*M
  ck(f'first p outputs are coefficients {p,L}',all(out[j]==c[j] for j in range(p)))
  ck(f'last L outputs are evaluations {p,L}',all(out[p+j]==sum(c[k]*lam[j]**k for k in range(p+L)) for j in range(L)))
  if L>=2:
   rep=lam.copy();rep[-1]=rep[0]
   ck(f'repeated root negative {p,L}',A(p,rep).det()==0)
  if p>0 and L>0:
   zero=lam.copy();zero[-1]=S.Integer(0)
   ck(f'zero root conflicts with zero coefficient block {p,L}',A(p,zero).det()==0)
ck('no coefficient block permits zero root',A(0,[S.Integer(0),S.Integer(2)]).det()==2)
ck('omitting root power factor negative',A(2,[S.Integer(2)]).det()!=1)
R=Path(__file__).resolve().parents[1]
d=dict(seed=SEED,status='PASS',checks=len(checks),controls=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite calibration, not a general matrix or probability theorem.')
(R/'verification/sheaf_wishart/quota-20261022-0949/zero-confluent-vandermonde-control.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print('PASS',len(checks),'exact controls; not proof')
