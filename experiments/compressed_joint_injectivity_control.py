"""Rank/reconstruction imply compressed stacked injectivity: exact controls."""
from pathlib import Path
import hashlib,json,random,sys
import sympy as s
SEED=2026102226;rng=random.Random(SEED);checks=0;cases=0
for m,p,n in [(0,0,0),(0,0,2),(0,2,2),(2,0,2),(1,1,2),(1,2,3),(2,1,3),(2,2,2),(1,1,3),(3,2,1)]:
 for zero in [False,True]:
  cases+=1
  A=s.zeros(m+p,n) if zero else s.Matrix(m+p,n,[rng.randint(-2,2)+s.I*rng.randint(-1,2) for _ in range((m+p)*n)])
  cols=A.conjugate().T.columnspace();C=s.Matrix.hstack(*s.GramSchmidt(cols,orthonormal=True)) if cols else s.zeros(n,0)
  r=int(A.rank());F=(A*C).applyfunc(s.simplify)
  assert C.cols==r;checks+=1
  assert (A*C*C.conjugate().T-A).applyfunc(s.simplify)==s.zeros(m+p,n);checks+=1
  assert F.rank()==r;checks+=1
  assert len(F.nullspace())==0;checks+=1
  # Reconstruction alone is insufficient without matching the rank-sized width.
  bad=C.row_join(s.zeros(n,1));G=A*bad
  assert (A*bad*bad.conjugate().T-A).applyfunc(s.simplify)==s.zeros(m+p,n);checks+=1
  assert G.cols!=r and len(G.nullspace())>0;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact reconstruction/rank/kernel controls, not a general proof',known_controls=['zero-dimensional map','zero factor/common kernel','rank-sized full column rank','extra zero column negative'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
