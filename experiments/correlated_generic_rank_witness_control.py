"""Exact finite affine-rank witnesses; NOT the general a.s. rank theorem."""
import hashlib,json
from pathlib import Path
import sympy as s
records=[];wrong_full=wrong_noise=0
for m,p,n in [(0,0,0),(0,2,3),(2,0,3),(2,1,3),(3,2,4),(2,4,3),(3,3,3),(4,2,4),(1,2,4),(3,1,1)]:
 for rank in range(min(p,n)+1):
  U=s.eye(n)
  for i in range(n-1):U[i,i+1]=1+s.I
  J=s.zeros(p,n)
  for i in range(rank):J[i,i]=1
  B=J*U
  for extra in range(min(m,n-rank)+1):
   Mbar=s.Matrix(m,n,lambda i,j:(s.Rational(i+j+1,3)+s.I*s.Rational(i-j,5)) if j<rank else
      (1 if j-rank<extra and i==j-rank else 0))
   M=Mbar*U
   basis=B.nullspace();ker=s.Matrix.hstack(*basis) if basis else s.zeros(n,0)
   r=B.rank();extra_actual=(M*ker).rank();target=min(m,r+extra_actual)
   assert r==rank and extra_actual==extra
   V=s.zeros(m,rank);q=min(rank,m-extra)
   for j in range(q):V[extra+j,j]=1
   Z=s.zeros(m,p)
   for i in range(m):
    for j in range(rank):Z[i,j]=s.expand(V[i,j]-Mbar[i,j])
   X=(Z*B+M).applyfunc(s.expand);actual=X.rank()
   assert actual==target
   wrong_full+=int(target!=min(m,n));wrong_noise+=int(target!=min(m,r))
   records.append(dict(shape=[m,p,n],rankB=r,rank_M_on_kernel=extra_actual,predicted=target,witness_rank=actual,
      Z=[[str(Z[i,j]) for j in range(p)] for i in range(m)]))
assert wrong_full>0 and wrong_noise>0
report=dict(seed=None,status='PASS exact rational-complex finite affine-rank witnesses and wrong-fullrank/noise-only controls; NOT general proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,
 wrong_fullrank_detected=wrong_full,wrong_noise_only_detected=wrong_noise)
Path('verification/central_mixed_moments/correlated-generic-rank-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(records))
