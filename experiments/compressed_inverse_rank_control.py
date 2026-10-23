"""Exact compression/rank controls before common-kernel inverse transport.
Reference matrices have b noise and c fixed kernel-image coordinates.
"""
from pathlib import Path
import hashlib,json,random
import sympy as sp
seed=2026102236;rng=random.Random(seed)
checks=cases=wrong_ambient=0
for a in range(1,4):
 for b in range(1,4):
  for c in range(1,4):
   for extra in [1,2]:
    m,r,n=a+c,b+c,b+c+extra
    B=sp.zeros(b,n);M=sp.zeros(m,n)
    for j in range(b):
     B[j,j]=j+1
     for i in range(m):M[i,j]=rng.randrange(-2,3)+sp.I*rng.randrange(-1,2)
    for j in range(c):M[a+j,b+j]=j+1
    order=list(range(n));rng.shuffle(order)
    P=sp.eye(n)[:,order];B=B*P;M=M*P
    C=P.conjugate().T[:,:r];Bc,Mc=B*C,M*C
    assert C.conjugate().T*C==sp.eye(r);checks+=1
    assert Bc*C.conjugate().T==B and Mc*C.conjugate().T==M;checks+=2
    assert B.col_join(M).rank()==r==Bc.col_join(Mc).rank();checks+=1
    assert B.rank()==Bc.rank()==b;checks+=1
    assert len(Bc.nullspace())==r-b==c;checks+=1
    assert abs(m-r)+1==abs(a-b)+1;checks+=1
    wrong_ambient+=int(abs(m-n)+1!=abs(m-r)+1)
    cases+=1
assert wrong_ambient>0;checks+=1
out=dict(status='PASS exact rank controls, not probability proof',seed=seed,
 checks=checks,cases=cases,wrong_ambient_negative_cases=wrong_ambient,
 reference='coordinate noise/fixed kernel-image matrices under column permutations',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/compressed-inverse-rank-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
