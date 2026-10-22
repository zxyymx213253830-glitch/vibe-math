"""Exact rank identity with deliberately deficient A and invertible N."""
from pathlib import Path
import hashlib,json,random,sys
import sympy as s
SEED=2026102234;rng=random.Random(SEED);checks=0;cases=0
for a in range(4):
 for b in range(4):
  for c in range(4):
   cases+=1
   # Rank at most1, with zero cases included, even when min(a,b)>1.
   A=s.Matrix(a,1,[rng.randint(-1,1)+s.I*rng.randint(-1,1) for _ in range(a)])*s.ones(1,b)
   H=s.Matrix(c,b,[rng.randint(-2,2)+s.I*rng.randint(-1,1) for _ in range(c*b)])
   N=s.eye(c)
   for i in range(c):
    N[i,i]=i+1
    for j in range(i):N[i,j]=rng.randint(-2,2)+s.I
   D=A.row_join(s.zeros(a,c)).col_join(H.row_join(N))
   assert D.rank()==A.rank()+c;checks+=1
   E=A.row_join(s.zeros(a,c)).col_join(s.zeros(c,b).row_join(N))
   assert E.rank()==A.rank()+c;checks+=1
   assert (N.inv()*H).shape==(c,b);checks+=1
# Invertibility of N is essential to the stated +c formula.
assert s.zeros(2,2).rank()!=s.zeros(1,1).rank()+1;checks+=1
out=dict(seed=SEED,cases=cases,checks=checks,status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Exact finite rank controls, not a general rank proof',known_controls=['rank-one/zero outer-product A','invertible triangular N','empty dimensions','singular N negative control'])
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
