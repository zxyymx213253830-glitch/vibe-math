"""Fixed-mean disjoint row/column selectors: exact controls, not a law proof."""
from pathlib import Path
import json,random,sys
import sympy as s
SEED=2026102224
rng=random.Random(SEED); checks=0; cases=0

def check(v,label):
 global checks
 if not v:raise AssertionError(label)
 checks+=1

def selector(m,n,rows,cols):
 S=s.zeros(len(rows)*len(cols),m*n)
 for a,i in enumerate(rows):
  for b,j in enumerate(cols):S[a*len(cols)+b,i*n+j]=1
 return S

for m,n in [(0,0),(0,3),(3,0),(1,1),(1,4),(4,1),(2,3),(3,2),(3,3),(4,4)]:
 M=s.Matrix(m,n,[rng.randint(-3,3)+s.I*rng.randint(-3,3) for _ in range(m*n)])
 for axis,size in [('row',m),('column',n)]:
  perm=list(range(size));rng.shuffle(perm)
  for cut in range(size+1):
   cases+=1; e=perm[:cut];f=perm[cut:]
   S=selector(m,n,e,list(range(n))) if axis=='row' else selector(m,n,list(range(m)),e)
   T=selector(m,n,f,list(range(n))) if axis=='row' else selector(m,n,list(range(m)),f)
   check(S*S.T==s.eye(S.rows),'first marginal unit covariance')
   check(T*T.T==s.eye(T.rows),'second marginal unit covariance')
   check(S*T.T==s.zeros(S.rows,T.rows),'cross covariance zero')
   A=M.extract(e,list(range(n))) if axis=='row' else M.extract(list(range(m)),e)
   B=M.extract(f,list(range(n))) if axis=='row' else M.extract(list(range(m)),f)
   vec=s.Matrix(m*n,1,list(M))
   check(S*vec==s.Matrix(A.rows*A.cols,1,list(A)),'actual selected first mean')
   check(T*vec==s.Matrix(B.rows*B.cols,1,list(B)),'actual selected second mean')
   check(s.Rational(1,2)*S*S.T==s.eye(S.rows)/2,'proper real variance half')
   if S.rows:check(S*S.T!=s.zeros(S.rows,S.rows),'overlap negative independence control')
result=dict(seed=SEED,cases=cases,checks=checks,status='PASS',scope='Exact shifted mean/covariance selectors only, not Gaussian independence proof',known_controls=['empty blocks','permuted partitions','proper CN1 variance half','overlap negative'])
if len(sys.argv)>1:Path(sys.argv[1]).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
