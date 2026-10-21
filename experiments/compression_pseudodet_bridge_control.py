"""Exact Cauchy--Binet coefficient controls for the next unproved bridge."""
from pathlib import Path
from itertools import combinations,product
import hashlib,json,sys,time
import numpy as np
import sympy as s
SEED=2026102126
rng=np.random.default_rng(SEED)
x=s.Symbol('x');checks=[]
def record(name,ok,**details):
    if not bool(ok):raise AssertionError(name)
    checks.append(dict(name=name,**details))
def matrix(m,n):
    return s.Matrix(m,n,lambda i,j:s.Rational(int(rng.integers(-2,3)),2)+s.I*s.Rational(int(rng.integers(-2,3)),2))
start=time.monotonic()
for m in range(5):
 for n in range(5):
  for variant in range(2):
   A=matrix(m,n)
   if variant and n>1:A[:,n-1]=A[:,0]
   G=A.conjugate().T*A
   poly=s.Poly((s.eye(n)+x*G).det(),x)
   rank=A.rank()
   for q in range(min(n,3)+1):
    C=A[:,list(range(q))]
    # Row multilinearity over ALL functions, before injective/image grouping.
    expansion=s.S.Zero
    for f in product(range(m),repeat=q):
     weight=s.prod(s.conjugate(C[f[i],i]) for i in range(q))
     expansion+=weight*C.extract(f,range(q)).det()
    record(f'all-functions-row-expansion-{m}-{n}-{variant}-{q}',s.simplify(expansion-(C.conjugate().T*C).det())==0)
   for q in range(n+1):
    minor_sum=s.S.Zero
    for ii in combinations(range(m),q):
     for jj in combinations(range(n),q):
      d=s.expand(A.extract(ii,jj).det())
      minor_sum+=s.expand(d*s.conjugate(d))
    coeff=s.expand(poly.nth(q))
    record(f'coefficient-minor-squares-{m}-{n}-{variant}-{q}',s.simplify(coeff-minor_sum)==0)
   c=s.expand(poly.nth(rank))
   record(f'rank-coefficient-positive-{m}-{n}-{variant}',c>0,rank=rank)
   if rank:
    # The selected fixed coordinate minor is nonzero at this deterministic witness.
    ds=[s.expand(A.extract(ii,jj).det()) for ii in combinations(range(m),rank) for jj in combinations(range(n),rank)]
    d=next(v for v in ds if v!=0)
    norm2=s.expand(d*s.conjugate(d))
    record(f'chosen-compression-domination-{m}-{n}-{variant}',c>=norm2)
    S=float(s.log(c));T=float(s.re(s.trace(G)));lp=float(s.log(norm2))/2
    record(f'aggregate-log-domination-{m}-{n}-{variant}',abs(S)<=T+2*abs(lp)+1e-10)
   else:record(f'rank-zero-empty-product-{m}-{n}-{variant}',c==1)
record('missing-conjugation-negative-control',(s.I*s.I)!=s.I*s.conjugate(s.I))
record('extra-factorial-negative-control',s.eye(2).det()!=s.factorial(2)*s.eye(2).det())
A=s.diag(2,0)
record('singular-column-det-is-not-pseudodet-negative-control',(A.conjugate().T*A).det()==0 and (s.eye(2)+x*(A.conjugate().T*A)).det().coeff(x)==4)
record('totalized-log0-does-not-justify-AE-nonzero',s.log(s.Rational(1,100))<0,explanation='For X=diag(1/10,0) and a zero chosen minor, log pseudoDet=log(1/100)<0=2*totalizedLog0; so log comparison requires nonzero minor AE.')
out=dict(status='PASS exact finite controls; NOT a general proof',seed=SEED,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=len(checks),details=checks,seconds=time.monotonic()-start,scope='Rational complex dimensions0..4, duplicated columns, rank0 and conjugation negative controls. No probability/measure theorem.')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seconds']}))
