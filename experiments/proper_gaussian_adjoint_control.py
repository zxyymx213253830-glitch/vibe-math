"""Exact signed-coordinate/variance controls for shifted proper-CN1 adjoint law."""
from pathlib import Path
import hashlib,json,sys,time
import sympy as sp
seed=2026102219; start=time.monotonic(); checks=[]; cases=[]
for m in range(4):
 for n in range(4):
  size=2*m*n
  x=sp.Matrix(sp.symbols('x:'+str(size),real=True)) if size else sp.zeros(0,1)
  T=sp.zeros(size,size)
  for i in range(m):
   for j in range(n):
    for k in range(2):
     T[2*(j*m+i)+k,2*(i*n+j)+k]=1 if k==0 else -1
  assert T*T.T==sp.eye(size) and T.T*T==sp.eye(size)
  checks.append('signed-coordinate-orthogonal-bijection')
  y=T*x
  Z=sp.Matrix(m,n,lambda i,j:(x[2*(i*n+j)]+sp.I*x[2*(i*n+j)+1])/sp.sqrt(2))
  Y=sp.Matrix(n,m,lambda i,j:(y[2*(i*m+j)]+sp.I*y[2*(i*m+j)+1])/sp.sqrt(2))
  assert (Y-Z.conjugate().T).applyfunc(sp.simplify)==sp.zeros(n,m)
  checks.append('actual-properCN1-encoded-adjoint')
  M=sp.Matrix(m,n,lambda i,j:i+j+1+sp.I*(2*i-j+1))
  assert ((Z+M).conjugate().T-(Y+M.conjugate().T)).applyfunc(sp.simplify)==sp.zeros(n,m)
  checks.append('fixed-mean-must-adjoint')
  if size:
   # Independent standard real coordinates: both component variances=1/2.
   dr=[sp.diff(sp.re(Y[0,0]),v) for v in x]
   di=[sp.diff(sp.im(Y[0,0]),v) for v in x]
   assert sp.simplify(sum(v*v for v in dr))==sp.Rational(1,2)
   assert sp.simplify(sum(v*v for v in di))==sp.Rational(1,2)
   assert sp.simplify(sum(v*w for v,w in zip(dr,di)))==0
   checks.append('known-proper-variance-one-reference')
  else:
   assert size==0 and Y.rows*Y.cols==0
   checks.append('empty-law-singleton-reference')
  cases.append(dict(m=m,n=n,real_dimension=size))
assert sp.conjugate(1+2*sp.I)!=1+2*sp.I
checks.append('negative-control-untransformed-mean')
out=dict(status='PASS exact controls only; not a general measure-law proof',seed=seed,checks=len(checks),
 cases=cases,check_labels=checks,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checks','seed','seconds']}))
