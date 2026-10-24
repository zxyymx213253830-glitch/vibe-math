"""Exact pre-source controls for polynomial orthogonality/Christoffel route."""
from pathlib import Path
import hashlib,json
import sympy as sp
import numpy as np
seed=2026102404;rng=np.random.default_rng(seed);X=sp.Symbol('X');checks=0
for n in range(11):
 p=sp.Poly(sum((-1)**(n+k)*sp.factorial(n)*sp.binomial(n,k)*X**k/sp.factorial(k) for k in range(n+1)),X)
 assert p.degree()==n and p.LC()==1;checks+=1
 for j in range(n):
  assert sum(p.nth(k)*sp.factorial(k+j) for k in range(n+1))==0;checks+=1
 for x in [sp.Rational(0),sp.Rational(1,3),sp.I,1+2*sp.I]:
  L=sum(sp.binomial(n,k)*x**k/sp.factorial(k) for k in range(n+1))
  assert sp.expand((-1)**n*p.eval(-x)-sp.factorial(n)*L)==0;checks+=1
for n in range(6):
 # Arbitrary complex linear functional, no positivity/multiplicativity.
 moments=[sp.Integer(int(rng.integers(-5,6)))+sp.I*int(rng.integers(-3,4)) for _ in range(2*n+1)]
 H=sp.Matrix(n,n,lambda i,j:moments[i+j])
 if H.det()==0: continue
 coeff=-H.inv()*sp.Matrix(n,1,lambda i,j:moments[i+n])
 p=X**n+sum(coeff[k]*X**k for k in range(n))
 for x in [sp.Rational(0),sp.Rational(2,3),sp.I]:
  M=sp.Matrix(n,n,lambda i,j:moments[i+j+1]+x*moments[i+j])
  assert sp.simplify(M.det()-(-1)**n*H.det()*p.subs(X,-x))==0;checks+=1
# P1's replacement of the tridiagonal Jacobi matrix by its diagonal is false.
x=sp.Symbol('x');assert sp.expand((x+1)*(x+3)-(sp.Matrix([[x+1,1],[1,x+3]])).det())==1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact finite controls; not general proof',
 reference='Signed monic factorial-Laguerre orthogonality; arbitrary complex linear moment functional Christoffel identity; tridiagonal/diagonal negative control',
 scope='Orthogonality n<=10, generic complex moment n<=5; positivity not assumed',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/christoffel-factorial-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
