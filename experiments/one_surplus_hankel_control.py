"""Exact pre-source controls for one-surplus central T1 determinant bridge."""
from pathlib import Path
import hashlib,json,math
import sympy as sp
x=sp.Symbol('x');seed=2026102403;checks=0
for n in range(9):
 H0=sp.Matrix(n,n,lambda i,j:sp.factorial(i+j))
 H1=sp.Matrix(n,n,lambda i,j:sp.factorial(i+j+1))
 A=sp.Matrix(n,n,lambda i,j:sp.factorial(i)*sp.binomial(i,j))
 J=sp.Matrix(n,n,lambda i,j:2*i+1 if i==j else max(i,j) if abs(i-j)==1 else 0)
 assert H0==A*A.T;checks+=1
 assert H1==A*J*A.T;checks+=1
 L=sum(sp.binomial(n,k)*x**k/sp.factorial(k) for k in range(n+1))
 denominator=math.prod(math.factorial(i)*math.factorial(i+1) for i in range(n))
 pencil=H1+x*H0
 assert sp.expand(pencil.det(method='domain-ge')-denominator*L)==0;checks+=1
 upper=sp.Matrix(n,n,lambda i,j:sp.factorial(i+j+1)*sum(x**k/sp.factorial(k) for k in range(i+j+2)))
 assert sp.expand(upper.det(method='domain-ge')-denominator*L)==0;checks+=1
 assert sp.expand((J+x*sp.eye(n)).det(method='domain-ge')-sp.factorial(n)*L)==0;checks+=1
 assert sp.expand(sp.laguerre(n,-x)-L)==0;checks+=1
# Missing nonconstant Laguerre factor fails in the first nontrivial dimension.
assert (sp.Matrix([[1+x]]).det()-1).subs(x,1)==1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact finite algebra; not a general proof',
 reference='Factorial/Pascal Gram factor; Laguerre polynomial; explicit integer upper-Gamma polynomial; n=0 empty determinant',
 scope='n<=8 exact controls; no new actual probability law and no general determinant proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/one-surplus-hankel-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
