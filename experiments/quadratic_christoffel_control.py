"""Exact bilinear (not Hermitian) confluent Christoffel controls before Lean.
Seed2026102502. Controls are not proofs; calibrated n0/n1 closed identities.
"""
from pathlib import Path
import hashlib,json,random,time
import sympy as s
SEED=2026102502
rng=random.Random(SEED); X=s.Symbol('X'); checks=[]
def ck(label,v):
    assert v,label
    checks.append(label)
def monic_orthogonal(n,mom):
    if n==0:return s.Integer(1)
    H=s.Matrix(n,n,lambda i,j:mom(i+j))
    c=H.inv()*s.Matrix([-mom(n+i) for i in range(n)])
    return X**n+sum(c[i]*X**i for i in range(n))
def evaluate(n,mom,p,q,z,label):
    H=s.Matrix(n,n,lambda i,j:mom(i+j)).det()
    D=s.Matrix(n,n,lambda i,j:mom(i+j+2)-2*z*mom(i+j+1)+z*z*mom(i+j)).det()
    W=(p*s.diff(q,X)-q*s.diff(p,X)).subs(X,z)
    ck(label+' identity',s.simplify(D-H*W)==0)
    ck(label+' orthogonality',all(s.expand(X**i*p).as_poly(X).eval(0)==s.expand(X**i*p).as_poly(X).eval(0) and s.simplify(sum(a*mom(k[0]) for k,a in s.Poly(X**i*p,X).terms()))==0 and s.simplify(sum(a*mom(k[0]) for k,a in s.Poly(X**i*q,X).terms()))==0 for i in range(n)))
    return D,H,W
ck('empty determinant',s.det(s.zeros(0))==1)
for n in range(9):
    p=(-1)**n*s.factorial(n)*s.laguerre(n,X)
    q=(-1)**(n+1)*s.factorial(n+1)*s.laguerre(n+1,X)
    z=s.Rational(rng.randint(-5,5),2)+s.I*s.Rational(rng.randint(-3,3),3)
    D,H,W=evaluate(n,s.factorial,p,q,z,'factorial n'+str(n))
    ck('factorial H closed n'+str(n),H==s.prod(s.factorial(k)**2 for k in range(n)))
    if n==1:ck('n1 closed',s.expand(D-(z*z-2*z+2))==0)
    if n>=3:ck('omitted H rejected n'+str(n),s.simplify(D-W)!=0)
    if n>=1:ck('wrong sign rejected n'+str(n),s.simplify(D+H*W)!=0)
for trial in range(8):
    nodes=[-2,-1,0,2,3,5]
    weights=[s.Rational(rng.randint(1,9),rng.randint(1,5))*(1 if trial<4 else (1+s.I*(j%2))) for j in range(6)]
    mom=lambda k:sum(w*a**k for a,w in zip(nodes,weights))
    for n in range(4):
        p=monic_orthogonal(n,mom);q=monic_orthogonal(n+1,mom)
        z=s.Rational(rng.randint(-3,4),3)+s.I/2
        evaluate(n,mom,p,q,z,'discrete '+str(trial)+' n'+str(n))
for n in range(1,5):
    evaluate(n,lambda k:s.Integer(0),X**n,X**(n+1),s.I,'zero functional n'+str(n))
result=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controls=checks,scope='Exact calibrated factorial and discrete complex linear functionals including zero functional; not proof, not actual CDF mapping')
out=Path('verification/sheaf_wishart/quota-20261022-0949/quadratic-christoffel-control.json')
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls')
