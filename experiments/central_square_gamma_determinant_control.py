"""Exact central-square T1 determinant controls, not a general proof."""
from pathlib import Path
import hashlib,json,math,random
import sympy as s
seed=2026102246; rng=random.Random(seed); checks=0; records=[]
for n in range(9):
    H0=s.Matrix(n,n,lambda i,j:s.factorial(i+j))
    P=s.Matrix(n,n,lambda i,j:s.binomial(i,j))
    D=s.diag(*[s.factorial(i) for i in range(n)])
    assert H0==D*P*P.T*D; checks+=1
    mass=math.prod(math.factorial(i)**2 for i in range(n))
    assert H0.det()==mass; checks+=1
    for _ in range(5):
        x=s.Rational(rng.randint(0,9),rng.randint(1,6))
        H=s.Matrix(n,n,lambda i,j:s.factorial(i+j)*sum(x**a/s.factorial(a) for a in range(i+j+1)))
        T=s.Matrix(n,n,lambda i,j:s.binomial(i,j)*x**(i-j) if j<=i else 0)
        assert H==T*H0*T.T; checks+=1
        assert T.det()==1 and H.det()==mass; checks+=1
        # Reversing both rows/columns gives the actual Gamma index 2n-i-j-2.
        Rev=s.Matrix(n,n,lambda i,j:H[n-1-i,n-1-j])
        assert Rev.det()==mass; checks+=1
    records.append(dict(n=n,zero_threshold_determinant=mass))
x=s.Symbol('x',nonnegative=True)
for n in range(1,5):
    H=s.Matrix(n,n,lambda i,j:s.factorial(i+j)*sum(x**a/s.factorial(a) for a in range(i+j+1)))
    assert s.expand(H.det())==math.prod(math.factorial(i)**2 for i in range(n)); checks+=1
# Known dimensions1 and2 agree with Gamma1 and the existing actual Exp(rate2).
for n in [1,2]:
    assert s.simplify(s.exp(-x)**n-s.exp(-n*x))==0; checks+=1
# New generic functional controls precede the monic-basis/translation source.
# Complex shifts require transpose, not conjugate transpose; positivity is unused.
for n in range(7):
    for _ in range(3):
        shift=s.Rational(rng.randint(-3,3),2)+s.I*s.Rational(rng.randint(-2,2),3)
        moments=[s.Rational(rng.randint(-4,4),3)+s.I*s.Rational(rng.randint(-3,3),2) for k in range(max(1,2*n))]
        H=s.Matrix(n,n,lambda i,j:moments[i+j])
        T=s.Matrix(n,n,lambda i,j:s.binomial(i,j)*shift**(i-j) if j<=i else 0)
        G=s.Matrix(n,n,lambda i,j:sum(s.binomial(i+j,k)*shift**(i+j-k)*moments[k] for k in range(i+j+1)))
        assert (G-T*H*T.T).applyfunc(s.expand)==s.zeros(n); checks+=1
        assert s.expand(G.det()-H.det())==0; checks+=1
# New factorial-functional recurrence/Gamma-polynomial checks before its source.
for k in range(13):
    shift=s.Rational(rng.randint(-4,5),3)+s.I*s.Rational(rng.randint(-2,2),2)
    y=s.Symbol('y')
    def F(poly):
        pp=s.Poly(s.expand(poly),y)
        return s.expand(sum(pp.nth(a)*s.factorial(a) for a in range(max(0,pp.degree())+1))) if pp else s.Integer(0)
    poly=sum((s.Rational(rng.randint(-4,4),2)+s.I*rng.randint(-2,2))*y**a for a in range(k+1))
    assert s.expand(F(poly)-poly.subs(y,0)-F(s.diff(poly,y)))==0; checks+=1
    assert s.expand(F((y+shift)**k)-s.factorial(k)*sum(shift**a/s.factorial(a) for a in range(k+1)))==0; checks+=1
out=dict(status='PASS exact finite controls; not general determinant/probability proof',seed=seed,
    checks=checks,records=records,reference='Gamma integer finite sum; H0=D Pascal Pascal.T D; unit triangular translation; known Exp(rate1/rate2)',
    empty_dimension='Algebra determinant1 only; no minimum-positive eigenvalue claimed at n0',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/central-square-gamma-determinant-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
