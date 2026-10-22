"""Exact proper-CN1 rectangular frame controls; not a distributional proof."""
from pathlib import Path
import json, random, sys
import sympy as s
SEED=2026102223
rng=random.Random(SEED)
checks=0

def check(c, label):
    global checks
    if not c: raise AssertionError(label)
    checks+=1

def eq(A,B):
    return A.shape==B.shape and all(s.simplify(x-y)==0 for x,y in zip(A,B))

def unitary(n):
    if n==0:return s.zeros(0,0)
    v=s.Matrix([rng.randint(-2,2)+s.I*rng.randint(-2,2) for _ in range(n)])
    if eq(v,s.zeros(n,1)):v[0]=1
    return (s.eye(n)-2*v*v.conjugate().T/(v.conjugate().T*v)[0]).applyfunc(s.simplify)

cases=0
conjugation_negative=0
for m,p,b in [(m,p,b) for m in range(4) for p in range(5) for b in range(p+1)]:
    cases+=1
    V=unitary(m); U=unitary(p)[:,:b]
    check(eq(U.conjugate().T*U,s.eye(b)), 'isometric columns')
    check(eq(V.conjugate().T*V,s.eye(m)), 'row unitary')
    # Row-major vectorization: vec(V Z U)=(V tensor U^T) vec(Z).
    K=s.kronecker_product(V,U.T) if m*b*m*p else s.zeros(m*b,m*p)
    C=(K*K.conjugate().T).applyfunc(s.simplify)
    check(eq(C,s.eye(m*b)), 'complex coisometry')
    A=K.applyfunc(s.re); B=K.applyfunc(s.im)
    R=A.row_join(-B).col_join(B.row_join(A))
    check(eq(R*R.T,s.eye(2*m*b)), 'encoded real coisometry')
    check(eq(s.Rational(1,2)*R*R.T,s.eye(2*m*b)/2), 'proper real covariance one half')
    check(eq((A+s.I*B)*(A+s.I*B).T+(s.I*A-B)*(s.I*A-B).T,s.zeros(m*b,m*b)), 'zero pseudo covariance')
    z=s.Matrix(m,p,[rng.randint(-2,2)+s.I*rng.randint(-2,2) for _ in range(m*p)])
    w=V*z*U
    check(eq(K*s.Matrix(m*p,1,list(z)),s.Matrix(m*b,1,list(w))), 'pointwise vectorization')
    for a in range(m+1):
        # Each complex output row block is a set of independent coordinates.
        hi=list(range(a*b));lo=list(range(a*b,m*b))
        check(eq(C.extract(hi,lo),s.zeros(len(hi),len(lo))), 'row block cross covariance zero')
    check(s.simplify(sum(C[i,i] for i in range(m*b))-m*b)==0, 'known CN1 total energy')
    if m*b:
        check(not eq(R*R.T,s.eye(2*m*b)/2),'missing sqrt2 negative control')
    if m*p and m*b:
        wrong=V*z*U.conjugate()
        if not eq(w,wrong):conjugation_negative+=1
check(cases==60,'shape count')
check(conjugation_negative>0,'pointwise conjugation error detected')
result=dict(seed=SEED,cases=cases,checks=checks,conjugation_negative_cases=conjugation_negative,
    known_controls=['identity/empty shapes','U^HU=I','CN1 component variance 1/2','E Frobenius energy=mb'],
    scope='Exact finite covariance and pointwise controls only; no general Gaussian or independence proof',status='PASS')
if len(sys.argv)>1:Path(sys.argv[1]).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
