"""Exact fixed-right-inverse controls, not a uniform general theorem."""
import hashlib,itertools,json
from pathlib import Path
import sympy as s
records=[]
for m,r in [(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)]:
    n=m+r
    U=s.eye(n)
    for j in range(n-1):
        U[j,j+1]=1+s.I
    B=s.eye(r).row_join(s.zeros(r,m))*U
    D=s.diag(*range(1,m+1))
    A=s.Matrix(m,r,lambda i,j:s.Rational(i+j+1,3)+s.I*s.Rational(i-j,5))
    M=A.row_join(D)*U
    C=U.inv()*s.zeros(r,m).col_join(D.inv())
    assert (B*C).applyfunc(s.simplify)==s.zeros(r,m) and (M*C).applyfunc(s.simplify)==s.eye(m)
    normsq=s.simplify(s.trace(C.H*C))
    floor=1/normsq
    assert floor>0
    for k in range(5):
        Z=s.Matrix(m,r,lambda i,j:s.Rational(k-2+i,2)+s.I*s.Rational(j-k,3))
        X=(Z*B+M).applyfunc(s.expand)
        assert (X*C).applyfunc(s.simplify)==s.eye(m)
        lower=(X*X.H-floor*s.eye(m)).applyfunc(s.simplify)
        for size in range(1,m+1):
            for ix in itertools.combinations(range(m),size):
                assert s.simplify(lower.extract(ix,ix).det())>=0
        records.append(dict(m=m,r=r,samples_index=k,frobenius_floor=str(floor),rank=X.rank()))
z=s.symbols('z',real=True)
assert s.Matrix([[z,1]]).multiply(s.Matrix([[z],[1]]))[0,0]==z*z+1
report=dict(seed=None,status='PASS exact fixed-right-inverse spectral-floor controls; NOT general proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,
 known_scalar_rowgram='|z|^2+1 >=1',naive_rank_only_hard_edge_exponent_not_valid_here=True)
Path('verification/central_mixed_moments/correlated-noiseless-floor-control.json').write_text(
 json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(records))
