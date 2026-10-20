"""Exact finite controls for square compression, not a general rank proof."""
import hashlib
import json
from pathlib import Path
import sympy as s

records = []
negative_full_gram = 0
for m, p, n in [(0,0,0),(0,2,3),(2,0,3),(2,1,3),(3,2,4),(2,4,3),
                 (3,3,3),(4,2,4),(1,2,4),(3,1,1)]:
    for r in range(min(p,n)+1):
        U=s.eye(n)
        for i in range(n-1):
            U[i,i+1]=1+s.I
        J=s.zeros(p,n)
        for i in range(r):
            J[i,i]=1
        B=J*U
        for extra in range(min(m,n-r)+1):
            Mbar=s.Matrix(m,n,lambda i,j:(s.Rational(i+j+1,3)+s.I*s.Rational(i-j,5))
                          if j<r else (1 if j-r<extra and i==j-r else 0))
            M=Mbar*U
            Z=s.zeros(m,p)
            for i in range(m):
                for j in range(r):
                    Z[i,j]=(1 if j<min(r,m-extra) and i==extra+j else 0)-Mbar[i,j]
            X=(Z*B+M).applyfunc(s.expand)
            q=X.rank()
            C,F=X.rank_decomposition()
            if q:
                L=(C.H*C).inv()*C.H
                H=F.H*(F*F.H).inv()
            else:
                L=s.zeros(0,m)
                H=s.zeros(n,0)
            compressed=(L*X*H).applyfunc(s.simplify)
            assert compressed==s.eye(q) and compressed.det()==1
            reconstructed=s.Matrix(m,p,lambda i,j:
                s.simplify((s.sqrt(2)*s.re(Z[i,j])+s.I*s.sqrt(2)*s.im(Z[i,j]))/s.sqrt(2)))
            assert reconstructed==Z
            stacked=B.col_join(M)
            assert stacked.rank()==r+extra
            assert q==min(m,stacked.rank())
            if 0<q<n:
                assert (X.H*X).det()==0
                negative_full_gram+=1
            records.append(dict(shape=[m,p,n],q=q,compression_determinant='1',
                                square_size=q,stacked_rank=stacked.rank()))
assert negative_full_gram>0
report=dict(seed=None,status='PASS finite exact square-compression and real-coordinate controls; NOT general proof',
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            records=records,wrong_full_gram_witness_detected=negative_full_gram)
Path('verification/central_mixed_moments/correlated-rank-compression-control.json').write_text(
    json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(records))
