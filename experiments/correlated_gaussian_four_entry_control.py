"""Exact rational complex four-entry moment control; not a general proof."""
import hashlib, json, math
from pathlib import Path
import sympy as s

records=[]
for m,p,n in [(1,0,2),(1,1,2),(2,1,3),(2,2,3),(2,2,4)]:
    q=m*p
    z,w=s.symbols(f'z0:{q}'),s.symbols(f'w0:{q}')
    B=s.Matrix(p,n,lambda a,i:s.Rational(a+i+1,3)+s.I*s.Rational(2*a-i+1,5))
    M=s.Matrix(m,n,lambda k,i:s.Rational(k-i+1,7)+s.I*s.Rational(k+i+1,11))
    Sigma=s.conjugate(B).T*B
    def direct(k,j): return sum(B[a,j]*z[k*p+a] for a in range(p))+M[k,j]
    def conj(k,i): return sum(s.conjugate(B[a,i])*w[k*p+a] for a in range(p))+s.conjugate(M[k,i])
    choices=[(t%m,(t//2)%m,t%n,(t+1)%n,(2*t+1)%n,(3*t+2)%n) for t in range(8)]
    for k,l,i,j,u,v in dict.fromkeys(choices):
        product=s.expand(conj(k,i)*direct(k,j)*conj(l,u)*direct(l,v))
        terms=s.Poly(product,*(z+w)).terms() if q else [((),product)]
        actual=s.expand(sum(c*math.prod(math.factorial(e[a]) for a in range(q))
                 for e,c in terms if all(e[a]==e[q+a] for a in range(q))))
        delta=int(k==l)
        formula=(s.conjugate(M[k,i])*M[k,j]*s.conjugate(M[l,u])*M[l,v]
          +Sigma[i,j]*s.conjugate(M[l,u])*M[l,v]+Sigma[u,v]*s.conjugate(M[k,i])*M[k,j]
          +delta*(Sigma[i,v]*M[k,j]*s.conjugate(M[l,u])+Sigma[u,j]*s.conjugate(M[k,i])*M[l,v])
          +Sigma[i,j]*Sigma[u,v]+delta*Sigma[i,v]*Sigma[u,j])
        assert s.expand(actual-formula)==0,(m,p,n,k,l,i,j,u,v)
        records.append(dict(shape=[m,p,n],indices=[k,l,i,j,u,v],real=str(s.re(actual)),imag=str(s.im(actual))))
    # Scalar central fourth: factorial2. Deterministic zero source reduces to mean product.
    if p==0: assert all(Sigma[i,j]==0 for i in range(n) for j in range(n))
# Independent expansion of complete Gram entries, not merely one row contraction.
gram_records=[]
for m,p,n in [(1,0,2),(2,1,2),(2,2,2)]:
    q=m*p
    z,w=s.symbols(f'g0:{q}'),s.symbols(f'h0:{q}')
    B=s.Matrix(p,n,lambda a,i:s.Rational(a+i+1,3)+s.I*s.Rational(2*a-i+1,5))
    M=s.Matrix(m,n,lambda k,i:s.Rational(k-i+1,7)+s.I*s.Rational(k+i+1,11))
    Sigma=s.conjugate(B).T*B; A=s.conjugate(M).T*M; K=m*Sigma+A
    def gp(i,j):
        return sum((sum(s.conjugate(B[a,i])*w[k*p+a] for a in range(p))+s.conjugate(M[k,i]))*
          (sum(B[a,j]*z[k*p+a] for a in range(p))+M[k,j]) for k in range(m))
    def moment(poly):
        terms=s.Poly(s.expand(poly),*(z+w)).terms() if q else [((),s.expand(poly))]
        return s.expand(sum(c*math.prod(math.factorial(e[a]) for a in range(q))
                    for e,c in terms if all(e[a]==e[q+a] for a in range(q))))
    for i,j,u,v in [(0,0,1,1),(0,1,1,0),(0,1,0,1),(1,1,1,1)]:
        result=moment(gp(i,j)*gp(u,v))
        candidate=K[i,j]*K[u,v]+m*Sigma[i,v]*Sigma[u,j]+Sigma[i,v]*A[u,j]+Sigma[u,j]*A[i,v]
        assert s.expand(result-candidate)==0
        gram_records.append(dict(shape=[m,p,n],indices=[i,j,u,v]))
    trace=sum(gp(i,i) for i in range(n))
    tr2=sum(gp(i,j)*gp(j,i) for i in range(n) for j in range(n))
    expected_spectral=m*m*s.trace(Sigma*Sigma)+m*s.trace(Sigma)**2+2*m*s.trace(Sigma*A)+2*s.trace(Sigma)*s.trace(A)+s.trace(A*A)
    expected_variance=m*s.trace(Sigma*Sigma)+2*s.trace(Sigma*A)
    assert s.expand(moment(tr2)-expected_spectral)==0
    assert s.expand(moment(trace*trace)-s.trace(K)**2-expected_variance)==0

report=dict(seed=None,status='PASS exact rational-complex general four-entry contractions incl rectangular/singular/empty-source controls; NOT general proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,gram_records=gram_records)
Path('verification/central_mixed_moments/correlated-four-entry-control.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'],len(records))
