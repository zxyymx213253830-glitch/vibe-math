"""Original central square2 T3 transcription controls; before source, not proof."""
from pathlib import Path
import random,json,hashlib
import sympy as s
seed=2026102413;rng=random.Random(seed);checks=0
x,e=s.symbols('x e',real=True)
P=e*s.Matrix([[x*x+2*x+2,x+1],[x+1,1]]);Z=s.Matrix([[2,1],[1,1]]);Q=Z-P
mix=lambda A,B:s.Matrix([list(A.row(0)),list(B.row(1))]).det()+s.Matrix([list(B.row(0)),list(A.row(1))]).det()
assert s.expand(mix(P,Q)-((x*x+2)*e-2*e*e))==0;checks+=1
assert s.expand(mix(P,Q)-(Z.det()-P.det()-Q.det()))==0;checks+=1
for _ in range(60):
 A=s.Matrix(2,2,lambda i,j:rng.randrange(-4,5)+s.I*rng.randrange(-3,4));B=s.Matrix(2,2,lambda i,j:rng.randrange(-4,5)+s.I*rng.randrange(-3,4))
 assert s.expand(mix(A,B)-((A+B).det()-A.det()-B.det()))==0;checks+=1
A=s.diag(1,-1);B=s.eye(2)
terms=[s.Matrix([list(A.row(0)),list(B.row(1))]).det(),s.Matrix([list(B.row(0)),list(A.row(1))]).det()]
assert sum(terms)!=sum(abs(t) for t in terms);checks+=1
assert s.prod(s.factorial(2-(i+1)) for i in range(2))==1;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact controls; not proof',reference='Unchanged s=t=2 L0 k2 c3=1, exact mixed-row sum equals actual crossing closed expression, arbitrary complex det-add relation, determinant-versus-modulus negative control',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/original-two-t3-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
