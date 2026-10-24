"""Split Andreief/count determinant exact controls, before source; not proof."""
from pathlib import Path
import itertools,hashlib,json,random,math
import sympy as s
seed=2026102411;rng=random.Random(seed);t=s.symbols('t');checks=0
for n in range(5):
 for repeat in range(5):
  points=[-1,0,2];w=[rng.randrange(1,4) for _ in points]
  f=[[rng.randrange(-3,4) for _ in points] for i in range(n)]
  g=[[rng.randrange(-3,4) for _ in points] for i in range(n)]
  E=[a<=repeat-2 for a in points]
  A=s.Matrix(n,n,lambda i,j:sum(w[k]*f[i][k]*g[j][k] for k in range(3) if E[k]))
  B=s.Matrix(n,n,lambda i,j:sum(w[k]*f[i][k]*g[j][k] for k in range(3) if not E[k]))
  moments=[0]*(n+1)
  for z in itertools.product(range(3),repeat=n):
   val=math.prod(w[k] for k in z)*s.Matrix(n,n,lambda i,j:f[i][z[j]]).det()*s.Matrix(n,n,lambda i,j:g[i][z[j]]).det()
   moments[sum(E[k] for k in z)]+=val
  poly=s.Poly((B+t*A).det(),t)
  for k in range(n+1):
   assert math.factorial(n)*poly.nth(k)==moments[k];checks+=1
  for a in [-2,0,1,3]:
   assert math.factorial(n)*poly.eval(a)==sum(a**k*moments[k] for k in range(n+1));checks+=1
# Explicit factorial negative calibration for n2 f=g=(1,y), atoms0,1.
atomic_integral=sum(s.Matrix([[1,1],[a,b]]).det()**2 for a in [0,1] for b in [0,1])
atomic_moment_det=s.Matrix([[2,1],[1,1]]).det()
assert atomic_integral==2*atomic_moment_det and atomic_integral!=atomic_moment_det;checks+=1
out=dict(seed=seed,checks=checks,status='PASS exact controls; not proof',reference='Exact discrete Andreief including empty dimension, signed f/g, atomic thresholds, zero and negative t, coefficient count masses and factorial negative calibration',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('verification/sheaf_wishart/quota-20261022-0949/split-andreief-count-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
