from pathlib import Path
import hashlib,itertools,json,random,sympy as s
from sympy.combinatorics import Permutation
random.seed(2026103106); t=s.symbols('t'); good=neg=0
for n in range(0,5):
 for L in range(n+1):
  A=s.Matrix(n,n,lambda i,j: random.randint(-9,9))
  B=s.Matrix(n,n,lambda i,j: random.randint(-9,9))
  C=A+B
  for perm in itertools.permutations(range(L)):
   cols=list(perm)+list(range(L,n)); P=(B+t*A).extract(list(range(n)),cols)
   sign=Permutation(list(perm)).signature() if L else 1
   assert s.expand(P.det()-sign*(B+t*A).det())==0
   assert C.extract(list(range(n)),cols).det()==sign*C.det()
   good+=1
   if sign==-1 and C.det()!=0 and (B+t*A).det()!=0:
    assert s.expand(P.det()-(B+t*A).det())!=0;neg+=1
assert neg>0
out={'seed':2026103106,'status':'PASS','checks':good,'negative_controls':neg,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'not_a_proof':True,'scope':'active column permutation of arbitrary affine polynomial matrix; numerator and denominator signs cancel; symbolic only, not Wishart proof'}
Path('verification/sheaf_wishart/quota-20261022-0949/active-column-permutation-control.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)

