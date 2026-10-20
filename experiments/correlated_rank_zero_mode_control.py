"""Exact controls for mean restoration versus a deterministic zero Gram mode."""
import hashlib,json
from pathlib import Path
import sympy as s
a,b=s.symbols('a b',real=True)
B=s.Matrix([[1,0]])
Z=s.Matrix([[a],[b]])
M=s.Matrix([[0,0],[0,1]])
X=Z*B+M
assert s.expand((X.H*X).det())==a*a
assert B.rank()==1 and B.col_join(M).rank()==2
assert X.subs({a:1,b:3}).rank()==2
assert X.subs({a:0,b:3}).rank()==1
M0=s.zeros(2,2)
X0=Z*B+M0
assert (X0.H*X0).det()==0 and B.col_join(M0).rank()==1
deterministic=s.Matrix([[0,1],[2,0]])
assert (s.zeros(2,1)*s.zeros(1,2)+deterministic).rank()==2
assert (deterministic.H*deterministic).det()==4
report=dict(seed=None,status='PASS exact mean-restored and deficient Gram controls; NOT an almost-sure proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 restored_gram_det='a^2',rankB=1,restored_stacked_rank=2,deficient_stacked_rank=1,
 wrong_singular_B_implies_zero_min_detected=True,
 wrong_pointwise_rank_attainment_detected=True,
 zero_B_nonzero_M_deterministic_full_rank=True)
Path('verification/central_mixed_moments/correlated-rank-zero-mode-control.json').write_text(
 json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(report['status'])
