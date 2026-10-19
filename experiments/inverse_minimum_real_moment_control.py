"""Positive real inverse-Gamma moment / weighted-layercake controls; not proof."""
import hashlib,json
from pathlib import Path
from scipy.special import gammainc,gamma
from scipy.integrate import quad

records=[]
for k in range(1,6):
 for p in sorted(set((0.25,0.5,k-0.5))):
  assert 0<p<k
  # q_real=p-1 can be NEGATIVE: handle the integrable singularity at0,
  # rather than bounding by a constant as in the integer-moment proof.
  fn=lambda t:p*t**(p-1)*gammainc(k,1/t)
  near,e1=quad(fn,0,4,epsabs=1e-10,limit=300)
  far,e2=quad(fn,4,float('inf'),epsabs=1e-10,limit=300)
  closed=gamma(k-p)/gamma(k)
  assert abs(near+far-closed)<1e-7*max(1.,closed)
  records.append(dict(k=k,p=p,near_zero_integral=near,tail_integral=far,closed=closed,
   weighted_tail_exponent=p-1-k,finite_condition=p<k))
result=dict(seed=None,status='PASS real Gamma inverse moment closed forms versus weighted layercake, including near0 singular weights; not proof',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records,
 critical_statement='p=k yields weighted-tail exponent-1 and logarithmic divergence; numerical finiteness is not used to infer this')
(Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/inverse-real-moment-control.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
