from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
from datetime import datetime,timezone
claim=a.read(a.PROJECT/'coord/claims/cauchy-binet-hour-20261022.lock')
assert a.read(a.SESSION/'state.json').get('current_coordinator_token')==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['hard_deadline_utc'])
prior=a.read(R/'verification/central_mixed_moments/spec.json')
assert not any(t['module']=='JinWishartFormalization.ExpectedLogDetDerivative' for t in prior['targets']), 'Refusing repeated preparation before any mutation'
main=a.LEAN/'JinWishartFormalization.lean'
main.write_bytes(b'import JinWishartFormalization.ExpectedLogDetDerivative\n'+main.read_bytes())
s=a.read(R/'verification/central_mixed_moments/spec.json');mod='JinWishartFormalization.ExpectedLogDetDerivative'
assert not any(t['module']==mod for t in s['targets'])
s['targets'].append(dict(module=mod,count=2,log='verification/sheaf_wishart/expected-derivative-20261022-locked.txt',kernel_exit_code_recorded=0))
s['controls'].append(dict(script='experiments/logdet_derivative_control.py',result=a.rel(run/'logdet-derivative-control.json'),seed=2026102203))
rev=dict(request=a.rel(run/'derivative-exactapi-review-request.json'),prompt=a.rel(run/'p4-derivative-exactapi-prompt.txt'),receipt=a.rel(run/'p4-derivative-exactapi.receipt.json'),raw=a.rel(run/'p4-derivative-exactapi.raw.json'),snapshot=a.rel(run/'derivative-exactapi-snapshot'),resolution='notes/WISHART_EXPECTED_LOGDET_DERIVATIVE.md')
s['reviews'].append({k:rev[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' Two further printed declarations: arbitrary-measure measurable nonnegative L1 f has derivative-under-integral log(1+rho f) at every rho>0, with integrable f/(1+rho f). Actual fixed arbitraryfactor full-logdet expectation derivative is SUM E eigenvalue/(1+rho eigenvalue), all finite shapes and no rank/inverse premise. No derivative at0/concavity/coding theorem claimed.610 bound items (608 theorem/instance+2constructions). Exact-API finalsource Qoder P4 conditional AE-decomposition alarm resolved against actual pointwise spectral signature; human derivative/integral/model review REQUIRED.'
a.write(R/'verification/central_mixed_moments/spec.json',s)
a.write(run/'acceptance-expected-derivative.json',dict(target_lock=a.rel(run/'locks-expected-derivative.json'),check=a.rel(run/'check-expected-derivative.json'),review=rev,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-64.receipt.json'))
for p in list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/facade-64.receipt.json';a.write(p,d)
print('PREPARED_610; facade64 and auditor still required')
