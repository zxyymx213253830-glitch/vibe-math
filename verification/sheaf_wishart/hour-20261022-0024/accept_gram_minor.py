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
assert not any(t['module'] in ['JinWishartFormalization.GramRankSpectralCoefficient','JinWishartFormalization.RectangularDeterminantExpansion'] for t in prior['targets']), 'Refusing repeated preparation before any mutation'
main=a.LEAN/'JinWishartFormalization.lean'
main.write_bytes(b'import JinWishartFormalization.GramRankSpectralCoefficient\nimport JinWishartFormalization.RectangularDeterminantExpansion\n'+main.read_bytes())
s=a.read(R/'verification/central_mixed_moments/spec.json')
review=dict(request=a.rel(run/'gram-minor-review-request.json'),prompt=a.rel(run/'p4-gram-minor-prompt.txt'),receipt=a.rel(run/'p4-gram-minor.receipt.json'),raw=a.rel(run/'p4-gram-minor.raw.json'),snapshot=a.rel(run/'gram-minor-snapshot'),resolution='notes/WISHART_GRAM_RANK_COEFFICIENT.md')
for tag,name in [('spectral','GramRankSpectralCoefficient'),('minor','RectangularDeterminantExpansion')]:
 mod='JinWishartFormalization.'+name
 assert not any(t['module']==mod for t in s['targets'])
 s['targets'].append(dict(module=mod,count=5,log='verification/sheaf_wishart/gram-minor-'+tag+'-20261022-locked.txt',kernel_exit_code_recorded=0))
 a.write(run/('acceptance-'+tag+'.json'),dict(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')),review=review,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-62.receipt.json'))
s['controls'].append(dict(script='experiments/compression_pseudodet_bridge_control.py',result='verification/sheaf_wishart/hour-20261021-1201/compression-bridge-control-3.json',seed=2026102126))
s['reviews'].append({k:review[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' 2026-10-22 ten deterministic finite-algebra declarations: Gram determinant polynomial rank coefficient is positive nonzero-eigenvalue product and its log is positive-spectrum log sum; rank-sized injective coordinate minor exists via raw rectangular all-functions expansion. No subset Cauchy-Binet or new unconditional singular offset yet. Qoder log_prod positivity alarm resolved against exact nonzero-factor API.595 total bound items; human model review REQUIRED.'
a.write(R/'verification/central_mixed_moments/spec.json',s)
paths=list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']
for p in paths:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/facade-62.receipt.json';a.write(p,d)
print('PREPARED_595; facade62 and auditor still required')
