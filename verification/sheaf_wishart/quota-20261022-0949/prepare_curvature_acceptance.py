"""Prepare new curvature evidence once, refusing reruns before mutations."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
cards=a.read(run/'cards-curvature.json');specpath=R/'verification/central_mixed_moments/spec.json'
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json').get('current_coordinator_token')==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
s=a.read(specpath)
assert not any(t['module'] in ['JinWishartFormalization.'+c['module'] for c in cards] for t in s['targets']), 'Refusing repeated preparation before any mutation'
assert not any((run/('acceptance-'+c['tag']+'.json')).exists() for c in cards)
for c in cards:assert a.read(run/('check-'+c['tag']+'.json'))['success']
rev=dict(request=a.rel(run/'curvature-final-review-request.json'),prompt=a.rel(run/'p4-curvature-final-prompt.txt'),receipt=a.rel(run/'p4-curvature-final.receipt.json'),raw=a.rel(run/'p4-curvature-final.raw.json'),snapshot=a.rel(run/'curvature-final-snapshot'),resolution='notes/WISHART_EXPECTED_LOGDET_CURVATURE.md')
assert a.read(R/rev['receipt'])['exit_code']==0
main=a.LEAN/'JinWishartFormalization.lean'
main.write_bytes(''.join('import JinWishartFormalization.'+c['module']+'\n' for c in cards).encode()+main.read_bytes())
for c in cards:
 tag=c['tag'];mod='JinWishartFormalization.'+c['module']
 s['targets'].append(dict(module=mod,count=len(c['nodes']),log='verification/sheaf_wishart/'+tag+'-20261022-locked.txt',kernel_exit_code_recorded=0))
 a.write(run/('acceptance-'+tag+'.json'),dict(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')),review=rev,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-66.receipt.json'))
s['controls'].append(dict(script='experiments/logdet_curvature_control.py',result=a.rel(run/'curvature-control.json'),seed=2026102205))
s['reviews'].append({k:rev[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' Further13 printed declarations/2modules: arbitrary-measure measurable nonnegativeL1 f suffices for integrable squared resolvent and derivative-under-integral resolvent formula onpositive scale; actual arbitraryfixed rectangular/singular/zeroB,M full-logdet second derivative equals negativeSUM expected squared resolvents. ActualF is concave onIoi0, strictly concave IFF min(m,rank stacked[B;M])>0; rank0 givesF=0 forrho>=0. All finite shapes; no inverse/fullrank/squareL1 premise added to scalar theorem; no new channelcoding or scaled-derivative-limit theorem.631 total bounditems (629theorem/instance+2constructions), not631 probability breakthroughs. Final-source Qoder P4 false index/neighborhood/AE-measurability warnings preserved and resolved; human differentiation/measure/model review REQUIRED. Frozenpublications unchanged/fullLake and Linuxindependentkernel NOT_RUN.'
a.write(specpath,s)
for p in list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/facade-66.receipt.json';a.write(p,d)
print('PREPARED_631; facade66 and audit required')
