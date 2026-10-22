"""One-off evidence preparation; all refusal checks precede source/spec changes."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
cards=a.read(run/'cards.json');specpath=R/'verification/central_mixed_moments/spec.json'
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json').get('current_coordinator_token')==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
s=a.read(specpath)
assert not any(t['module'] in ['JinWishartFormalization.'+c['module'] for c in cards] for t in s['targets']), 'Refusing repeated preparation before any mutation'
assert not any((run/('acceptance-'+c['tag']+'.json')).exists() for c in cards)
for c in cards:assert a.read(run/('check-'+c['tag']+'.json'))['success']
rev=dict(request=a.rel(run/'subset-final-review-request.json'),prompt=a.rel(run/'p4-subset-final-prompt.txt'),receipt=a.rel(run/'p4-subset-final.receipt.json'),raw=a.rel(run/'p4-subset-final.raw.json'),snapshot=a.rel(run/'subset-final-snapshot'),resolution='notes/WISHART_EXACT_SUBSET_CAUCHY_BINET.md')
assert a.read(R/rev['receipt'])['exit_code']==0
main=a.LEAN/'JinWishartFormalization.lean'
prefix=''.join('import JinWishartFormalization.'+c['module']+'\n' for c in cards)
main.write_bytes(prefix.encode()+main.read_bytes())
for c in cards:
 tag=c['tag'];mod='JinWishartFormalization.'+c['module']
 s['targets'].append(dict(module=mod,count=len(c['nodes']),log='verification/sheaf_wishart/'+tag+'-20261022-locked.txt',kernel_exit_code_recorded=0))
 a.write(run/('acceptance-'+tag+'.json'),dict(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')),review=rev,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-65.receipt.json'))
s['controls'].append(dict(script='experiments/subset_cauchy_binet_control.py',result=a.rel(run/'subset-control.json'),seed=2026102204))
s['reviews'].append({k:rev[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' 2026-10-22 quota continuation: eight further printed finite-algebra declarations in3modules; fixed-cardinality image fibers/permutation-invariant function-sum grouping, exact subset rectangular Cauchy-Binet and Gram squares, exact ALL row/column squared-minor polynomial coefficient. All natural shapes incl0 andq>m; overC, factorial cancellation characteristic0. Earlier historical OPEN subset/all-minor cards are now superseded by verified identities; not a new probability law.618 total bounditems (616 theorem/instance+2constructions); local enumeration/image definitions source-locked but not counted as extra theorem breakthroughs. Real final-source Qoder P4 false finite-equivalence/API/empty-case concerns explicitly resolved in notes/WISHART_EXACT_SUBSET_CAUCHY_BINET.md. Human inherited measure/model review REQUIRED; fullLake and independentLinuxkernel NOT_RUN, frozen publications unchanged.'
a.write(specpath,s)
for p in list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/facade-65.receipt.json';a.write(p,d)
print('PREPARED_618; facade65 and audit required before accept')
