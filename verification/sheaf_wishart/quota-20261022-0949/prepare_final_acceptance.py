"""Prepare a new immutable reviewed bundle, checking rerun guards first."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
c=a.read(run/sys.argv[1]);cards=a.read(run/('cards-'+c['name']+'.json'))
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json').get('current_coordinator_token')==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
state=a.read(a.SESSION/'state.json')
if state.get('user_hard_deadline'):assert datetime.now(timezone.utc)<datetime.fromisoformat(state['user_deadline_utc'])
sp=R/'verification/central_mixed_moments/spec.json';s=a.read(sp)
assert not any(t['module'] in ['JinWishartFormalization.'+card['module'] for card in cards] for t in s['targets']), 'Refusing repeated preparation before mutation'
assert not any((run/('acceptance-'+card['tag']+'.json')).exists() for card in cards)
def review_paths(name):
 return dict(request=a.rel(run/(name+'-review-request.json')),prompt=a.rel(run/('p4-'+name+'-prompt.txt')),receipt=a.rel(run/('p4-'+name+'.receipt.json')),raw=a.rel(run/('p4-'+name+'.raw.json')),snapshot=a.rel(run/(name+'-snapshot')),resolution=c['resolution'])
overrides=c.get('review_for_module',{})
assert set(overrides).issubset({card['module'] for card in cards})
reviews={name:review_paths(name) for name in dict.fromkeys([c['review']]+list(overrides.values()))}
requests={name:a.read(R/rev['request']) for name,rev in reviews.items()}
for rev in reviews.values():assert a.read(R/rev['receipt'])['exit_code']==0
for card in cards:
 review_name=overrides.get(card['module'],c['review']);rev=reviews[review_name];req=requests[review_name]
 tag=card['tag'];a.validate_locks(a.rel(run/('locks-'+tag+'.json')))
 assert a.read(run/('check-'+tag+'.json'))['success']
 src=a.LEAN/'JinWishartFormalization'/(card['module']+'.lean')
 assert req['inputs'][src.name]['sha256']==a.sha(src)
 assert a.sha(R/rev['snapshot']/src.name)==a.sha(src)
controls=[dict(script=c['control_script'],result=c['control_result'],seed=c['seed'])]+c.get('additional_controls',[])
for index,control in enumerate(controls):
 if index==0 and c.get('reuse_control',False):
  assert control in s['controls'], 'A reused control must already be identically audit-bound'
 else:
  assert control not in s['controls'], 'A new control must not silently duplicate an existing control'
  assert list(control)==['script','result','seed'], 'Control metadata must preserve the audit schema'
  evidence=a.read(R/control['result'])
  assert evidence['seed']==control['seed'] and evidence['status']=='PASS'
  assert evidence['source_sha256']==a.sha(R/control['script'])
main=a.LEAN/'JinWishartFormalization.lean'
main.write_bytes(''.join('import JinWishartFormalization.'+card['module']+'\n' for card in cards).encode()+main.read_bytes())
for card in cards:
 rev=reviews[overrides.get(card['module'],c['review'])]
 tag=card['tag'];s['targets'].append(dict(module='JinWishartFormalization.'+card['module'],count=len(card['nodes']),log='verification/sheaf_wishart/'+tag+'-20261022-locked.txt',kernel_exit_code_recorded=0))
 a.write(run/('acceptance-'+tag+'.json'),dict(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')),review=rev,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/'+c['facade']+'.receipt.json'))
for index,control in enumerate(controls):
 if not (index==0 and c.get('reuse_control',False)):s['controls'].append(control)
for rev in reviews.values():s['reviews'].append({k:rev[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' '+c['scope'];a.write(sp,s)
for p in list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/'+c['facade']+'.receipt.json';a.write(p,d)
print('PREPARED',c['total'],'requires facade and audit')
