"""Lock a declared bundle and run the existing serial gate, without renewing the hour."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
config=a.read(run/sys.argv[1]);checker=run/config['checker'];locks=[]
claim=a.read(a.PROJECT/'coord/claims/cauchy-binet-hour-20261022.lock')
assert a.read(a.SESSION/'state.json')['current_coordinator_token']==claim['token']
for card in config['modules']:
 tag,name=card['tag'],card['module'];mod='JinWishartFormalization.'+name;src=a.LEAN/'JinWishartFormalization'/(name+'.lean');deps={};seen=set()
 def visit(path):
  for d in a.li.imports_of(path.read_text(encoding='utf-8')):
   p=a.LEAN/Path(d.replace('.','/')+'.lean')
   if p.exists() and d not in seen:
    seen.add(d);deps[a.rel(p)]=a.sha(p);o=a.LIBRARY/Path(d.replace('.','/')+'.olean');deps[a.rel(o)]=a.sha(o);visit(p)
 visit(src)
 for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:deps[a.rel(p)]=a.sha(p)
 lp=run/('locks-'+tag+'.json');assert not lp.exists()
 a.write(lp,dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=a.statements(src),definition_dependencies=deps,type_check_source=a.rel(checker),type_check_source_sha256=a.sha(checker),locked_local_definitions={}))
 a.validate_locks(a.rel(lp));locks.append((tag,src,mod,lp))
 for ident,decl,ds in card['nodes']:
  a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='target' if ident.startswith('S17') else 'lemma',target=ident.startswith('S17'),module=mod,declaration='JinWishart.'+decl,stmt_deps=[],proof_deps=ds,proof=[dict(text='Locked final-source proof; precise target type checked separately. Human measure/model review required when stochastic.',uses=ds)],verification=dict(status='checked_pending_review')))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-hour-bundle-locked'):
 results=[]
 for tag,src,mod,lp in locks:
  assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['hard_deadline_utc'])
  a.validate_locks(a.rel(lp));leaf=a.gated(src,mod,tag+'-20261022-locked');assert leaf['success'];results.append(leaf)
 types=a.gated(checker,checker.stem,config['types_tag'],checker.parent);assert types['success']
 for (tag,src,mod,lp),leaf in zip(locks,results):
  a.validate_locks(a.rel(lp));a.write(run/('check-'+tag+'.json'),dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),leaf=leaf,types=types,lock_validated_before_and_after=True))
print('LOCKED_BUNDLE_PASS')
