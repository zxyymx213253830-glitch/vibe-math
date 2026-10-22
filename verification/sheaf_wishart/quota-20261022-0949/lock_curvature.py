"""Lock and check the reviewed curvature bundle through the shared gate."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
checker=run/'SheafCurvatureTargets.lean';cards=[];locks=[];previous=None
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json')['current_coordinator_token']==claim['token']
assert not (run/'cards-curvature.json').exists(), 'One-off locked preparation'
for tag,name in [('curvature','ExpectedLogDetCurvature'),('strict-concavity','ExpectedLogDetStrictConcavity')]:
 mod='JinWishartFormalization.'+name;src=a.LEAN/'JinWishartFormalization'/(name+'.lean');deps={};seen=set()
 def visit(path):
  for d in a.li.imports_of(path.read_text(encoding='utf-8')):
   p=a.LEAN/Path(d.replace('.','/')+'.lean')
   if p.exists() and d not in seen:
    seen.add(d);deps[a.rel(p)]=a.sha(p)
    o=a.LIBRARY/Path(d.replace('.','/')+'.olean');deps[a.rel(o)]=a.sha(o);visit(p)
 visit(src);deps[a.rel(src)]=a.sha(src)
 for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:deps[a.rel(p)]=a.sha(p)
 lp=run/('locks-'+tag+'.json');assert not lp.exists()
 statements=a.statements(src)
 a.write(lp,dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=statements,definition_dependencies=deps,type_check_source=a.rel(checker),type_check_source_sha256=a.sha(checker),locked_local_definitions={}))
 a.validate_locks(a.rel(lp));locks.append((tag,src,mod,lp))
 nodes=[]
 for decl in statements:
  ident='L-curvature-'+decl.split('.')[-1];ds=[previous] if previous else []
  a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='lemma',target=decl.endswith('strictConcave_iff'),module=mod,declaration=decl,stmt_deps=[],proof_deps=ds,proof=[dict(text='Full source and literal independent expected type locked. Includes zero shapes; stochastic inherited measure/model review required.',uses=ds)],verification=dict(status='checked_pending_review')))
  nodes.append((ident,decl.split('.')[-1],ds));previous=ident
 cards.append(dict(tag=tag,module=name,nodes=nodes))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-quota-curvature-locked'):
 results=[]
 for tag,src,mod,lp in locks:
  assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
  a.validate_locks(a.rel(lp));leaf=a.gated(src,mod,tag+'-20261022-locked');assert leaf['success'];results.append(leaf)
 types=a.gated(checker,checker.stem,'curvature-target-types-20261022-locked',checker.parent);assert types['success']
 for (tag,src,mod,lp),leaf in zip(locks,results):
  a.validate_locks(a.rel(lp));a.write(run/('check-'+tag+'.json'),dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),leaf=leaf,types=types,lock_validated_before_and_after=True))
a.write(run/'cards-curvature.json',cards)
print('LOCKED_CURVATURE_BUNDLE_PASS')
