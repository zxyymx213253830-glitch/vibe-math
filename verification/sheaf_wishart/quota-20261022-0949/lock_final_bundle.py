"""Reusable immutable final-bundle gate; ordinary quota run ownership required."""
from pathlib import Path
from datetime import datetime,timezone
import sys,argparse
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
pa=argparse.ArgumentParser();pa.add_argument('--name',required=True);pa.add_argument('--checker',required=True);pa.add_argument('--modules',nargs='+',required=True);args=pa.parse_args()
checker=run/args.checker;cards=[];locks=[];previous=None
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json')['current_coordinator_token']==claim['token']
assert not (run/('cards-'+args.name+'.json')).exists(), 'One-off bundle already prepared'
for name in args.modules:
 tag=args.name+'-'+name;mod='JinWishartFormalization.'+name;src=a.LEAN/'JinWishartFormalization'/(name+'.lean');lp=run/('locks-'+tag+'.json');assert not lp.exists()
 deps={};seen=set()
 def visit(path):
  for d in a.li.imports_of(path.read_text(encoding='utf-8')):
   p=a.LEAN/Path(d.replace('.','/')+'.lean')
   if p.exists() and d not in seen:
    seen.add(d);deps[a.rel(p)]=a.sha(p);o=a.LIBRARY/Path(d.replace('.','/')+'.olean');deps[a.rel(o)]=a.sha(o);visit(p)
 visit(src);deps[a.rel(src)]=a.sha(src)
 for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:deps[a.rel(p)]=a.sha(p)
 statements=a.statements(src)
 a.write(lp,dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=statements,definition_dependencies=deps,type_check_source=a.rel(checker),type_check_source_sha256=a.sha(checker),locked_local_definitions={}))
 a.validate_locks(a.rel(lp));locks.append((tag,src,mod,lp));nodes=[]
 for index,decl in enumerate(statements):
  ident='L-'+args.name+'-'+decl.split('.')[-1];ds=[previous] if previous else []
  target=(name==args.modules[-1] and index==len(statements)-1)
  a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='lemma',target=target,module=mod,declaration=decl,stmt_deps=[],proof_deps=ds,proof=[dict(text='Final source, complete header and independent literal type locked; inherited measure/model review required.',uses=ds)],verification=dict(status='checked_pending_review')))
  nodes.append((ident,decl.split('.')[-1],ds));previous=ident
 cards.append(dict(tag=tag,module=name,nodes=nodes))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-quota-'+args.name+'-locked'):
 results=[]
 for tag,src,mod,lp in locks:
  assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
  a.validate_locks(a.rel(lp));leaf=a.gated(src,mod,tag+'-20261022-locked');assert leaf['success'];results.append(leaf)
 types=a.gated(checker,checker.stem,args.name+'-target-types-20261022-locked',checker.parent);assert types['success']
 for (tag,src,mod,lp),leaf in zip(locks,results):
  a.validate_locks(a.rel(lp));a.write(run/('check-'+tag+'.json'),dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),leaf=leaf,types=types,lock_validated_before_and_after=True))
a.write(run/('cards-'+args.name+'.json'),cards)
print('LOCKED_FINAL_BUNDLE_PASS',args.name)
