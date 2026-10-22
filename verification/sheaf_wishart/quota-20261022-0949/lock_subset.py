"""Bind final headers, definitions, dependencies and the literal type checker."""
from pathlib import Path
from datetime import datetime,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
cards=[('subset-sum','FiniteSubsetFunctionSum',[
 ('L-subset-fiber-equivalence','permutation_injective_image_fiber_equiv',[]),
 ('L-subset-weight-grouping','sum_functions_eq_factorial_sum_cardinal_subsets',['L-subset-fiber-equivalence'])]),
 ('subset-cb','SubsetCauchyBinet',[
 ('L-minor-product-invariant','rectangular_minor_product_permutation_invariant',[]),
 ('L-rectangular-cauchy-binet','det_mul_rectangular_sum_cardinal_subsets',['L-subset-weight-grouping','L-minor-product-invariant']),
 ('L-subset-gram-squares','gram_det_sum_squared_cardinal_minors',['L-rectangular-cauchy-binet'])]),
 ('all-minor-coeff','GramAllMinorCoefficient',[
 ('L-enumerated-principal-gram','gram_principal_minor_eq_enumerated_gram',[]),
 ('L-gram-all-minor-coefficient-complex','gram_polynomial_coefficient_eq_sum_squared_minors',['L-subset-gram-squares','L-enumerated-principal-gram']),
 ('L-gram-minor-coefficient','gram_polynomial_coefficient_re_eq_sum_normSq_minors',['L-gram-all-minor-coefficient-complex'])])]
checker=run/'SheafSubsetTargets.lean'
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert a.read(a.SESSION/'state.json')['current_coordinator_token']==claim['token']
assert not any((run/('locks-'+tag+'.json')).exists() for tag,_,_ in cards)
locks=[]
for tag,name,nodes in cards:
 mod='JinWishartFormalization.'+name;src=a.LEAN/'JinWishartFormalization'/(name+'.lean');deps={};seen=set()
 def visit(path):
  for d in a.li.imports_of(path.read_text(encoding='utf-8')):
   p=a.LEAN/Path(d.replace('.','/')+'.lean')
   if p.exists() and d not in seen:
    seen.add(d);deps[a.rel(p)]=a.sha(p)
    o=a.LIBRARY/Path(d.replace('.','/')+'.olean');deps[a.rel(o)]=a.sha(o);visit(p)
 visit(src)
 # Include full self bytes: in particular both noncomputable enumeration/image definitions.
 deps[a.rel(src)]=a.sha(src)
 for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:deps[a.rel(p)]=a.sha(p)
 lp=run/('locks-'+tag+'.json')
 a.write(lp,dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=a.statements(src),definition_dependencies=deps,type_check_source=a.rel(checker),type_check_source_sha256=a.sha(checker),locked_local_definitions={'policy':'Full self source bytes included in definition_dependencies.'}))
 a.validate_locks(a.rel(lp));locks.append((tag,src,mod,lp))
 for ident,decl,ds in nodes:
  a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='lemma',target=(ident=='L-gram-minor-coefficient'),module=mod,declaration='JinWishart.'+decl,stmt_deps=[],proof_deps=ds,proof=[dict(text='Exact final-source finite algebra; literal theorem type and full definition hashes locked. Includes empty shapes and q>m.',uses=ds)],verification=dict(status='checked_pending_review')))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-quota-subset-locked'):
 results=[]
 for tag,src,mod,lp in locks:
  assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
  a.validate_locks(a.rel(lp));leaf=a.gated(src,mod,tag+'-20261022-locked');assert leaf['success'];results.append(leaf)
 types=a.gated(checker,checker.stem,'subset-target-types-20261022-locked',checker.parent);assert types['success']
 for (tag,src,mod,lp),leaf in zip(locks,results):
  a.validate_locks(a.rel(lp));a.write(run/('check-'+tag+'.json'),dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),leaf=leaf,types=types,lock_validated_before_and_after=True))
a.write(run/'cards.json',[dict(tag=t,module=n,nodes=nodes) for t,n,nodes in cards])
print('LOCKED_SUBSET_BUNDLE_PASS')
