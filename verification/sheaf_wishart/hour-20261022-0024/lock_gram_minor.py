from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
checker=run/'SheafGramMinorTargets.lean'
configs=[('spectral','GramRankSpectralCoefficient',[
 ('L-hermitian-complex-parameter','hermitian_det_one_add_complex_smul',[]),
 ('L-hermitian-polynomial-identity','hermitian_det_polynomial_eq_product',['L-hermitian-complex-parameter']),
 ('L-gram-rank-coefficient-product','gram_rank_coefficient_eq_nonzero_product',['L-hermitian-polynomial-identity']),
 ('L-gram-rank-coefficient-positive','gram_rank_coefficient_re_pos',['L-gram-rank-coefficient-product']),
 ('L-gram-rank-spectral-coefficient','gram_rank_coefficient_log_eq_positive_sum',['L-gram-rank-coefficient-product','L-gram-rank-coefficient-positive'])]),
 ('minor','RectangularDeterminantExpansion',[
 ('L-rectangular-all-functions','det_mul_rectangular_sum_functions',[]),
 ('L-repeated-row-zero','det_submatrix_eq_zero_of_not_injective',[]),
 ('L-extract-row-minor','exists_injective_row_minor_of_mul_det_ne_zero',['L-rectangular-all-functions','L-repeated-row-zero']),
 ('L-extract-coordinate-minor','exists_coordinate_minor_of_compression_det_ne_zero',['L-extract-row-minor']),
 ('S18-rank-coordinate-minor','exists_rank_coordinate_minor',['L-extract-coordinate-minor'])])]
locks=[]
for tag,name,nodes in configs:
 mod='JinWishartFormalization.'+name;src=a.LEAN/'JinWishartFormalization'/(name+'.lean');deps={};seen=set()
 def visit(path):
  for d in a.li.imports_of(path.read_text(encoding='utf-8')):
   p=a.LEAN/Path(d.replace('.','/')+'.lean')
   if p.exists() and d not in seen:
    seen.add(d);deps[a.rel(p)]=a.sha(p);o=a.LIBRARY/Path(d.replace('.','/')+'.olean');deps[a.rel(o)]=a.sha(o);visit(p)
 visit(src)
 for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:deps[a.rel(p)]=a.sha(p)
 lock=dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=a.statements(src),definition_dependencies=deps,
  type_check_source=a.rel(checker),type_check_source_sha256=a.sha(checker),locked_local_definitions={})
 lp=run/('locks-'+tag+'.json');a.write(lp,lock);a.validate_locks(a.rel(lp));locks.append((tag,src,mod,lp))
 for ident,decl,ds in nodes:
  a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='target' if ident.startswith('S18') else 'lemma',target=ident.startswith('S18'),module=mod,declaration='JinWishart.'+decl,stmt_deps=[],proof_deps=ds,proof=[dict(text='Deterministic finite algebra; exact source and target type locked.',uses=ds)],verification=dict(status='checked_pending_review')))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-hour-gram-minor-locked'):
 results=[]
 for tag,src,mod,lp in locks:
  a.validate_locks(a.rel(lp));leaf=a.gated(src,mod,'gram-minor-'+tag+'-20261022-locked');assert leaf['success'];results.append(leaf)
 types=a.gated(checker,checker.stem,'gram-minor-types-20261022-locked',checker.parent);assert types['success']
 for (tag,src,mod,lp),leaf in zip(locks,results):
  a.validate_locks(a.rel(lp));a.write(run/('check-'+tag+'.json'),dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),leaf=leaf,types=types,lock_validated_before_and_after=True))
print('LOCKED_GRAM_MINOR_PASS')
