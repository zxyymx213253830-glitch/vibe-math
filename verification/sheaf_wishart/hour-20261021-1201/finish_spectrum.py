"""One-hour evidence preparation; uses the existing serial compiler gate only."""
from pathlib import Path
import sys,json
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
run=Path(__file__).parent
mod='JinWishartFormalization.PositiveSpectrumLogIntegrability'
src=a.LEAN/Path(mod.replace('.','/')+'.lean')
checker=run/'SheafSpectrumTargets.lean'
deps={}
seen=set()
def visit(path):
    for name in a.li.imports_of(path.read_text(encoding='utf-8')):
        p=a.LEAN/Path(name.replace('.','/')+'.lean')
        if p.exists() and name not in seen:
            seen.add(name)
            deps[a.rel(p)]=a.sha(p)
            o=a.LIBRARY/Path(name.replace('.','/')+'.olean')
            deps[a.rel(o)]=a.sha(o)
            visit(p)
visit(src)
for p in [a.LEAN/'lean-toolchain',a.LEAN/'lake-manifest.json']:
    deps[a.rel(p)]=a.sha(p)
lock=dict(created_utc=a.now(),module=mod,source=a.rel(src),statements=a.statements(src),
          definition_dependencies=deps,type_check_source=a.rel(checker),
          type_check_source_sha256=a.sha(checker),locked_local_definitions={})
lp=run/'locks-spectrum.json'
a.write(lp,lock)
a.validate_locks(a.rel(lp))
nodes=[('L-positive-log-upper','positiveSpectrumLog_le_self',[],False),
 ('L-mode-log-domination','abs_positiveSpectrumLog_le_trace_add_abs_sum',['L-positive-log-upper'],False),
 ('L-mode-log-L1','integrable_positiveSpectrumLog_of_sum',['L-mode-log-domination'],False),
 ('S16-offset-aggregate-log','actualCorrelatedMatrixLogDet_offset_of_sum_log',['L-mode-log-L1'],True)]
for ident,decl,ds,target in nodes:
    a.write(a.PROJECT/'dag/nodes'/f'{ident}.json',dict(id=ident,kind='target' if target else 'lemma',target=target,
      module=mod,declaration='JinWishart.'+decl,stmt_deps=[],proof_deps=ds,
      proof=[dict(text='Explicit aggregate-log L1 and nonnegative integrable spectrum; conditional only.',uses=ds)],
      verification=dict(status='checked_pending_review')))
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-hour-spectrum-final'):
    leaf=a.gated(src,mod,'positive-spectrum-20261021-locked')
    assert leaf['success']
    types=a.gated(checker,checker.stem,'spectrum-types-20261021-locked',checker.parent)
    assert types['success']
    a.validate_locks(a.rel(lp))
a.write(run/'check-spectrum.json',dict(success=True,source_sha256=a.sha(src),target_lock_sha256=a.sha(lp),
    leaf=leaf,types=types,lock_validated_before_and_after=True))
p=a.LEAN/'JinWishartFormalization.lean'
body=p.read_bytes()
new=('import '+mod+'\n').encode()+body
p.write_bytes(new)
print('LOCKED_SPECTRUM_PASS; facade61 pending')
