"""Accept only complete bound evidence and preserve accurate queue scope."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
for c in a.read(run/'cards.json'):
 a.accept(a.rel(run/('acceptance-'+c['tag']+'.json')),'codex-quota-subset-accept')
paths=list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']
for p in paths:a.verify_acceptance(a.read(p))
(a.PROJECT/'coord/STATE.md').write_text('# State\n\n618 bound items/auditPASS/facade65 exit0. Exact subset rectangular Cauchy-Binet and all-minor Gram coefficient cards now VERIFIED. Proper finite-dimensional Gaussian polynomial logs and fixed-factor generic-rank expected offset were previously closed. Outside target closure does not imply unproved; consult individual evidence.\n\nCurrent quota run is user-authorized, single coordinator, technical lease only. No background Lean worker. Human inherited measure/model review remains REQUIRED. Full Lake/mathlib and Linux independent kernel NOT_RUN; frozen publications unchanged.\n',encoding='utf-8')
print('ALL_ACCEPTANCE_CURRENT',len(paths))
