from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
for c in a.read(run/'cards-curvature.json'):
 a.accept(a.rel(run/('acceptance-'+c['tag']+'.json')),'codex-quota-curvature-accept')
paths=list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']
for p in paths:a.verify_acceptance(a.read(p))
(a.PROJECT/'coord/STATE.md').write_text('# State\n\n631 bound items/auditPASS/facade66 exit0. Actual fixed arbitrary-factor full-logdet second derivative is negative expected sum of squared resolvents. Concavity holds onpositive scale; strictness IFF genericrank>0, withrank0 zero expectation. Exact subset Cauchy-Binet/all-minor coefficient and finite proper Gaussian polynomial logs/expected rank offset previously closed. Outside closure does not mean unproved.\n\nUser-authorized quota run remains active, one coordinator and technical lease. No background Lean worker. Human inherited measure/model review REQUIRED; fullLake and Linux independent kernel NOT_RUN; frozenpublications unchanged.\n',encoding='utf-8')
print('ALL_ACCEPTANCE_CURRENT',len(paths))
