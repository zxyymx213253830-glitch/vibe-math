from pathlib import Path
from datetime import datetime,timezone
import sys,uuid,os,json
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
run=Path(__file__).parent
for p in [a.SESSION/'compute.lock',a.SESSION/'CODEX_REVIEW',a.SESSION/'runner.lock',a.SESSION/'STOP',a.PROJECT/'coord/operation.lock']:
 assert not p.exists(),str(p)
assert not list((a.PROJECT/'coord/claims').glob('*.lock'))
state=a.read(a.SESSION/'state.json');assert not state['stage'].startswith('ACTIVE')
claim=dict(token=uuid.uuid4().hex,group='codex-one-hour-20261022-0024',started_utc='2026-10-21T16:24:50+00:00',hard_deadline_utc='2026-10-21T17:24:50+00:00',authorization='User explicitly renewed one hour; no automatic extension.',single_coordinator=True)
p=a.PROJECT/'coord/claims/cauchy-binet-hour-20261022.lock'
with p.open('x',encoding='utf-8') as f:json.dump(claim,f)
a.write(run/'claim.json',claim)
state.update(stage='ACTIVE_WISHART_ONE_HOUR_20261022',resumed_utc=claim['started_utc'],deadline_utc=claim['hard_deadline_utc'],updated_utc=a.now(),current_coordinator_token=claim['token'],authorization=claim['authorization'],automation_status='PAUSED')
for k in ['ended_utc','pause_reason']:state.pop(k,None)
a.write(a.SESSION/'state.json',state)
old=R/'verification/sheaf_wishart/hour-20261021-1201/check_entry.py'
body=old.read_text(encoding='utf-8').replace('gaussian-log-hour-20261021.lock','cauchy-binet-hour-20261022.lock').replace('codex-hour-20261021-1201','codex-hour-20261022-0024')
(run/'check_entry.py').write_text(body,encoding='utf-8')
(R/'notes/WISHART_ONE_HOUR_20261022_0024.md').write_text('# Fixed-hour continuation2026-10-22\n\nUser-authorized00:24:50--01:24:50Asia/Shanghai (2026-10-21 16:24:50--17:24:50UTC). Hard deadline; no automatic extension. Baseline585/auditPASS/facade61.\n\nPrior426 exact complex-rational minor/coefficient controls bind the current script. Target Cauchy-Binet and Gram spectral coefficients from the explicit SHEAF queue. Qoder separate-family P1/P4; proofs Codex; one serial Windows kernel gate; no Linux kernel claim. Frozen publication untouched. [需人工审查] Inherited measure/model interpretation.\n',encoding='utf-8')
print(claim)
