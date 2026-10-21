"""Archive only after the explicit user deadline; no Lean/model calls or new math."""
from pathlib import Path
from datetime import datetime,timezone
import sys,subprocess,hashlib,json
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
claimpath=a.PROJECT/'coord/claims/cauchy-binet-hour-20261022.lock'
claim=a.read(claimpath);now=datetime.now(timezone.utc)
assert now>=datetime.fromisoformat(claim['hard_deadline_utc']),'Authorized hour still active'
state=a.read(a.SESSION/'state.json');assert state.get('current_coordinator_token')==claim['token']
locks=[p for p in [a.SESSION/'compute.lock',a.SESSION/'CODEX_REVIEW',a.SESSION/'runner.lock',a.PROJECT/'coord/operation.lock'] if p.exists()]
assert not locks,'Live locks retained; never delete another process lock: '+str(locks)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={
 'theory/wishart_paper/main.tex':'0f48aa2843ae53ab27b439af49adb90718ba72ffbcd9ea0c790c6a359bc41049',
 'output/pdf/wishart_formalization.pdf':'5a637adfd9945fcc8704c40eeec88bac55b1b61aea232b7cb1374c8ecd558203',
 'output/publication/wishart_arxiv_upload.zip':'b05b0146640505202369d07da8a5b00b6479102c41451401f1c382e4abc30d9c',
 'output/publication/wishart_formalization_code.zip':'2f1dfc2b60ac91c96ab15d24bc69a1cfe96da8efd366d10d191232726083c83b'}
frozen={p:dict(sha256=sha(R/p),unchanged=sha(R/p)==h) for p,h in expected.items()}
assert all(v['unchanged'] for v in frozen.values()),'Frozen artifact mismatch; preserve evidence'
audit=a.read(R/'verification/central_mixed_moments/audit.json');assert audit['total_declarations']==610
calls=[]
for p in sorted(run.glob('*.receipt.json')):
 d=a.read(p)
 if 'requested_model' in d:calls.append(dict(receipt=a.rel(p),exit_code=d['exit_code'],seconds=d['seconds'],requested_model=d['requested_model']))
summary=dict(started_utc=claim['started_utc'],hard_deadline_utc=claim['hard_deadline_utc'],archived_utc=now.isoformat(),
 baseline_items=585,final_items=610,new_printed_declarations=25,new_modules=7,proof_author='Codex',
 source_commits=['e53fe9a','4aedf84','8c9ced9'],documentation_commit='a7db472',archive_integrity_commit='b27edce',preparation_guard_commit='19c57d4',facade=a.read(R/'verification/sheaf_wishart/facade-64.receipt.json'),
 audit_sha256=sha(R/'verification/central_mixed_moments/audit.json'),literal_target_types=25,current_acceptance_records=18,
 model_calls=calls,model_review_is_human_review=False,model_independent_compilation=False,
 linux_receipt=a.read(run/'linux-source-index.receipt.json'),linux_lean_compile='NOT_RUN',full_build='NOT_RUN',
 control_checks=dict(averaged_exact=52,singular_known_reference=27,derivative_known_reference=8,reused_exact=426),
 claims='Fixed arbitrary B/M aggregate positive-spectrum log L1 and expected generic-rank offset; positive-scale expected full-logdet derivative. No evaluated offset constant/rate/parameter-uniformity/coding theorem.',
 deferred=['Full subset-grouped Cauchy-Binet','Original paper T1/G2/T3/full coverage obligations; human review'],
 frozen=frozen,automation_status='PAUSED',locks_present=[],human_review='REQUIRED measure/Fubini/derivative/variance/model',
 committed_source_byte_audit=a.read(run/'git-source-byte-audit.json'),preparation_guard_regression=a.read(run/'preparation-guard-regression.json'),report='notes/WISHART_HOUR_20261022_REVIEW_CN.md')
a.write(run/'hour-summary.json',summary)
with (R/'notes/WISHART_ONE_HOUR_20261022_0024.md').open('a',encoding='utf-8') as f:
 f.write('\n## Fixed-hour closeout\n\nAuthorized00:24:50--01:24:50Asia/Shanghai (16:24:50--17:24:50UTC), archive observed '+now.isoformat()+'. No automatic extension. Final610 bound items,25new printed declarations/7modules; facade64 actualexit0 and25literal type comparisons.18current acceptance records were revalidated before deadline.\n\nEight Qoder calls all delivered exit0:1route plus4final bound reviews and3superseded/context-clarification responses. False warnings and their dispositions are preserved, not called blanket approvals. All proof bodies Codex; model reviews are not human review or independent compilation.\n\nLinux source-only snapshot439hash-verified files/362modules/71DAGnodes; Linux Lean and fullLake NOT_RUN.52new exact controls plus27and8known-reference controls (200000samples each numerical experiment) and426reused exact controls are not proofs.\n\nFrozen source/PDF/upload/code archives match prior hashes. [需人工审查] Gaussian variance/model correspondence, AE/Fubini/integrability/DCT and integral differentiation. General singular inverse-moment thresholds, evaluated offset constants/rates, original-paper unresolved mappings and full subset Cauchy-Binet are not claimed. Own claim released; no shared/review lock left, no other process stopped, heartbeatPAUSED. No push.\n')
state.update(stage='CLOSED_WISHART_ONE_HOUR_20261022',updated_utc=now.isoformat(),ended_utc=now.isoformat(),
 automation_status='PAUSED',pause_reason='Explicit fixed one hour ended; no automatic extension.',
 checkpoint='610/auditPASS/facade64exit0;25new declarations/7modules. Fixed arbitraryfactor positive-log L1/expected rank offset and positive-scale expected logdet derivative closed. Linux439files/71nodes source-only. Humanreview REQUIRED.')
state.pop('current_coordinator_token',None);a.write(a.SESSION/'state.json',state)
assert a.read(claimpath)['token']==claim['token'];claimpath.unlink()
(a.PROJECT/'coord/STATE.md').write_text('# State\n\nFIXED_HOUR_CLOSED2026-10-22 01:24:50Asia/Shanghai.610accepted items; current target queue complete, outside-closure deferred cards retained.\n\nNo active coordinator/background service; heartbeatPAUSED. Human reviewREQUIRED.\n',encoding='utf-8')
a.ledger('Fixed hour CLOSED610/auditPASS/facade64;25new declarations, own claim released, heartbeatPAUSED. No further mathematics/check/model work after17:24:50UTC.')
git=r'D:\MinGit\cmd\git.exe'
paths=['sheaf/wishart/README.md','sheaf/wishart/coord/STATE.md','sheaf/wishart/coord/ledger.md',
 'notes/WISHART_ONE_HOUR_20261022_0024.md',a.rel(run/'close_hour.py'),a.rel(run/'hour-summary.json')]
subprocess.run([git,'add','--']+paths,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m','Archive fixed one-hour singular-offset research milestone'],cwd=R,check=True)
print('HOUR_CLOSED_610_AUTOMATION_PAUSED')
