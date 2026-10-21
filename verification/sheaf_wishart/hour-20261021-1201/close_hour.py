"""Archive this bounded hour after its deadline; no mathematics/compiler/model calls."""
from pathlib import Path
from datetime import datetime,timezone
import sys,hashlib,json,subprocess
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
claimpath=a.PROJECT/'coord/claims/gaussian-log-hour-20261021.lock'
claim=a.read(claimpath);deadline=datetime.fromisoformat(claim['hard_deadline_utc'])
now=datetime.now(timezone.utc)
assert now>=deadline,'One hour still active; early closeout refused'
state=a.read(a.SESSION/'state.json')
assert state.get('current_coordinator_token')==claim['token']
locks=[p for p in [a.SESSION/'compute.lock',a.SESSION/'CODEX_REVIEW',a.SESSION/'runner.lock',a.PROJECT/'coord/operation.lock'] if p.exists()]
assert not locks, 'Retain claims and inspect live locks; never delete or stop another process: '+str(locks)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen_expected={
 'theory/wishart_paper/main.tex':'0f48aa2843ae53ab27b439af49adb90718ba72ffbcd9ea0c790c6a359bc41049',
 'output/pdf/wishart_formalization.pdf':'5a637adfd9945fcc8704c40eeec88bac55b1b61aea232b7cb1374c8ecd558203',
 'output/publication/wishart_arxiv_upload.zip':'b05b0146640505202369d07da8a5b00b6479102c41451401f1c382e4abc30d9c',
 'output/publication/wishart_formalization_code.zip':'2f1dfc2b60ac91c96ab15d24bc69a1cfe96da8efd366d10d191232726083c83b'}
frozen={name:dict(sha256=sha(R/name),unchanged=sha(R/name)==expected) for name,expected in frozen_expected.items()}
assert all(x['unchanged'] for x in frozen.values()),'Unexpected frozen artifact change; report before any further mutation'
calls=[]
for p in sorted(run.glob('*.receipt.json')):
 d=a.read(p)
 if 'requested_model' in d:calls.append(dict(receipt=a.rel(p),exit_code=d['exit_code'],seconds=d['seconds'],requested_model=d['requested_model']))
audit=a.read(R/'verification/central_mixed_moments/audit.json')
summary=dict(started_utc=claim['started_utc'],hard_deadline_utc=claim['hard_deadline_utc'],archived_utc=now.isoformat(),
 baseline_items=571,final_items=audit['total_declarations'],new_printed_declarations=14,proof_author='Codex',
 review_partner='Qoder Qwen3.8-Max',review_calls=calls,model_review_is_human_review=False,
 facade=a.read(R/'verification/sheaf_wishart/facade-61.receipt.json'),audit_sha256=sha(R/'verification/central_mixed_moments/audit.json'),
 source_commit='8594ffd',open_nodes=['L-rectangular-cauchy-binet','L-gram-minor-coefficient','L-gram-rank-spectral-coefficient','S17-general-singular-offset'],
 linux='409 exact source files,48 DAG nodes; source/index only; Linux Lean NOT_RUN',full_build='NOT_RUN',
 frozen=frozen,automation_status='PAUSED',locks_present=[],human_review='REQUIRED measure/Fubini/variance/model',
 next_card='notes/WISHART_NEXT_PSEUDODET_CARD.md')
a.write(run/'hour-summary.json',summary)
with (R/'notes/WISHART_ONE_HOUR_20261021_1201.md').open('a',encoding='utf-8') as f:
 f.write('\n## Fixed-hour closeout\n\nThe authorized hour ended13:01:41UTC (21:01:41Asia/Shanghai); archive observed '+now.isoformat()+'. No automatic extension. Final585 accepted items (583theorem/instance+2constructions),14 new printed declarations in3modules. All11 acceptance records revalidated before deadline. Mainfacade61 actualexit0.\n\nLinux native source/index snapshot:409 hash-verified inputs,355modules,48DAGnodes,4explicit OPEN_NOT_FORMALIZED obligations. Linux Lean remains NOT_RUN; it is not an independently compiled library. Both earlier405 and older388 input snapshots are preserved.\n\nThis hour Qoder7 bounded calls:6 real exit0 and1 timeout; route reviews are not proof approvals. The final next-route inequality-direction warning is false and explicitly resolved. The next card preserves all actual algebraic gaps and raw/physical polynomial-ring distinction.426 exact next-bridge controls are preflight only, outside585; earlier results are superseded by finalcontrol3.\n\nFrozen source/PDF/upload/code archives match recorded hashes. FullLake/mathlib build NOT_RUN. [需人工审查] AE/Fubini/integrability, physical variance and model correspondence remain human obligations. No active shared/compiler/review lock found; only this hour own claim released; heartbeat remains PAUSED. No push or credential migration.\n')
state.update(stage='CLOSED_WISHART_ONE_HOUR_20261021',updated_utc=now.isoformat(),ended_utc=now.isoformat(),
 automation_status='PAUSED',pause_reason='User-authorized fixed one hour ended; no automatic extension.',
 checkpoint='585 accepted items/auditPASS/facade61exit0; properCN1 and physical compressed log L1; singular pseudoDet bridge four OPEN nodes; Linux409files/48nodes source-only.')
state.pop('current_coordinator_token',None);a.write(a.SESSION/'state.json',state)
assert a.read(claimpath)['token']==claim['token'];claimpath.unlink()
(a.PROJECT/'coord/STATE.md').write_text('# State\n\nFIXED_HOUR_CLOSED2026-10-21 13:01:41UTC.585accepted bound items;4next bridge nodes OPEN_NOT_FORMALIZED.\n\nNo active coordinator/background service; heartbeat PAUSED. Human measure/model review REQUIRED.\n',encoding='utf-8')
a.ledger('Fixed one hour CLOSED;585accepted/4unformalized next nodes; own claim released, heartbeatPAUSED. No new math/check/model work after13:01:41UTC.')
git=r'D:\MinGit\cmd\git.exe'
out=subprocess.check_output([git,'status','--porcelain','-uall'],cwd=R,text=True,encoding='utf-8')
paths=[line[3:] for line in out.splitlines() if not line[3:].startswith(('.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'))]
subprocess.run([git,'add','--']+paths,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m','Archive bounded SHEAF hour and open singular-offset bridge queue'],cwd=R,check=True)
print('HOUR_CLOSED_585_AUTOMATION_PAUSED')
