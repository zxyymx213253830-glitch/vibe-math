"""Collect exact checkpoint evidence; --close only after the user hour expires."""
from datetime import datetime,timezone
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
session=root/'.tools/central-mixed-moments-20261019'
now=datetime.now(timezone.utc)
deadline=datetime.fromisoformat('2026-10-20T08:05:09+00:00')
close='--close' in sys.argv
assert not close or now>=deadline,'The authorized hour has not ended.'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=json.loads((base/'spec.json').read_text(encoding='utf-8'))
audit=json.loads((base/'audit.json').read_text(encoding='utf-8'))
assert audit['total_declarations']==515 and audit['status'].startswith('PASS')
names=['CorrelatedRankUpperBound','CorrelatedRankWitness','MatrixRankCompression',
 'CorrelatedGaussianGenericRank','CorrelatedLogDetGenericRank','CorrelatedMinimumZeroAtom',
 'CorrelatedNoiselessSpectralFloor','CorrelatedNoiselessInverseMoments']
targets=[x for x in spec['targets'] if x['module'].split('.')[-1] in names]
assert len(targets)==8 and sum(x['count'] for x in targets)==24
for x in targets:
    b=(base/Path(x['log']).name).read_text(encoding='utf-8')
    assert 'error' not in b and 'sorryAx' not in b
    rec=audit['modules'][x['module']]
    rel=Path(x['module'].replace('.','/'))
    assert sha(root/'theory/jin_wishart_formalization'/rel.with_suffix('.lean'))==rec['source_sha256']
    assert sha(root/spec['library']/rel.with_suffix('.olean'))==rec['olean_sha256']
    assert sha(root/x['log'])==rec['log_sha256']
frozen={
 'theory/wishart_paper/main.tex':'0f48aa2843ae53ab27b439af49adb90718ba72ffbcd9ea0c790c6a359bc41049',
 'output/pdf/wishart_formalization.pdf':'5a637adfd9945fcc8704c40eeec88bac55b1b61aea232b7cb1374c8ecd558203',
 'output/publication/wishart_arxiv_upload.zip':'b05b0146640505202369d07da8a5b00b6479102c41451401f1c382e4abc30d9c',
 'output/publication/wishart_formalization_code.zip':'2f1dfc2b60ac91c96ab15d24bc69a1cfe96da8efd366d10d191232726083c83b'}
for p,h in frozen.items():
    assert sha(root/p)==h,p
facade=json.loads((base/'facade-48.receipt.json').read_text(encoding='utf-8'))
assert facade['gated_helper_exit_code']==0
assert facade['log_sha256']==sha(base/'facade-48.txt')
main=root/'theory/jin_wishart_formalization/JinWishartFormalization.lean'
main_artifact=root/spec['library']/'JinWishartFormalization.olean'
assert main_artifact.stat().st_mtime>=main.stat().st_mtime
tags=['rank-algebra-0705','rank-compression-0705','gaussian-rank-0705',
 'logdet-generic-rank-0705','minimum-zero-atom-0705','noiseless-floor-inverse-0705']
receipts=[base/'p1-correlated-rank-upper-0705.receipt.json']+[base/('p4-'+t+'.receipt.json') for t in tags]
reviews=[]
for p in receipts:
    r=json.loads(p.read_text(encoding='utf-8'))
    assert r['exit_code']==0
    reviews.append(dict(receipt=str(p.relative_to(root)).replace('\\','/'),sha256=sha(p),
      requested_model=r['requested_model'],reported_model_usage=r.get('reported_model_usage'),
      seconds=r['seconds'],exit_code=r['exit_code'],independent_compilation=False,human_review=False))
locks={p.name:p.exists() for p in [session/'compute.lock',session/'CODEX_REVIEW']}
if close:
    assert not any(locks.values()),locks
git=r'D:\MinGit\cmd\git.exe'
head=subprocess.check_output([git,'rev-parse','HEAD'],cwd=root,text=True).strip()
state=json.loads((session/'state.json').read_text(encoding='utf-8'))
state.update(stage='CLOSED_USER_ONE_HOUR' if close else 'ACTIVE_USER_ONE_HOUR_REVIEW_PACKETS',
 checkpoint='515 bounditems (513 theorem/instance+2 earlier constructions), auditPASS/facade48 actualexit0. '
 'Actual arbitrary fixedB/M genericrank=min(m,rank stacked[B;M]), explicit full-logdet prelog, '
 'columnminimum zeroatom; noiseless-surjective fixedmean gives uniform ROW floor and all real inverse orders. '
 'General noiseless row offset remainsOPEN/preflight only.',
 updated_utc=now.isoformat(),automation_status='PAUSED')
if close:
    state.update(ended_utc=now.isoformat(),paused_utc=now.isoformat(),
      pause_reason='Fixed one-hour user deadline reached; not quota exhaustion. No new research without renewed authorization.')
(session/'state.json').write_text(json.dumps(state,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
summary=dict(stage=state['stage'],started_utc='2026-10-20T07:05:09+00:00',deadline_utc=deadline.isoformat(),
 collected_utc=now.isoformat(),initial_bound_items=491,final_bound_items=515,new_declarations=24,
 new_modules=8,proof_author='Codex',planning_and_review='Qoder only;1P1+6scoped final-source P4',
 new_targets=targets,new_exact_source_bindings={x['module']:audit['modules'][x['module']] for x in targets},
 qoder_calls=reviews,facade48=facade,
 facade47=dict(reported_exec_exit_code=1,log_bytes=(base/'facade-47.txt').stat().st_size,
  log_sha256=sha(base/'facade-47.txt'),cause='UNKNOWN; retained, not counted as PASS; unchanged-source retry48 passed'),
 full_build='NOT_RUN',human_review='REQUIRED',frozen_publication_hashes_unchanged=frozen,
 audit_sha256=sha(base/'audit.json'),spec_sha256=sha(base/'spec.json'),
 source_main_sha256=sha(root/'theory/jin_wishart_formalization/JinWishartFormalization.lean'),
 current_head=head,research_milestone_commits=['a48cdb6','6bac414'],locks=locks,
 next_card='notes/WISHART_NEXT_NOISELESS_OFFSET_CARD.md',
 open_scope='General row offset/error, general singular inverse threshold, noncentral explicit minimum CDF/PDF/G2, '
 'original general T1 identity, generald simplified coefficient, T3 journal normalization/full paper mapping remainOPEN.',
 no_remote_push=True,no_purchases_resets_or_account_switches=True,
 quota_stop='Fixed user hour governs this run; actual ordinary usage at close is recorded separately in state.',
 protected_unknown=['.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'])
out=base/'one-hour-20261020-0705-summary.json'
out.write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(stage=summary['stage'],new_declarations=24,new_modules=8,final_bound_items=515,
                     facade48_exit_code=facade['gated_helper_exit_code'],head=head)))
