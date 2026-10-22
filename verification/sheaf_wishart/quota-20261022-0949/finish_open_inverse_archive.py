"""Commit the OPEN research milestone; no new proof acceptance or build."""
from pathlib import Path
import json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
out=run/'open-inverse-review-archive.json';assert not out.exists()
for rel,h in read(run/'open-inverse-card-summary.json')['files'].items():assert sha(R/rel)==h,rel
rc=read(run/'p4-open-inverse-block-route.receipt.json')
assert rc['exit_code']==0 and rc['prompt_sha256']==sha(run/'p4-open-inverse-block-route.md')
files={str(p.relative_to(R)).replace('\\','/'):sha(p) for p in run.glob('p4-open-inverse-block-route.*')}
resolution=R/'notes/WISHART_SINGULAR_INVERSE_ROUTE_REVIEW.md';files[str(resolution.relative_to(R)).replace('\\','/')]=sha(resolution)
faults=['Archive attempt1: KeyError modules; early summaries use new_source_modules. No Lean acceptance affected.',
'Archive attempt2: failed duplicate control-count assertion; 35-control experiment reused by two milestones. Unique seven experiments total403. No Lean acceptance affected.',
'Premature route-review launch after failed archive found no prompt and made NO model call. Later single real route-P4 exit0 preserved.']
out.write_text(json.dumps(dict(archived_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='OPEN route only; no general threshold proof',accepted_items=665,files=files,retained_archive_faults=faults,review='Qoder route P4 only; not final Lean-source acceptance',human_review='REQUIRED'),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
attrs=R/'.gitattributes';body=attrs.read_text(encoding='utf-8')
for rel in files:
 rule='/'+rel+' -text whitespace=cr-at-eol'
 if rule not in body:body+='\n'+rule+'\n'
attrs.write_text(body,encoding='utf-8')
git=r'D:\MinGit\cmd\git.exe'
own=['.gitattributes','notes/WISHART_STATUS.md','notes/WISHART_LIBRARY_CONTRIBUTION_MAP.md','notes/WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md','notes/WISHART_QUOTA_20261022_REVIEW_CN.md','notes/WISHART_SINGULAR_INVERSE_ROUTE_REVIEW.md','sheaf/wishart/README.md','experiments/singular_positive_minimum_preflight.py','experiments/singular_block_shear_control.py',str(run.relative_to(R))]
subprocess.run([git,'add','--']+own,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m','Archive open singular inverse-moment route and exact block controls'],cwd=R,check=True)
print('OPEN_CARD_COMMITTED; accepted Lean count unchanged665')
