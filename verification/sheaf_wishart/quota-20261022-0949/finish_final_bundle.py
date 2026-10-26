"""Accept, archive and commit own verified evidence; never claim human/build review."""
from pathlib import Path
import sys,subprocess,hashlib
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
c=a.read(run/sys.argv[1]);summary=run/(c['name']+'-summary.json');assert not summary.exists(), 'One-off completed milestone'
cards=a.read(run/('cards-'+c['name']+'.json'))
assert a.read(R/'verification/central_mixed_moments/audit.json')['total_declarations']==c['total']
assert a.read(R/'verification/sheaf_wishart'/(c['facade']+'.receipt.json'))['gated_helper_exit_code']==0
for card in cards:a.accept(a.rel(run/('acceptance-'+card['tag']+'.json')),'codex-quota-'+c['name']+'-accept')
paths=list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']
for p in paths:a.verify_acceptance(a.read(p))
frozen=a.read(run/'subset-summary.json')['frozen_hashes']
for p,h in frozen.items():assert a.sha(R/p)==h
for name in ['WISHART_STATUS.md','THEOREM_COVERAGE_AUDIT.md','JIN_WISHART_THEOREM_TRACKER.md','WISHART_LOGDET_RESEARCH_CLAIMS.md']:
 p=R/'notes'/name;p.write_text(c['scope']+'\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8')
state=a.read(a.SESSION/'state.json');state.update(checkpoint=c['scope'],updated_utc=a.now());a.write(a.SESSION/'state.json',state)
(a.PROJECT/'coord/STATE.md').write_text('# State\n\n'+c['scope']+'\n\nOutside target closure does not mean unproved; consult exact node evidence. One current coordinator, technical lease only; heartbeat ACTIVE; no parallel/background Lean worker. Human review REQUIRED; fullLake and Linux independent kernel NOT_RUN; frozen publications unchanged.\n',encoding='utf-8')
attrs=R/'.gitattributes';body=attrs.read_text(encoding='utf-8')
sources=['theory/jin_wishart_formalization/JinWishartFormalization/'+card['module']+'.lean' for card in cards]
for p in sources+[c['control_script'],c['resolution']]+[v['script'] for v in c.get('additional_controls',[])]:
 rule='/'+p+' -text whitespace=cr-at-eol'
 if rule not in body:body+='\n'+rule+'\n'
attrs.write_text(body,encoding='utf-8')
a.write(summary,dict(completed_utc=a.now(),items=c['total'],new_printed_declarations=c['new_count'],modules=len(cards),facade=c['facade'],controls=a.read(R/c['control_result'])['checks'],additional_controls=[dict(**v,checks=a.read(R/v['result'])['checks']) for v in c.get('additional_controls',[])],frozen_hashes=frozen,human_review='REQUIRED',full_lake_build='NOT_RUN',linux_independent_kernel='NOT_RUN',acceptance_records_current=len(paths)))
git=r'D:\MinGit\cmd\git.exe';out=subprocess.check_output([git,'status','--porcelain','-uall','-z'],cwd=R).decode('utf-8')
pending=set(c.get('pending_paths',[]))
entries=[line for line in out.split('\0') if line]
assert not any('R' in line[:2] or 'C' in line[:2] for line in entries), 'Review renames/copies explicitly before staging'
own=[line[3:] for line in entries if line[3:] not in pending and not line[3:].startswith(('.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'))]
subprocess.run([git,'add','--']+own,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m',c['commit']],cwd=R,check=True)
for p in sources:assert hashlib.sha256(subprocess.check_output([git,'show','HEAD:'+p],cwd=R)).hexdigest()==a.sha(R/p)
print('COMMITTED_SOURCE_BYTES_MATCH; ALL_ACCEPTANCE_CURRENT',len(paths))
