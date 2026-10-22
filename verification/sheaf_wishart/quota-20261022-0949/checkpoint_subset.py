"""Archive and commit only this run's own accepted milestone."""
from pathlib import Path
import sys,subprocess
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
assert a.read(R/'verification/central_mixed_moments/audit.json')['total_declarations']==618
assert a.read(R/'verification/sheaf_wishart/facade-65.receipt.json')['gated_helper_exit_code']==0
assert not (run/'subset-summary.json').exists(), 'One-off checkpoint'
frozen={
 'theory/wishart_paper/main.tex':'0f48aa2843ae53ab27b439af49adb90718ba72ffbcd9ea0c790c6a359bc41049',
 'output/pdf/wishart_formalization.pdf':'5a637adfd9945fcc8704c40eeec88bac55b1b61aea232b7cb1374c8ecd558203',
 'output/publication/wishart_arxiv_upload.zip':'b05b0146640505202369d07da8a5b00b6479102c41451401f1c382e4abc30d9c',
 'output/publication/wishart_formalization_code.zip':'2f1dfc2b60ac91c96ab15d24bc69a1cfe96da8efd366d10d191232726083c83b'}
for p,h in frozen.items():assert a.sha(R/p)==h,p
text='2026-10-22 额度续跑首个里程碑：618绑定项（616 theorem/instance+2构造），auditPASS/facade65真实exit0。新增8个有限代数声明、3模块，精确子集矩形Cauchy-Binet及Gram全子式模平方系数卡已完成；不是8个新概率定律。220个固定种子精确控制、8个独立字面目标类型、最终源码Qoder P4及误报裁决已绑定。用户本次授权继续至普通额度实际不可用，当前ordinary=true/主16%/周61%；旧固定小时不重开，单协调器/技术租约，heartbeat已恢复ACTIVE。一般d锐常数简式、非中心G2/原T1候选式/T3刊版及全文映射仍OPEN。[需人工审查]继承测度/Fubini/极限/方差/模型。冻结四产物哈希未改，fullLake及Linux独立内核NOT_RUN。详见WISHART_EXACT_SUBSET_CAUCHY_BINET.md。'
for name in ['WISHART_STATUS.md','THEOREM_COVERAGE_AUDIT.md','JIN_WISHART_THEOREM_TRACKER.md','WISHART_LOGDET_RESEARCH_CLAIMS.md']:
 p=R/'notes'/name;p.write_text(text+'\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8')
state=a.read(a.SESSION/'state.json');state.update(checkpoint=text,updated_utc=a.now(),automation_status='ACTIVE',current_quota_note='ordinaryUsageAllowed=true primary16% weekly61% at2026-10-22 02:03UTC');a.write(a.SESSION/'state.json',state)
attrs=R/'.gitattributes';body=attrs.read_text(encoding='utf-8')
for p in ['theory/jin_wishart_formalization/JinWishartFormalization/'+c['module']+'.lean' for c in a.read(run/'cards.json')]+['experiments/subset_cauchy_binet_control.py','notes/WISHART_EXACT_SUBSET_CAUCHY_BINET.md']:
 rule='/'+p+' -text whitespace=cr-at-eol'
 if rule not in body:body+='\n'+rule+'\n'
attrs.write_text(body,encoding='utf-8')
a.write(run/'subset-summary.json',dict(completed_utc=a.now(),items=618,theorems_instances=616,constructions=2,new_printed_declarations=8,new_source_modules=3,controls=220,facade='verification/sheaf_wishart/facade-65.receipt.json',audit='verification/central_mixed_moments/audit.json',frozen_hashes=frozen,full_lake_build='NOT_RUN',linux_independent_kernel='NOT_RUN',human_review='REQUIRED',ordinary_usage_allowed=True,primary_used_percent=16,weekly_used_percent=61))
git=r'D:\MinGit\cmd\git.exe'
out=subprocess.check_output([git,'status','--porcelain','-uall'],cwd=R,text=True,encoding='utf-8')
paths=[line[3:] for line in out.splitlines() if not line[3:].startswith(('.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'))]
subprocess.run([git,'add','--']+paths,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m','Prove exact subset Cauchy-Binet and all-minor Gram coefficients'],cwd=R,check=True)
for c in a.read(run/'cards.json'):
 p='theory/jin_wishart_formalization/JinWishartFormalization/'+c['module']+'.lean'
 import hashlib
 assert hashlib.sha256(subprocess.check_output([git,'show','HEAD:'+p],cwd=R)).hexdigest()==a.sha(R/p)
print('COMMITTED_SOURCE_BYTES_MATCH')
