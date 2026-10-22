from pathlib import Path
import sys,subprocess,hashlib
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
assert not (run/'curvature-summary.json').exists()
assert a.read(R/'verification/central_mixed_moments/audit.json')['total_declarations']==631
assert a.read(R/'verification/sheaf_wishart/facade-66.receipt.json')['gated_helper_exit_code']==0
text='2026-10-22 额度续跑第二里程碑：631绑定项（629 theorem/instance+2构造），auditPASS/facade66真实exit0。当前续跑累计新增21打印声明/5模块；最新13声明证明任意固定矩形/奇异/零B,M的期望full-logdet二阶导数=-SUM E[(lambda/(1+rho lambda))²]，正尺度凹且严格凹当且仅当通用秩min(m,rank stacked[B;M])>0，秩0时非负尺度期望恒0。通用积分引理仅需非负函数一阶矩L1，允许任意测度；未增加逆矩/平方矩前提。34项20万样本闭式对照、13独立字面类型、最终源码Qoder P4及误报裁决已绑定；不是13个新概率定律。ordinary=true/主27%/周63%，继续单协调器至实际不可用；旧固定小时仍关闭。[需人工审查]求导积分/AE/方差/模型，冻结投稿产物未改/fullLake和Linux独立内核NOT_RUN。详见WISHART_EXPECTED_LOGDET_CURVATURE.md。'
for name in ['WISHART_STATUS.md','THEOREM_COVERAGE_AUDIT.md','JIN_WISHART_THEOREM_TRACKER.md','WISHART_LOGDET_RESEARCH_CLAIMS.md']:
 p=R/'notes'/name;p.write_text(text+'\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8')
state=a.read(a.SESSION/'state.json');state.update(checkpoint=text,updated_utc=a.now(),current_quota_note='ordinaryUsageAllowed=true primary27% weekly63% at2026-10-22 02:16UTC');a.write(a.SESSION/'state.json',state)
attrs=R/'.gitattributes';body=attrs.read_text(encoding='utf-8')
for p in ['theory/jin_wishart_formalization/JinWishartFormalization/'+c['module']+'.lean' for c in a.read(run/'cards-curvature.json')]+['experiments/logdet_curvature_control.py','notes/WISHART_EXPECTED_LOGDET_CURVATURE.md']:
 rule='/'+p+' -text whitespace=cr-at-eol'
 if rule not in body:body+='\n'+rule+'\n'
attrs.write_text(body,encoding='utf-8')
frozen=a.read(run/'subset-summary.json')['frozen_hashes']
for p,h in frozen.items():assert a.sha(R/p)==h
a.write(run/'curvature-summary.json',dict(completed_utc=a.now(),items=631,theorems_instances=629,constructions=2,new_printed_declarations=13,new_source_modules=2,controls=34,samples=200000,facade='verification/sheaf_wishart/facade-66.receipt.json',audit='verification/central_mixed_moments/audit.json',frozen_hashes=frozen,human_review='REQUIRED',full_lake_build='NOT_RUN',linux_independent_kernel='NOT_RUN',ordinary_usage_allowed=True,primary_used_percent=27,weekly_used_percent=63))
git=r'D:\MinGit\cmd\git.exe'
out=subprocess.check_output([git,'status','--porcelain','-uall'],cwd=R,text=True,encoding='utf-8')
paths=[line[3:] for line in out.splitlines() if not line[3:].startswith(('.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'))]
subprocess.run([git,'add','--']+paths,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m','Verify full logdet curvature and exact generic-rank strict concavity'],cwd=R,check=True)
for c in a.read(run/'cards-curvature.json'):
 p='theory/jin_wishart_formalization/JinWishartFormalization/'+c['module']+'.lean'
 assert hashlib.sha256(subprocess.check_output([git,'show','HEAD:'+p],cwd=R)).hexdigest()==a.sha(R/p)
print('COMMITTED_SOURCE_BYTES_MATCH')
