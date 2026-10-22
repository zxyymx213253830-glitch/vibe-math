"""Archive exploratory controls and a precise OPEN card without changing Lean acceptance."""
from pathlib import Path
import json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
manifest=run/'open-inverse-card-summary.json'
assert not manifest.exists(),'One-off archive already completed'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
files={}
for script,result in [('singular_positive_minimum_preflight.py','singular-positive-minimum-preflight.json'),('singular_block_shear_control.py','singular-block-shear-control.json')]:
 p=R/'experiments'/script;q=run/result
 assert read(q)['source_sha256']==sha(p)
 files[str(p.relative_to(R)).replace('\\','/')]=sha(p)
 files[str(q.relative_to(R)).replace('\\','/')]=sha(q)
receipt=read(run/'p1-singular-inverse-threshold.receipt.json')
assert receipt['exit_code']==0 and receipt['prompt_sha256']==sha(run/'p1-singular-inverse-threshold.md')
for p in run.glob('p1-singular-inverse-threshold.*'):files[str(p.relative_to(R)).replace('\\','/')]=sha(p)
scope='2026-10-22 当前665项/auditPASS/facade72真实exit0。本轮55打印声明/18模块，精确全子式公式、期望曲率/严格凹、缩放导数极限、有限高斯多项式log平方可积、实际任意固定奇异因子正谱log有限方差、随机均方偏移和full-logdet方差极限已闭合。详见WISHART_QUOTA_20261022_REVIEW_CN.md。最小正谱一般奇异逆矩阈值新增9例40万样本预检/12已知控制和20例81项分块剪切控制，仍OPEN、未计665，不以采样代替证明；Qoder P1指数/边界误报已保留并裁决。当前用户额度授权继续、单协调器、旧小时关闭。人审仍需，冻结发表产物未改/fullLake及Linux独立内核NOT_RUN。'
for name in ['WISHART_STATUS.md','WISHART_LIBRARY_CONTRIBUTION_MAP.md']:
 p=R/'notes'/name;body=p.read_text(encoding='utf-8')
 if not body.startswith(scope+'\n\n'):p.write_text(scope+'\n\n'+body,encoding='utf-8')
p=R/'sheaf/wishart/README.md'
intro='2026-10-22当前入口：665项/auditPASS/facade72真实exit0。本轮55声明/18模块的说明见notes/WISHART_QUOTA_20261022_REVIEW_CN.md。历史队列节点可能已完成，请以接受证据为准；下一张研究卡WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md仍OPEN，尚无待编译证明。用户当前授权至普通额度实际不可用，单协调器，无第二后台研究循环。Linux独立内核/fullLake未运行、发表包未更新。'
body=p.read_text(encoding='utf-8')
if not body.startswith(intro+'\n\n'):p.write_text(intro+'\n\n'+body,encoding='utf-8')
p=R/'.tools/central-mixed-moments-20261019/state.json';state=read(p)
assert state['current_coordinator_token']=='d4b78a7c1a0449debe4e04635d41d232'
state.update(checkpoint=scope,updated_utc=now,current_quota_note='ordinaryUsageAllowed=true primary94% weekly73% at2026-10-22 03:16UTC; observation only, not exhaustion')
p.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for name in ['WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md','WISHART_QUOTA_20261022_REVIEW_CN.md']:files['notes/'+name]=sha(R/'notes'/name)
totals=[read(run/(tag+'-summary.json')) for tag in ['subset','curvature','rank-limit','log-moment-v2','finite-log-square','singular-log-square','offset-l2','variance-limit']]
assert sum(x['new_printed_declarations'] for x in totals)==55
assert sum(x.get('modules',x.get('new_source_modules')) for x in totals)==18
# offset-l2 reused the preceding 35-control result; count each experiment once.
assert sum(x['controls'] for x in totals)-read(run/'offset-l2-summary.json')['controls']==403
assert read(R/'verification/central_mixed_moments/audit.json')['total_declarations']==665
manifest.write_text(json.dumps(dict(archived_utc=now,status='OPEN research card; no added Lean acceptance',accepted_items=665,new_accepted_printed_declarations=55,new_accepted_modules=18,accepted_control_checks=403,exploratory_checks=93,files=files,human_review='REQUIRED',full_lake_build='NOT_RUN',linux_independent_kernel='NOT_RUN'),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
attrs=R/'.gitattributes';body=attrs.read_text(encoding='utf-8')
for rel in files:
 rule='/'+rel+' -text whitespace=cr-at-eol'
 if rule not in body:body+='\n'+rule+'\n'
attrs.write_text(body,encoding='utf-8')
prompt=run/'p4-open-inverse-block-route.md'
prompt.write_text('P4 mathematical route review ONLY. NOT final Lean source review or acceptance. Codex wrote the OPEN card and control scripts. Check only concrete mathematical faults: block shear DS=diag(A,N), smallest POSITIVE singular-value comparison with same rank index, and proposed sufficiency/necessity transfer using independent blocks. Do not cite uncertain literature or treat numerical controls as a proof. b=0/c=m are already separate ALL-moment branches; R=0 excluded. Never confuse singular value with its square. If an issue is not a gap say so, do not invent one. No tools. Report problems only.\n\n'+(R/'notes/WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md').read_text(encoding='utf-8')+'\n\nCONTROL SOURCE SHA256 '+sha(R/'experiments/singular_block_shear_control.py')+'\n'+(R/'experiments/singular_block_shear_control.py').read_text(encoding='utf-8'),encoding='utf-8')
print(json.dumps(dict(status='ARCHIVED OPEN CARD, no Lean changes',accepted=665,exploratory_checks=93)))
