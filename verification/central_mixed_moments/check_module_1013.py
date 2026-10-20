"""Capture actual gated-check exit codes. One serialized compiler child only."""
from datetime import datetime,timezone
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'verification/central_mixed_moments'
name,tag=sys.argv[1:];module='JinWishartFormalization'+('.'+name if name!='FACADE' else '')
source=root/'theory/jin_wishart_formalization'/Path(module.replace('.','/')+'.lean')
log=base/(tag+'.txt');receipt=base/(tag+'.receipt.json')
if log.exists() or receipt.exists():raise SystemExit('Refusing to overwrite evidence')
start=datetime.now(timezone.utc).isoformat()
cmd=[r'D:\miniconda3\python.exe',str(root/'tools/deepseek_prover/collaborative_check.py'),'--session',str(root/'.tools/central-mixed-moments-20261019'),'--source',str(source),'--module',module,'--library',str(root/'.tools/publication-revision-20261016/fresh-project-library'),'--log',str(log)]
code=subprocess.run(cmd,cwd=root).returncode
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(module=module,started_utc=start,ended_utc=datetime.now(timezone.utc).isoformat(),gated_helper_exit_code=code,source_sha256=sha(source),log_sha256=sha(log),log_bytes=log.stat().st_size,policy='Unmodified serialized gated helper, no added compiler flags')
receipt.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print(json.dumps(report));raise SystemExit(code)
