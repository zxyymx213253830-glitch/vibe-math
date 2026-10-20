"""Capture the gated facade retry exit code without changing compiler/gate settings."""
from datetime import datetime,timezone
import hashlib,json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
log=base/'facade-48.txt'
started=datetime.now(timezone.utc).isoformat()
command=[r'D:\miniconda3\python.exe',str(root/'tools/deepseek_prover/collaborative_check.py'),
 '--session',str(root/'.tools/central-mixed-moments-20261019'),
 '--source',str(root/'theory/jin_wishart_formalization/JinWishartFormalization.lean'),
 '--module','JinWishartFormalization','--library',str(root/'.tools/publication-revision-20261016/fresh-project-library'),
 '--log',str(log)]
code=subprocess.run(command,cwd=root).returncode
report=dict(started_utc=started,ended_utc=datetime.now(timezone.utc).isoformat(),
 gated_helper_exit_code=code,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
 log_bytes=log.stat().st_size,policy='Same serialized gated helper, no extra compiler flags; retry of empty-log facade47 failure')
(base/'facade-48.receipt.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report))
raise SystemExit(code)
