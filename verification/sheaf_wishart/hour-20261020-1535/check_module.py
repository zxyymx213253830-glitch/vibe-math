"""Receipt wrapper; compilation is exclusively through the existing shared gate."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
module, tag = sys.argv[1:3]
source = ROOT / 'theory/jin_wishart_formalization' / Path(module.replace('.', '/') + '.lean')
if len(sys.argv) > 3:
    source = (ROOT / sys.argv[3]).resolve()
log = BASE / (tag + '.txt')
receipt = BASE / (tag + '.receipt.json')
if log.exists() or receipt.exists():
    raise SystemExit('Refusing to overwrite previous evidence')
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
before = sha(source)
started = datetime.now(timezone.utc).isoformat()
cmd = [r'D:\miniconda3\python.exe', '-X', 'utf8', 'tools/deepseek_prover/collaborative_check.py',
       '--session', '.tools/central-mixed-moments-20261019', '--source', str(source),
       '--module', module, '--library', '.tools/publication-revision-20261016/fresh-project-library',
       '--log', str(log)]
if len(sys.argv) > 3:
    cmd += ['--root', str(source.parent)]
result = subprocess.run(cmd, cwd=ROOT)
data = dict(started_utc=started, ended_utc=datetime.now(timezone.utc).isoformat(), module=module,
            source=source.relative_to(ROOT).as_posix(), source_sha256_before=before,
            source_sha256=sha(source), gated_helper_exit_code=result.returncode,
            log_sha256=sha(log) if log.exists() else None)
receipt.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
print(json.dumps(data))
raise SystemExit(result.returncode)
