"""One local-only DeepSeek P4 through the existing exclusive compute gate."""
from pathlib import Path
import subprocess,sys,hashlib,json
from datetime import datetime,timezone
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
tag='paper-spectral-orbit-final-local'
prompt=run/('p4-'+tag+'-prompt.txt');prefix=run/('p4-'+tag)
native=Path(str(prefix)+'.ollama.json');receipt=Path(str(prefix)+'.receipt.json')
assert not native.exists() and not receipt.exists()
started=a.now()
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-local-P4-paper-spectrum'):
    cmd=[str(a.PYTHON),'-X','utf8',str(R/'tools/deepseek_prover/collaborative_check.py'),
         '--session',str(a.SESSION),'--review-prompt',str(prompt),'--response',str(native),
         '--log',str(Path(str(prefix)+'.local.log'))]
    code=subprocess.run(cmd,cwd=R).returncode
rep=dict(started_utc=started,ended_utc=a.now(),exit_code=code,
         requested_model='deepseek-prover-v2:7b',provider='local Ollama 127.0.0.1:11434',
         no_external_destination=True,tools_disabled=True,independent_compilation=False,
         prompt_sha256=a.sha(prompt),runner_sha256=a.sha(Path(__file__)),
         model_manifest_digest='3d08a648fcd62941fd88c507cd9113f529c05637b58d6e33090c382da656327b',
         policy='One local request; shared compute lock; default180s; no tools or proof authorship')
if code==0:
    raw=a.read(native);text=raw.get('response','')
    a.write(Path(str(prefix)+'.raw.json'),dict(is_error=not bool(raw.get('done') and text.strip()),result=text,provider=rep['provider'],native_response=a.rel(native),native_sha256=a.sha(native),model=raw.get('model'),done_reason=raw.get('done_reason')))
    Path(str(prefix)+'.response.md').write_text(text+'\n',encoding='utf-8')
a.write(receipt,rep)
print(json.dumps(rep))
sys.exit(code)
