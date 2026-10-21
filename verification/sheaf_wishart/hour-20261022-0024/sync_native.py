"""Source-only native workcopy. Never invokes a Linux compiler or migrates secrets."""
from pathlib import Path
import hashlib,json,subprocess,tarfile,time
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
snap=R/'.tools/sheaf-native-hour-20261022-0024/snapshot'
manifest=json.loads((snap/'manifest.json').read_text())
(run/'linux-source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
archive=snap.parent/'snapshot.tar'
with tarfile.open(archive,'w') as t:
    for p in snap.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:t.add(p,arcname=p.relative_to(snap).as_posix())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(run/'linux-source-package.json').write_text(json.dumps(dict(archive_sha256=sha(archive),manifest_sha256=sha(snap/'manifest.json'),files=len(manifest['files']),credentials=False,oleans=False),indent=2)+'\n')
code=r'''
from pathlib import Path
import tarfile,json,hashlib,sys,time
base=Path('/root/wishart-sheaf-hour-20261022-0024')
base.mkdir(exist_ok=False)
with tarfile.open('/mnt/d/vibe math/.tools/sheaf-native-hour-20261022-0024/snapshot.tar') as t:t.extractall(base,filter='data')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((base/'manifest.json').read_text())
for name,digest in m['files'].items():assert sha(base/name)==digest,name
sys.path.insert(0,str(base/'upstream'))
import leanindex as li
li.ROOT=base;li.LEAN=base/'lean'
import dag_queue as dq
t=time.monotonic();decls,imports=li.scan();g=dq.Dag(dq.load())
targets=['S17-general-singular-offset','S18-rank-coordinate-minor','S19-actual-expected-logdet-derivative']
for k in targets:assert g.n[k]['verification']['status']=='verified'
print(json.dumps(dict(native_directory=str(base),manifest_sha256=sha(base/'manifest.json'),verified_input_files=len(m['files']),modules=len(imports),lexical_declarations=len(decls),dag_nodes=len(g.n),new_target_records=targets,stage1=g.stage1(),stage2=g.stage2()[0],seconds=time.monotonic()-t,kernel_evidence='Windows serial gate receipts; no independent Linux compilation',linux_lean_compile='NOT_RUN')))
'''
t=time.monotonic()
p=subprocess.run(['wsl.exe','--distribution','SheafBenchUbuntu','--user','root','--exec','python3','-X','utf8','-c',code],capture_output=True,timeout=90)
decode=lambda b:b.decode('utf-16-le' if b'\0' in b else 'utf8',errors='replace')
receipt=dict(exit_code=p.returncode,seconds=time.monotonic()-t,stdout=decode(p.stdout),stderr=decode(p.stderr))
(run/'linux-source-index.receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt,ensure_ascii=False));assert p.returncode==0
