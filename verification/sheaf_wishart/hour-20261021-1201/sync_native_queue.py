"""Append the new OPEN obligations in a fresh Linux directory; keep old snapshot immutable."""
from pathlib import Path
import subprocess,json,time,hashlib
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
code=r'''
from pathlib import Path
import hashlib,json,shutil,sys
old=Path('/root/wishart-sheaf-hour-20261021-1201')
base=Path('/root/wishart-sheaf-hour-20261021-1201-queue')
shutil.copytree(old,base,ignore=shutil.ignore_patterns('__pycache__'))
names=['L-rectangular-cauchy-binet','L-gram-minor-coefficient','L-gram-rank-spectral-coefficient','S17-general-singular-offset','DEFERRED-polynomial-negative-log']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((base/'manifest.json').read_text())
for name in names:
 src=Path('/mnt/d/vibe math/sheaf/wishart/dag/nodes')/(name+'.json')
 dst=base/'dag/nodes'/(name+'.json');shutil.copyfile(src,dst)
 m['files']['dag/nodes/'+name+'.json']=sha(dst)
(base/'manifest.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
for name,digest in m['files'].items():assert sha(base/name)==digest,name
sys.path.insert(0,str(base/'upstream'))
import leanindex as li
li.ROOT=base;li.LEAN=base/'lean'
import dag_queue as dq
decls,imports=li.scan();g=dq.Dag(dq.load())
for name in names[:4]:assert not dq.has_decl(g.n[name]) and g.n[name]['verification']['status']=='open_not_formalized'
print(json.dumps(dict(native_directory=str(base),verified_files=len(m['files']),manifest_sha256=sha(base/'manifest.json'),modules=len(imports),dag_nodes=len(g.n),stage2=g.stage2()[0],new_nodes_status='OPEN_NOT_FORMALIZED; not a proof',linux_lean_compile='NOT_RUN')))
'''
t=time.monotonic();p=subprocess.run(['wsl.exe','--distribution','SheafBenchUbuntu','--user','root','--exec','python3','-X','utf8','-c',code],capture_output=True,timeout=60)
decode=lambda b:b.decode('utf-16-le' if b'\0' in b else 'utf8',errors='replace')
r=dict(exit_code=p.returncode,seconds=time.monotonic()-t,stdout=decode(p.stdout),stderr=decode(p.stderr),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(run/'linux-next-queue.receipt.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(r,ensure_ascii=False));assert p.returncode==0
