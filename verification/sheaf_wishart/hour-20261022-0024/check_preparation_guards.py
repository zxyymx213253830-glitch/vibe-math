"""Completed one-off preparations must refuse reruns before touching bound files."""
from pathlib import Path
import sys,subprocess,hashlib,json
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bound=[R/'theory/jin_wishart_formalization/JinWishartFormalization.lean',R/'verification/central_mixed_moments/spec.json']
before={str(p.relative_to(R)):sha(p) for p in bound};rows=[]
for name in ['accept_gram_minor.py','accept_singular_bundle.py','accept_derivative.py']:
 p=run/name
 result=subprocess.run([r'D:\miniconda3\python.exe','-X','utf8',str(p)],cwd=R,capture_output=True,text=True,encoding='utf-8',timeout=15)
 assert result.returncode!=0 and 'Refusing repeated preparation before any mutation' in result.stderr,name
 assert before=={str(p.relative_to(R)):sha(p) for p in bound},name
 rows.append(dict(script=name,source_sha256=sha(p),exit_code=result.returncode,guard='duplicate preparation refused before mutation'))
out=dict(status='PASS three completed-preparation rerun guards',items=rows,bound_file_hashes=before,kernel_calls=0,model_calls=0)
(run/'preparation-guard-regression.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(out['status'])
