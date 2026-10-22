"""Retain failed checker evidence without duplicate live declaration ownership."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
out=run/'log-moment-v1-superseded-nodes.json';assert not out.exists()
old=[]
for p in sorted((a.PROJECT/'dag/nodes').glob('L-log-moment-*.json')):
 if p.name.startswith('L-log-moment-v2-'):continue
 d=a.read(p);assert d['verification']['status']=='checked_pending_review';old.append(d.copy())
 d['target']=False;d['superseded_declaration']=d.pop('declaration');d['superseded_module']=d.pop('module')
 d['verification']=dict(status='superseded_failed_type_checker',reason='Checker proposition Polynomial shadowed actual polynomial type; no proof-source change. Final corrected evidence belongs to L-log-moment-v2 nodes.',evidence='verification/sheaf_wishart/log-moment-target-types-20261022-locked.txt')
 a.write(p,d)
assert len(old)==8
a.write(out,old)
print('V1_FAILED_CHECKER_NODES_RETAINED_AND_SUPERSEDED',len(old))
