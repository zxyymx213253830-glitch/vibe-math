"""Retain the failed expected-type grouping attempt without duplicate live ownership."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
record=run/'positive-transport-v1-retirement.json';assert not record.exists()
snap=run/'positive-transport-v1-retired-nodes';snap.mkdir(exist_ok=False)
files={}
for p in (R/'sheaf/wishart/dag/nodes').glob('L-positive-transport-*.json'):
 assert not p.name.startswith('L-positive-transport-v2-')
 raw=p.read_bytes();(snap/p.name).write_bytes(raw);files[p.name]=hashlib.sha256(raw).hexdigest()
 d=json.loads(raw);d['superseded_declaration']=d.pop('declaration');d['superseded_module']=d.pop('module')
 d['target']=False;d['verification']={'status':'superseded_failed_type_checker','reason':'Expected type v1 grouped implication/iff incorrectly; proof source unchanged; relock corrected independent checker as v2.'}
 p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
assert len(files)==5
record.write_text(json.dumps(dict(retired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),nodes=files,failed_checker='SheafPositiveTransportTargets.lean',failure='unparenthesized implication/iff changed expected proposition grouping',proof_source_changed=False,old_lock_and_logs_preserved=True),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('RETIRED5_FAILED_TYPE_CHECKER_NODES; source bodies unchanged')
