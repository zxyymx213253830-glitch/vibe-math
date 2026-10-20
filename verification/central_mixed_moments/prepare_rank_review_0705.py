"""Freeze exact review inputs for this fixed-hour rank continuation."""
import hashlib,json,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
source=root/'theory/jin_wishart_formalization/JinWishartFormalization'
tag=sys.argv[1]
names=sys.argv[2:]
snapshot=base/(tag+'-snapshot')
snapshot.mkdir(exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
parts=['P4 adversarial review. You are a different model family from Codex proof author. '
       'No tools available: answer directly, no tool tags. Issues only. '
       'Review exact full Lean sources below for hidden assumptions, unsupported steps, '
       'dimension/mean/rank errors or statement/proof scope mismatch. '
       'Kernel exit0 and standard three axioms are separately recorded, not an independent compilation by you. '
       'Do not claim human approval. No numerical evidence is used as proof. '
       'Zero dimensions are intentional. Fixed B:p-by-n, M:m-by-n, sourceZ:m-by-p; '
       'CN1 source uses two standard real coordinates divided by sqrt2. '
       'Inheritance of polynomial null sets/Fubini and model correspondence remains [需人工审查]. '
       'Review the scope of this supplied module; imported results are separately checked '
       'and are not claimed to have been re-proved here.\n']
inputs={}
for name in names:
    b=(source/name).read_bytes()
    (snapshot/name).write_bytes(b)
    inputs[name]=dict(sha256=sha(b),supplied='Full source')
    parts += ['\nFULL SOURCE '+name+'\n'+b.decode('utf-8')]
prompt=base/('p4-'+tag+'-prompt.txt')
prompt.write_text('\n'.join(parts),encoding='utf-8')
request=base/(tag+'-review-request.json')
request.write_text(json.dumps(dict(inputs=inputs,prompt_sha256=sha(prompt.read_bytes())),indent=2)+'\n',encoding='utf-8')
print(tag,len(prompt.read_text(encoding='utf-8')),list(inputs))
