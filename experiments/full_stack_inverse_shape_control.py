"""Finite exact shape controls before eliminating the fixed normal form.
Not a probability proof. Reference: simultaneous dimension identities.
"""
from pathlib import Path
import hashlib,json,random
seed=2026102235
rng=random.Random(seed)
cases=[(a,b,c) for a in range(1,9) for b in range(1,9) for c in range(1,9)]
rng.shuffle(cases)
checks=0
for a,b,c in cases:
    m,n=a+c,b+c
    canonical=max(a,b)-min(a,b)+1
    physical=max(m,n)-min(m,n)+1
    assert canonical==physical==abs(m-n)+1
    checks+=2
    assert min(m,n)-1<n and min(a,b)-1<b and c-1<c
    checks+=1
# Missing the noiseless-column dimension gives a false threshold in general.
a,b,c=2,2,3
assert abs((a+c)-b)+1 != abs((a+c)-(b+c))+1
checks+=1
out=dict(status='PASS exact finite controls, not general proof',seed=seed,
    checks=checks,cases=len(cases),reference='m=a+c,n=b+c; |m-n|=|a-b|',
    negative_control='omitting c from n changes the threshold',
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
p=Path('verification/sheaf_wishart/quota-20261022-0949/full-stack-inverse-shape-control.json')
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
