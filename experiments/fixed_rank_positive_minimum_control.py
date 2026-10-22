"""Exact finite ordered-spectrum enumeration before the positive-minimum proof."""
from itertools import combinations_with_replacement
from pathlib import Path
import json,hashlib,sys
checks=0;seqs=0;zero_cases=0;negative_cases=0
for n in range(7):
 for raw in combinations_with_replacement([-1,0,1,2,3],n):
  f=tuple(reversed(raw));r=sum(x>0 for x in f);seqs+=1
  negative_cases+=int(any(x<0 for x in f))
  for i,x in enumerate(f):
   assert (x>0)==(i<r);checks+=1
  if r:
   assert f[r-1]>0 and all(f[r-1]<=x for x in f if x>0);checks+=1
  else:zero_cases+=1
# Closed structural-zero reference and a negative control for omitted monotonicity.
f=(3,2,0,0);assert f[1]==2 and min(f)==0;checks+=1
unsorted=(0,2);r=sum(x>0 for x in unsorted)
assert not all((x>0)==(i<r) for i,x in enumerate(unsorted));checks+=1
out=dict(status='PASS exact finite controls, not the general theorem',seed=2026102215,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checks=checks,
 sequences=seqs,rank_zero_cases=zero_cases,negative_entry_sequences=negative_cases,
 scope='Antitone real sequence positive prefix; no inverse-moment theorem')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
