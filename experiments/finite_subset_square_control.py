"""Finite rational kernel-to-squares controls with signed coefficients; not proof."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import random,hashlib,json
SEED=2026102505;rng=random.Random(SEED);checks=[]
def ck(l,v):
 assert v,l
 checks.append(l)
for n in range(7):
 N=1<<n
 for trial in range(4):
  f=[Q(rng.randint(-4,5),rng.randint(1,5)) for i in range(N)]
  lhs=sum((f[u]*f[v]/((u|v).bit_count()+1) for u in range(N) for v in range(N)),Q(0))
  rhs=sum((sum((f[u] for u in range(N) if u&r==u),Q(0))**2/((n+1)*comb(n,r.bit_count())) for r in range(N)),Q(0))
  ck('signed squares '+str((n,trial)),lhs==rhs)
  ck('positive kernel '+str((n,trial)),lhs>=0)
  if n==0:ck('empty base '+str(trial),lhs==f[0]**2)
  if n==1:ck('one point closed '+str(trial),lhs==f[0]**2+f[0]*f[1]+f[1]**2/2)
  if n>=2 and lhs!=0:ck('missing outer divisor rejected '+str((n,trial)),lhs!=(n+1)*rhs)
r=dict(seed=SEED,checks=len(checks),status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controls=checks,scope='Independent signed rational double-sum versus weighted subset-square transform, empty/one-point calibration; not proof')
Path('verification/sheaf_wishart/quota-20261022-0949/finite-subset-square-control.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('PASS',len(checks),'exact controls')
