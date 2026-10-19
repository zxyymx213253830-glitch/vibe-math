"""Fixed-seed exact sparse binomial-sum control with independent binomial identity."""
from pathlib import Path
import random,math,json,hashlib
rng=random.Random(2026101920);records=[]
for N in range(17):
 assert sum(math.comb(N,i) for i in range(N+1))==2**N
 for K in range(10):
  f=[rng.randint(-9,9) for _ in range(K)]
  left=sum(math.comb(N,i)*(f[i] if i<K else 0) for i in range(N+1))
  right=sum((math.comb(N,i) if i<=N else 0)*f[i] for i in range(K))
  assert left==right
  records.append(dict(N=N,K=K,value=left))
result=dict(seed=2026101920,status='PASS exact sparse binomial truncation and independent sumchoose=2^N controls; not proof',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records=records)
p=Path(__file__).resolve().parents[1]/'verification/central_mixed_moments/choose-truncation-control.json';p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(result['status'])
