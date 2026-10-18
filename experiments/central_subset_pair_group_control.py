"""Deterministic exact enumeration control for grouping two-subset statistics."""
from collections import Counter
from pathlib import Path
from fractions import Fraction
from math import comb, factorial
import hashlib
import json

def moment(d,n,p):
    ans=Fraction(1)
    for j in range(n):ans*=Fraction(factorial(d+j+p),factorial(d+j))
    return ans

records=[]
for n in range(9):
    actual=Counter((s.bit_count(),t.bit_count(),(s&t).bit_count())
                   for s in range(2**n) for t in range(2**n))
    grouped=Counter()
    for a in range(n+1):
        for c in range(a+1):
            for b in range(n-a+1):
                grouped[a,c+b,c]+=comb(n,a)*comb(a,c)*comb(n-a,b)
    assert actual==grouped and sum(actual.values())==4**n
    coefficients=[Fraction(0) for _ in range(2*n+1)]
    for (a,t,c),count in actual.items():
        left=a-c;right=t-c
        mixed=moment(n-c,c,2)*moment(n-a,left,1)*moment(n-t,right,1)
        ratio=Fraction(factorial(n),factorial(n-a))*Fraction(factorial(n),factorial(n-t))*Fraction(n+1,n-c+1)
        assert mixed==ratio
        coefficients[2*n-a-t]+=count*mixed/Fraction(factorial(n)*factorial(n+1))
    assert coefficients[0]==1
    if n: assert coefficients[1]==n and coefficients[2]==Fraction(n*n,2)
    records.append(dict(n=n,pair_count=sum(actual.values()),cardinality_classes=len(actual),coefficients=[str(x) for x in coefficients]))
assert records[1]['coefficients']==['1','1','1/2']
root=Path(__file__).resolve().parents[1]
out=dict(seed=None,method='No randomness; exhaustive exact finite integer/rational enumeration',
         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         status='PASS n=0..8 pair histograms and factorial ratios; not a general proof',
         known_control='4^n total pairs, n=1 Gamma(3,1) tail polynomial',records=records)
(root/'verification/central_mixed_moments/group-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS exact grouping n=0..8; 4^n counting and Gamma(3,1) polynomial controls')
