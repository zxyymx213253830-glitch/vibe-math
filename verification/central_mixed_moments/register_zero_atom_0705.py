import json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
path=base/'spec.json'
spec=json.loads(path.read_text(encoding='utf-8'))
tag='minimum-zero-atom-0705'
assert json.loads((base/('p4-'+tag+'.receipt.json')).read_text(encoding='utf-8'))['exit_code']==0
body=(base/(tag+'-1.txt')).read_text(encoding='utf-8')
assert 'error' not in body and 'sorryAx' not in body
assert not any(x['module']=='JinWishartFormalization.CorrelatedMinimumZeroAtom' for x in spec['targets'])
spec['targets'].append(dict(module='JinWishartFormalization.CorrelatedMinimumZeroAtom',count=5,
 log='verification/central_mixed_moments/'+tag+'-1.txt',kernel_exit_code_recorded=0))
spec['reviews'].append(dict(request='verification/central_mixed_moments/'+tag+'-review-request.json',
 prompt='verification/central_mixed_moments/p4-'+tag+'-prompt.txt',
 receipt='verification/central_mixed_moments/p4-'+tag+'.receipt.json',
 raw='verification/central_mixed_moments/p4-'+tag+'.raw.json',
 snapshot='verification/central_mixed_moments/'+tag+'-snapshot'))
spec['controls'].append(dict(script='experiments/correlated_rank_zero_mode_control.py',
 result='verification/central_mixed_moments/correlated-rank-zero-mode-control.json',seed=None))
spec['scope']+=' Five further checked declarations give the exact minimum COLUMN Gram zero-atom for n>0: probability1 iff min(m,rank stacked[B;M])<n, else0. Fullrank/strictpositivity and deterministic spectral/rank bridges included. Total507 theorem/instance+2 constructions=509 items. The n=0 minimum is intentionally excluded. Final source Qoder P4 delivered; Measure.real is toReal of same measure, NOT a different real sample space; false inherited-precondition alarms resolved against exact checked source. Human measure/model review remains REQUIRED.'
path.write_text(json.dumps(spec,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Registered5 zero-atom declarations; cumulative509.')
