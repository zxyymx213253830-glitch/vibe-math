import json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
path=base/'spec.json'
spec=json.loads(path.read_text(encoding='utf-8'))
tag='noiseless-floor-inverse-0705'
assert json.loads((base/('p4-'+tag+'.receipt.json')).read_text(encoding='utf-8'))['exit_code']==0
for name,count,log in [('CorrelatedNoiselessSpectralFloor',4,'noiseless-floor-0705-3.txt'),
                       ('CorrelatedNoiselessInverseMoments',2,'noiseless-inverse-0705-1.txt')]:
    body=(base/log).read_text(encoding='utf-8')
    assert 'error' not in body and 'sorryAx' not in body
    module='JinWishartFormalization.'+name
    assert not any(x['module']==module for x in spec['targets'])
    spec['targets'].append(dict(module=module,count=count,
      log='verification/central_mixed_moments/'+log,kernel_exit_code_recorded=0))
spec['reviews'].append(dict(request='verification/central_mixed_moments/'+tag+'-review-request.json',
 prompt='verification/central_mixed_moments/p4-'+tag+'-prompt.txt',
 receipt='verification/central_mixed_moments/p4-'+tag+'.receipt.json',
 raw='verification/central_mixed_moments/p4-'+tag+'.raw.json',
 snapshot='verification/central_mixed_moments/'+tag+'-snapshot'))
for script,result,seed in [('experiments/correlated_noiseless_floor_control.py',
 'verification/central_mixed_moments/correlated-noiseless-floor-control.json',None),
 ('experiments/noiseless_row_logdet_offset_preflight.py',
 'verification/central_mixed_moments/noiseless-row-offset-preflight.json',202610200705)]:
    spec['controls'].append(dict(script=script,result=result,seed=seed))
spec['scope']+=' Six further declarations prove: if fixed M restricted to kerB surjects onto m-dimensional output (m>0 for minima), fixed C satisfies BC=0,MC=I, hence EVERY noise Z has rowGram minimum >=delta>0 and actual Gaussian ROW inverse minimum all real p>=0 moments integrable. This is ROW Gram XX^H, not singular COLUMN Gram X^H X. Total513 theorem/instance+2 constructions=515. Exact35 controls plus scalar200000-seed next-offset preflight; general row offset remains OPEN. Final2-source real Qoder P4 delivered/resolved: max enlarging denominator weakens floor, no false m<=p assumption. Humanreview REQUIRED/fullbuildNOT_RUN/frozenpublicationUNCHANGED.'
path.write_text(json.dumps(spec,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Registered6 noiseless-floor/moment declarations; total515.')
