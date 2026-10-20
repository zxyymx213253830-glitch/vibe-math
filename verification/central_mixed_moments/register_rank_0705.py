"""Register only completed leaves/reviews; main compilation remains a separate gated step."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
specpath=base/'spec.json'
spec=json.loads(specpath.read_text(encoding='utf-8'))
targets=[('CorrelatedRankUpperBound',3,'rank-upper-0705-3.txt'),
 ('CorrelatedRankWitness',2,'rank-witness-0705-2.txt'),
 ('MatrixRankCompression',1,'rank-compression-0705-2.txt'),
 ('CorrelatedGaussianGenericRank',4,'gaussian-generic-rank-0705-4.txt'),
 ('CorrelatedLogDetGenericRank',3,'logdet-generic-rank-0705-2.txt')]
for name,count,log in targets:
    body=(base/log).read_text(encoding='utf-8')
    assert 'error' not in body and 'sorryAx' not in body,log
    module='JinWishartFormalization.'+name
    assert not any(x['module']==module for x in spec['targets']),module
    spec['targets'].append(dict(module=module,count=count,
        log='verification/central_mixed_moments/'+log,kernel_exit_code_recorded=0))
for tag in ['rank-algebra-0705','rank-compression-0705','gaussian-rank-0705','logdet-generic-rank-0705']:
    receipt=json.loads((base/('p4-'+tag+'.receipt.json')).read_text(encoding='utf-8'))
    assert receipt['exit_code']==0,tag
    spec['reviews'].append(dict(request='verification/central_mixed_moments/'+tag+'-review-request.json',
      prompt='verification/central_mixed_moments/p4-'+tag+'-prompt.txt',
      receipt='verification/central_mixed_moments/p4-'+tag+'.receipt.json',
      raw='verification/central_mixed_moments/p4-'+tag+'.raw.json',
      snapshot='verification/central_mixed_moments/'+tag+'-snapshot'))
spec['controls'].append(dict(script='experiments/correlated_rank_compression_control.py',
 result='verification/central_mixed_moments/correlated-rank-compression-control.json',seed=None))
spec['scope']+=' Fixed arbitrary rectangular/singular/zero B and fixed M: actual complex affine rank(ZB+M)=min(m,rankB+rank(M restricted kerB)) AE, equivalently min(m,rank stacked[B;M]); actual expected full-logdet/logrho tends this deterministic rank. Thirteen new declarations include universal rank-nullity/witness/compression helpers, not thirteen probability breakthroughs. 502 theorem/instance+2 constructions=504 items. Final exact-source Qoder P4 delivered, false API/domain/zero-centre alarms explicitly resolved in WISHART_GENERIC_RANK.md, inherited human review REQUIRED. No growing-parameter uniformity, logdet offset or singular inverse-moment threshold asserted. Fullbuild NOT_RUN/frozenpublicationUNCHANGED.'
specpath.write_text(json.dumps(spec,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
main=root/'theory/jin_wishart_formalization/JinWishartFormalization.lean'
body=main.read_text(encoding='utf-8')
imp='import JinWishartFormalization.CorrelatedLogDetGenericRank\n'
assert imp not in body
main.write_text(imp+body,encoding='utf-8')
print('Registered13 completed leaves; main import added, facade46 still requires real compilation.')
