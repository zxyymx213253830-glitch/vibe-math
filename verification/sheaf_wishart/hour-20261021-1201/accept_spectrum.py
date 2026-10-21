from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
run=Path(__file__).parent
review=dict(request=a.rel(run/'spectrum-review-request.json'),prompt=a.rel(run/'p4-spectrum-prompt.txt'),
 receipt=a.rel(run/'p4-spectrum.receipt.json'),raw=a.rel(run/'p4-spectrum.raw.json'),
 snapshot=a.rel(run/'spectrum-snapshot'),resolution='notes/WISHART_POSITIVE_SPECTRUM_LOG.md')
ev=dict(target_lock=a.rel(run/'locks-spectrum.json'),check=a.rel(run/'check-spectrum.json'),review=review,
 audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-61.receipt.json')
a.write(run/'acceptance-spectrum.json',ev)
specpath=R/'verification/central_mixed_moments/spec.json'
s=a.read(specpath)
assert not any(x['module'].endswith('.PositiveSpectrumLogIntegrability') for x in s['targets'])
s['targets'].append(dict(module='JinWishartFormalization.PositiveSpectrumLogIntegrability',count=4,
 log='verification/sheaf_wishart/positive-spectrum-20261021-locked.txt',kernel_exit_code_recorded=0))
s['controls'].append(dict(script='experiments/positive_spectrum_log_control.py',
 result=a.rel(run/'positive-spectrum-control.json'),seed=2026102125))
s['reviews'].append({k:review[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' Four deterministic/conditional aggregate-positive-log declarations added: integrable nonnegative trace plus aggregate-log L1 implies each mode log L1. Actual correlated offset still assumes aggregate L1 explicitly; arbitrary singular pseudoDet bridge remains OPEN. 585 bound items (583 theorem/instance+2 constructions), facade61 realexit0. Qoder cancellation alarm resolved by exact upper/lower bounds, not ignored. Humanreview REQUIRED; Linux kernel NOT_RUN.'
a.write(specpath,s)
paths=[R/'verification/sheaf_wishart/pilot-acceptance.json']
paths+=list((R/'verification/sheaf_wishart/hour-20261020-1535').glob('acceptance-*.json'))
paths+=list((R/'verification/sheaf_wishart/continuation-20261021').glob('acceptance-*.json'))
paths+=list(run.glob('acceptance-*.json'))
for path in paths:
    data=a.read(path);data['facade_receipt']=ev['facade_receipt'];a.write(path,data)
print('SPEC_PREPARED_585; run auditor then native accept')
