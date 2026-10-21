from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
cfg=a.read(run/'singular-bundle.json')
main=a.LEAN/'JinWishartFormalization.lean'
prefix=''.join('import JinWishartFormalization.'+card['module']+'\n' for card in cfg['modules'])
main.write_bytes(prefix.encode()+main.read_bytes())
s=a.read(R/'verification/central_mixed_moments/spec.json')
reviews={}
for tag in ['average-bound','actual-singular-corrected']:
 reviews[tag]=dict(request=a.rel(run/(tag+'-review-request.json')),prompt=a.rel(run/('p4-'+tag+'-prompt.txt')),
  receipt=a.rel(run/('p4-'+tag+'.receipt.json')),raw=a.rel(run/('p4-'+tag+'.raw.json')),snapshot=a.rel(run/(tag+'-snapshot')),resolution='notes/WISHART_SINGULAR_LOGDET_OFFSET.md')
for card in cfg['modules']:
 tag=card['tag'];mod='JinWishartFormalization.'+card['module'];rev=reviews['actual-singular-corrected' if tag=='actual-singular' else 'average-bound']
 assert not any(t['module']==mod for t in s['targets'])
 s['targets'].append(dict(module=mod,count=len(card['nodes']),log='verification/sheaf_wishart/'+tag+'-20261022-locked.txt',kernel_exit_code_recorded=0))
 a.write(run/('acceptance-'+tag+'.json'),dict(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')),review=rev,audit='verification/central_mixed_moments/audit.json',facade_receipt='verification/sheaf_wishart/facade-63.receipt.json'))
for script,result,seed in [('averaged_cauchy_binet_control.py','averaged-cauchy-binet-control.json',2026102201),('singular_factor_offset_control.py','singular-factor-offset-control.json',2026102202)]:
 s['controls'].append(dict(script='experiments/'+script,result=a.rel(run/result),seed=seed))
for rev in reviews.values():s['reviews'].append({k:rev[k] for k in ['request','prompt','receipt','raw','snapshot']})
s['scope']+=' 2026-10-22 thirteen further declarations: permutation-averaged rectangular Cauchy-Binet with explicit factorial; selected-minor Gram-coefficient/log domination; ACTUAL all-shape fixed arbitrary rectangular/singular/zero B,M aggregate positive-spectrum log L1, individual positive-mode log L1 and UNCONDITIONAL expected generic-rank full-logdet offset with r=min(m,rank stacked[B;M]). Constant is finite expected positive-spectrum log sum, not closed evaluated and not singular full-Gram determinant log. No inverse-moment threshold/rate/parameter-uniformity/channelcoding. Full subset-grouped Cauchy-Binet remains OPEN but is not needed for this route.608 bound items (606 theorem/instance+2constructions). Final-source Qoder exact-definition response false q0/sign/mean alarms explicitly resolved in WISHART_SINGULAR_LOGDET_OFFSET.md; no blanket approval. Humanreview REQUIRED/fullLake and LinuxkernelNOT_RUN/frozenpublication unchanged.'
a.write(R/'verification/central_mixed_moments/spec.json',s)
for p in list((R/'verification/sheaf_wishart').rglob('acceptance-*.json'))+[R/'verification/sheaf_wishart/pilot-acceptance.json']:
 d=a.read(p);d['facade_receipt']='verification/sheaf_wishart/facade-63.receipt.json';a.write(p,d)
print('PREPARED_608; facade63 and auditor still required')
