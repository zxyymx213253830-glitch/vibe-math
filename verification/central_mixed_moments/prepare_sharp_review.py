"""Freeze final analytic/hard-edge sources for real issues-only P4."""
from pathlib import Path
import argparse,hashlib,json
pa=argparse.ArgumentParser();pa.add_argument('--actual',action='store_true');args=pa.parse_args()
r=Path(__file__).resolve().parents[2];a=Path(__file__).resolve().parent
s=r/'theory/jin_wishart_formalization/JinWishartFormalization'
key='sharp-actual' if args.actual else 'sharp-analytic'
names=(['CentralMinimumSharpOrder.lean','CentralMinimumHardEdgeCoefficient.lean',
 'CentralMinimumFiniteHardEdgeCoefficient.lean'] if args.actual else
 ['AnalyticPositivePowerLimit.lean','AnalyticPowerTaylorCoefficient.lean','ExponentialPolynomialTaylor.lean'])
snap=a/(key+'-review-snapshot');snap.mkdir(exist_ok=True)
prompt=('P4 concrete issues only, no tools or rewrite. Exact final Codex proof bodies kernelPASS '
 'standard3 axioms. Maincentralm=N+d,N=n+1>0 minimumCDF=1-exp(-Nx)*P(x)/mass forx>=0 '
 'alreadychecked, P realfixedfinitefactorial-functionalpolynomial. ActualCDF NOT analyticat0: '
 'separate continuation G onALLreals. AlreadypositiveTWO localpowerbounds andlogF/logx->d+1. '
 'Generic analyticgermfactorization fromlockedmathlibexists_eventuallyEq_pow_smul_nonzero_iff '
 'plusrightpositivity andfiniteintegerlogexponentk impliesG=x^k H locally,Hanalytic,H0>0. '
 'Loglimituniquenessidentifiesorder, not assuminglimitfromlogratio alone fornonanalyticfunctions. '
 'Taylorfactor analyticremainder givesleadingcoefficient iteratedDeriv k G0/k!, positive. '
 'Finiteformula: -massinv/k! times SUM i=0..k choose(k,i)*(-N)^i*(k-i)!*Pcoeff(k-i). '
 'No unevaluatedprobabilityintegral/derivative in final coefficient, BUT classicalsimplified '
 'factorialcoefficient identity andoriginalgeneralT4prefactorNOTproved. P1 absurd route3 '
 'bootstrapallintegerdfromfinitelymanycontrols REJECTED; nofiniteexamplesasproof. '
 'No smoothnonanalyticfactorization assumed. Numericalsymbols notproof. Humanmeasure/model '
 'review REQUIRED, notwaived. Checkone-sidedfilters/zero/logexponentorder/Taylorfactorials '
 'andfiniteconvolution signs/offbyone. Full final sources:\n')
inputs={}
for name in names:
 data=(s/name).read_bytes();(snap/name).write_bytes(data)
 inputs[name]=dict(sha256=hashlib.sha256(data).hexdigest(),supplied='Full source')
 prompt+='\nFULL '+name+'\n'+data.decode('utf-8')
p=a/('p4-'+key+'-prompt.txt');p.write_text(prompt,encoding='utf-8')
(a/(key+'-review-request.json')).write_text(json.dumps(dict(inputs=inputs,
 prompt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print(key+' exactsnapshotprepared')
