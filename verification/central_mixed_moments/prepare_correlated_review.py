"""Freeze the exact checked correlated-column sources for real P4, no generation."""
from pathlib import Path
import hashlib,json,argparse
parser=argparse.ArgumentParser()
parser.add_argument('--inverse',action='store_true')
args=parser.parse_args()
root=Path(__file__).resolve().parents[2]
area=Path(__file__).resolve().parent
source=root/'theory/jin_wishart_formalization/JinWishartFormalization'
names=['GramMinimumColumnComparison.lean','CorrelatedColumnMinimum.lean']
key='correlated-column'
if args.inverse:
 names=['CorrelatedColumnInverseMoments.lean']
 key='correlated-inverse'
snapshot=area/(key+'-review-snapshot')
snapshot.mkdir(exist_ok=True)
prompt=('P4 critical issues only, no rewrite/tools. Codex final13 theorem bodies have kernel PASS, '
 'standard propext/Classical.choice/Quot.sound only. Arbitrary rectangular A including singular. '
 'Fixed invertible square complex B, physical sample Z B + M; normalized mean M B^-1, '
 'N>0, m>=N for diversity, fixed M arbitrary includingzero. Covariance of row samples '
 'E[(Zrow B)^H(Zrow B)] is B^H B. CLM norm is OPERATOR norm, '
 'C(B)=max(1,norm(CLMB)^2), not Frobenius norm and not1+norm^2. '
 'Pointwise bounds: min(AB)<=C(B)min(A), min(A)<=C(Binv)min(AB). '
 'Hence Fnorm(x/C(B)) <= Fcorr(x) <= Fnorm(C(Binv)*x). '
 'Earlier P1 incorrectly reversed first CDF inequality and asserted false Loewner '
 'B^H H B<=norm(B)^2 H for arbitraryPSD H; neither used. No targetdensityassumption, '
 'no sharpconstant, no growing-conditionnumber uniformity. Inspect directions/zero/rank/mean/covariance. '
 'Do not waive human measure/model review, which remains REQUIRED. Full checkedsources follow.\n')
if args.inverse:
 prompt=('P4 issues only, no rewrite/tools. Five final Codex statements have kernelPASS standard '
 '3 axioms. Generic inverse-real-moment transfer uses measurable f,g strictlypositiveAE '
 'and pointwise f<=c*g,g<=C*f withc,C>0. Then anyp>0 inversepowersintegrable iff. '
 'Zero inverse convention handled byAEpositive actual Gaussian minimum, not bypointwiserank. '
 'Actual ZB+M, Bfixedinvertible square, arbitraryfixed M incl0, m=d+N,N=n+1>0. '
 'Normalizedmean M B^-1 fixed. Arbitraryp>0 inverseGramminimum integrable iff p<d+1, '
 'criticalandhigherNONNEGATIVEENNRealintegralTOP. Not realBochnerinfinity, no exactmomentvalue, '
 'no nonsingularA assumption. Upstream pointwisecontrol C(B)=max(1,opnormB^2) andC(Binv)>0 '
 'gives f<=C(B)g,g<=C(Binv)f for f=correlatedGramminimum,g=normalizeduncorrelatedminimum. '
 'Inspect reciprocaldirection,rpowcriticalcase,AEandphysicalmean. Humanmeasure/modelreviewREQUIRED.\n')
inputs={}
for name in names:
 data=(source/name).read_bytes();(snapshot/name).write_bytes(data)
 inputs[name]={'sha256':hashlib.sha256(data).hexdigest(),'supplied':'Full source'}
 prompt+='\nFULL '+name+'\n'+data.decode('utf-8')
path=area/('p4-'+key+'-prompt.txt');path.write_text(prompt,encoding='utf-8')
(area/(key+'-review-request.json')).write_text(json.dumps(dict(inputs=inputs,
 prompt_sha256=hashlib.sha256(path.read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print('Frozen exact checked source for '+key+' P4')
