"""Exact final-source freeze for actual one-dimensional minimum density P4."""
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parents[2];a=Path(__file__).resolve().parent
s=r/'theory/jin_wishart_formalization/JinWishartFormalization';snap=a/'minimum-density-review-snapshot';snap.mkdir(exist_ok=True)
names=['MeasureFromPositivePrimitive.lean','CentralMinimumActualDensity.lean','CentralMinimumPDF.lean']
prompt=('P4 issues only, no tools/rewrite. FinalCodex12 declarations kernelPASS standard3axioms. '
 'Actual generalCENTRAL m=N+d,N=n+1>0 minimumcdf alreadyproved independentlyviaactualmatrixdensity '
 'andcone translation: F(x)=1-exp(-Nx)*P(x)/M forx>=0,0 forx<0. Pfinitefactorialfunctional '
 'polynomial, Mpositivefactorialproduct, P0=M. Nowreconstruct actualpushforwardmeasure '
 '=Lebesgue.withDensity(Ioi0.indicator(ofReal(exp(-Nx)/M*(N*P-Pderivative)))). '
 'ONEdimensional marginal NOTG2jointdensity. GenericμprobabilityCDFagreementplusglobalprimitive '
 'Gderivativecontinuoush yieldsmeasureidentitybyext_of_Iic, FTC onIoc0x andlintegralofReal. '
 'No targetPDFassumption inactualtheorem. h>=0 onx>0 PROVEDusingmonotoneactualCDFandlocal '
 'derivativeequality. G0=0 normalization impliesnoatom0; densityvalue0atboundaryirrelevant. '
 'GlobalGnotactualCDFonnegativeaxis, no assumedanalyticCDF. No fictitiousuniformnoncentralclaim '
 'orclassicalprefactoridentity. Examineboundaryx0/negative, truncationofReal, finiteintegral '
 'conversion, actualGaussianmapmeasurability, variance rawGraminterpretation. Humanmeasure/model '
 'reviewREQUIRED. Exact fullsources:\n')
inputs={}
for name in names:
 b=(s/name).read_bytes();(snap/name).write_bytes(b)
 inputs[name]=dict(sha256=hashlib.sha256(b).hexdigest(),supplied='Full source')
 prompt+='\nFULL '+name+'\n'+b.decode('utf-8')
p=a/'p4-minimum-density-prompt.txt';p.write_text(prompt,encoding='utf-8')
(a/'minimum-density-review-request.json').write_text(json.dumps(dict(inputs=inputs,
 prompt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print('Prepared exact minimum-density source review')
