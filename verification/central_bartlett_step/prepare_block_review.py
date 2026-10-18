"""Final complete source snapshot of the actual Bartlett joint-law milestone."""
import argparse
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
parser=argparse.ArgumentParser()
parser.add_argument('--followup',action='store_true')
args=parser.parse_args()
prompt = '''P4 stringent mathematical/semantic review, another model family from proof author Codex.
Report only concrete issues, not a rewrite, max500words. No tools or independent compilation.
ALL 20 declarations in the three supplied final files passed local Lean standard-axiom checks.
Main claim: actual CENTRAL CN(0,1) matrix of (m+1)x(n+1), extract u=first column,V=remaining,
r=||u||^2,z_j=<u,V_j>/||u||,B=V^H V-z^H z. Actual joint law is Gamma(m+1,rate1)
product standardComplexColumnLaw(n) product complexWishart(rows=m,cols=n).
This must be a law for the ENTIRE B, not only trace/determinant. n and m may be zero; when
m<n residual Wishart is singular but remains a well-defined probability law. No density claim.
The frame for each fixed u is complex-unitary, chosen only inside fixed-fiber proof. The joint
observable is explicitly measurable with division interpreted totally at u=0; u=0 is null
since m+1>0. No jointly measurable selection is claimed. Do not mistake this proof architecture
for a missing measurable QR hypothesis: the exact skew_product signature is supplied.
Check real Gaussian vs CN variance, row-vs-column indexing, mean=0 restriction, u=0 exception,
entire fiber constancy and mutual independence. No candidate density is an assumption.
Fixed-frame existence/invariance and Gamma radial integration are kernel dependencies, only
selected support is supplied, not a full re-review of them. Human review remains required.
'''
snapshot=HERE/'block-review-snapshot'
snapshot.mkdir(exist_ok=True)
bindings={}
for name in ['GaussianMatrixBlockLaw.lean','GaussianBartlettFiber.lean','GaussianBartlettBlockLaw.lean']:
    path=BASE/name
    if (snapshot/name).exists():
        assert (snapshot/name).read_bytes()==path.read_bytes(), 'Do not overwrite a reviewed snapshot'
    else:
        (snapshot/name).write_bytes(path.read_bytes())
    bindings[name]=dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),supplied='Full source')
    prompt+='\nFILE '+name+'\n'+path.read_text(encoding='utf-8')
for name, selected in [('GaussianComplexFrameExists.lean',[(18,57)]),
                       ('GaussianComplexMatrixFrame.lean',[(100,129)])]:
    path=BASE/name
    lines=path.read_text(encoding='utf-8').splitlines()
    bindings[name]=dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),supplied_line_ranges=selected)
    for lo,hi in selected:
        prompt+=f'\nSUPPORT {name} lines{lo}-{hi}\n'+'\n'.join(lines[lo-1:hi])
asset=ROOT/'theory/jin_wishart_formalization/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean'
prompt+='\nLOCKED skew_product lines869-880\n'+'\n'.join(asset.read_text(encoding='utf-8').splitlines()[868:880])
if args.followup:
    prompt+='''\nFOLLOW-UP: your earlier report recommended z_j*conj(z_k) instead of
conj(z_j)*z_k and called the latter critical. Here z is a ROW of normalized inner
products, so the contribution is z^H z, not column z z^H. The supplied proved
complexGram_firstRow_split is exactly that identity. Your assertion that the
existing subtraction becomes addition was incorrect. An exact counterexample
to the recommended change is below. Please explicitly withdraw or defend your
claim using the actual row convention; then report any remaining concrete issue.
Mean0 centrality is explicit in all types/headers, not an unclaimed noncentral
extension. At u=0 complex division returns0, hence z=0 and B=V^H V; this extension
is used only for measurability, and the Gamma norm law proves that u=0 is null.
These conventions are documented in BLOCK_REVIEW_RESOLUTION.md. No source
proof or target was changed in response to the incorrect conjugation suggestion.\n'''
    prompt+=(HERE/'review-conjugation-control.json').read_text(encoding='utf-8')
prefix='p4-block-followup' if args.followup else 'p4-block'
target=HERE/(prefix+'-prompt.txt')
target.write_text(prompt,encoding='utf-8')
(HERE/('block-followup-review-request.json' if args.followup else 'block-review-request.json')).write_text(json.dumps(dict(inputs=bindings,
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
    skew_product_source_sha256=hashlib.sha256(asset.read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print('Prepared full Bartlett-block targets, characters:',len(prompt))
