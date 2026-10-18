"""Bind a final source snapshot for a bounded cross-family P4 review."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
prompt = '''P4 semantic/math review. Proof author Codex; you are a different model family.
Report concrete problems only (max650 words); no rewrites, no tools or independent compile.
All 12 printed declarations in the FOUR FULL target files below passed Lean, standard
propext/Classical.choice/Quot.sound only. Main new claim: actual CENTRAL complex CN(0,1)
t-by-s Gram (t>=s) determinant has the law of a product of independent
Gamma(t-s+1,rate1),...,Gamma(t,rate1). A prior checked actual Bartlett block law is
supplied as support, NOT assumed from a candidate density. Reconstruction is pointwise,
including u=0; determinant factorization needs r>0, then is transported a.e. using the
actual norm law. n=0 means empty residual matrix det=1, not det=0. Singular wide
residuals are allowed in block/determinant recursion; product theorem uses d+n rows.
z is a ROW of inner products (inner conjugate-linear in FIRST argument). Thus the
rank-one contribution has entry conj(z_j)*z_k. At u=0, z=0 by total division and
B=V^H V. Pi product input variables are real, output embeds their product in complex.
Check indexing, null sets, product-map orientation, Gamma shape/rate, dimensions,
stronger statement vs actual proof, and whether the finite-product law really follows
from actual samples. Human review of measure/variance/model interpretation remains
required. This is not a matrix/spectral density or a general-paper-Theorems1-4 claim.
Do not report hypothetical conventions absent from this code as actual errors.
Earlier full-fiber and frame audit is a dependency, not a full re-review here.
'''
bindings = {}
snapshot = HERE/'review-snapshot'
snapshot.mkdir(exist_ok=True)
names = ['GaussianBartlettGramRecursion.lean', 'GaussianBartlettGramDeterminant.lean',
         'GaussianBartlettDeterminantLaw.lean', 'CentralWishartDeterminantProduct.lean']
for name in names:
    path = BASE/name
    dest = snapshot/name
    if dest.exists():
        assert dest.read_bytes() == path.read_bytes(), 'Never overwrite a different reviewed snapshot'
    else:
        dest.write_bytes(path.read_bytes())
    bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), supplied='Full source')
    prompt += '\nFULL TARGET '+name+'\n'+path.read_text(encoding='utf-8')
for name, start, end in [('GaussianBartlettBlockLaw.lean', 18, 88),
                         ('GaussianBartlettFiber.lean', 18, 29),
                         ('CentralWishartBlockStep.lean', 17, 65)]:
    path = BASE/name
    bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                          supplied_line_ranges=[[start, end]])
    prompt += f'\nSUPPORT {name} lines{start}-{end}\n'+'\n'.join(
        path.read_text(encoding='utf-8').splitlines()[start-1:end])
gamma = ROOT/'theory/jin_wishart_formalization/.lake/packages/mathlib/Mathlib/Probability/Distributions/Gamma.lean'
prompt += '\nLOCKED GAMMA DEFINITION\n'+'\n'.join(gamma.read_text(encoding='utf-8').splitlines()[39:49])
target = HERE/'p4-prompt.txt'
target.write_text(prompt, encoding='utf-8')
(HERE/'review-request.json').write_text(json.dumps(dict(inputs=bindings,
    gamma_source_sha256=hashlib.sha256(gamma.read_bytes()).hexdigest(),
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print('Prepared byte-exact source review:', len(prompt), 'characters')
