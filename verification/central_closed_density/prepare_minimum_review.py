"""Exact final-source snapshot for the general square minimum law P4."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
OUT = Path(__file__).resolve().parent
context = '''P4 semantic review. Only report concrete problems, no rewriting, <=750 words. Codex proof author, you are a different model family. These full sources passed locked Lean kernel with only standard propext/Classical.choice/Quot.sound. You have no tools/independent compilation. Claim: actual central variance-one complex square n-by-n Gram minimum has Exp(rate n) law for every n>0, not just 2x2. Actual rectangular t=d+n>=n cone-tail probability retains det(V+xI)^d under the integral. Closed actual density was just independently reviewed; its source is supplied fully. Canonical real n² coordinates, not Frobenius volume. Existing checked centralCone_candidateIntegral_shift uses translation q->q+xI on canonical volume, H(q+xI)=Hq+xI, trace shift n*x and Haar invariance; it does NOT assume actual density. Existing hermitian_shift_posDef_iff_smallest is deterministic spectral theorem: (A-xI).PosDef iff x<least descending eigenvalue, for any Hermitian A and n>0. complexNoncentralSampleSmallestEigenvalue 0 hn is the smallest eigenvalue of the ACTUAL variance-one sample Gram; it is measurable, pointwise nonnegative, and has the same descending index. The imported actual density chain derives product source from actual full Bartlett joint law. No desired probability formula is an assumption. n=0 is allowed for cone integrals but excluded for the minimum exponential law. x>=0 in strict-tail formula; all-real CDF includes negative-zero branch; CDF uniqueness identifies expMeasure rate n. Density positive-cone mass derives from actual normalization. For x>=0 shifted PD cone is contained in original PD cone by adding xI PSD. Review dimensions, equality vs strict events, reference volume, exponential rate, normalization, and any circularity. Human review remains [需人工审查]. Paper general T1-4 and noncentral G2 NOT claimed. The previous P4 misexplained leading Bartlett degrees: leading norm shape equals full row count d+n+1, residual has d+n rows; source proof is correct.
'''
snapshot = OUT/'minimum-review-snapshot'
snapshot.mkdir(exist_ok=True)
inputs = {}
pieces = [context]
for name in ['CentralWishartClosedDensity.lean', 'CentralWishartMinimum.lean']:
    raw = (SRC/name).read_bytes()
    (snapshot/name).write_bytes(raw)
    inputs[name] = {'sha256': hashlib.sha256(raw).hexdigest(), 'supplied': 'Full source'}
    pieces.append('\nFULL SOURCE '+name+'\n'+raw.decode('utf-8'))
prompt = OUT/'p4-minimum-prompt.txt'
prompt.write_text('\n'.join(pieces), encoding='utf-8')
(OUT/'minimum-review-request.json').write_text(json.dumps(dict(inputs=inputs,
    prompt_sha256=hashlib.sha256(prompt.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
print('Prompt characters:', len(prompt.read_text(encoding='utf-8')))
