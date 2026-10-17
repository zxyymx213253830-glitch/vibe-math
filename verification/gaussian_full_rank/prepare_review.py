"""Freeze the exact final sources and selected supporting asset lines."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
prompt = '''P4 independent cross-family review. You are the strict reviewer, Codex wrote these proofs.
Report ONLY concrete problems: undeclared assumptions, unsupported steps, or statement/proof mismatches.
Do not rewrite proofs. Do not assert compilation verification; tools are disabled.
All three targets have already locally compiled with only the three standard Lean axioms.
Check arbitrary fixed complex means, n=0, n=m and both Gram orientations. The new energy law
uses an ACTUAL preceding CN(0,1) matrix and independent stdGaussian on complex column space:
the latter has real coordinate variance 1, so dividing norm squared by 2 gives CN(0,1) energies.
There is NO new general Wishart density or Bartlett coefficient/joint-matrix law claimed.
Gaussian a.e. full rank is now to be established by a NONZERO determinant polynomial, not merely
simple spectrum or assuming target density. Existing sampleEval_ne_zero_ae is a reused kernel theorem;
its underlying Fubini/absolute-continuity proof is NOT fully supplied for re-review here.
Distinguish an intentional domain restriction from a missing hypothesis. At most 500 words.
If no concrete issue, say so scoped to supplied sources. Model review is not human review.
'''
bindings = {}
snapshot = HERE/'review-snapshot'
snapshot.mkdir(exist_ok=True)
for name in ['GaussianGramFullRank.lean', 'GaussianGramEnergyLaw.lean', 'GaussianGramSupport.lean']:
    path = BASE/name
    data = path.read_bytes()
    (snapshot/name).write_bytes(data)
    bindings[name] = dict(sha256=hashlib.sha256(data).hexdigest(), supplied='Full source')
    prompt += '\n\nFILE '+name+'\n'+data.decode('utf-8')
path = BASE/'ComplexGramSimpleSpectrum.lean'
lines = path.read_text(encoding='utf-8').splitlines()
selected = [(180, 184), (211, 263), (313, 347), (428, 440), (461, 482), (505, 536)]
for lo, hi in selected:
    prompt += f'\n\nEXACT SUPPORT ComplexGramSimpleSpectrum.lean lines {lo}-{hi}\n'
    prompt += '\n'.join(lines[lo-1:hi])
bindings[path.name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
    supplied_line_ranges=selected, caveat='Full inherited Fubini proof not supplied')
target = HERE/'p4-prompt.txt'
target.write_text(prompt, encoding='utf-8')
(HERE/'review-request.json').write_text(json.dumps(dict(inputs=bindings,
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
    proof_author='Codex', reviewer_requested='Qoder Qwen3.8-Max', independent_compilation=False),
    indent=2)+'\n', encoding='utf-8')
print('Prepared final 3-target review, characters:', len(prompt))
