"""Final append-law snapshot and exact supporting excerpts for P4."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
prompt = '''P4: You are the strict cross-family reviewer; Codex authored the supplied target.
Report only concrete undeclared assumptions, unsupported steps and statement/proof mismatches.
Do not rewrite proofs. No tools or independent compilation. Latest target has 10 declarations
checked by Lean with only propext/Classical.choice/Quot.sound. This is evidence, not your check.
Target GaussianColumnAppendLaw transports the actual n+1-column Gaussian sample to preceding
columns and a fresh complex column. Check index equivalence, first column 0 vs remaining succ,
the real Gaussian vs CN(0,1) sqrt2 factor, independence and gamma shapes n and m-n.
No global measurable QR, general density or full Bartlett coefficient law is claimed.
The inherited energy theorem and Gaussian full rank are kernel dependencies; their full
measure-theoretic proofs are not being re-reviewed here. State the supplied scope honestly.
At most 400 words. If no concrete problem, say so. Model review does not replace human review.
'''
snapshot = HERE/'review-snapshot'
snapshot.mkdir(exist_ok=True)
bindings = {}
for name in ['GaussianColumnAppendLaw.lean', 'GaussianGramEnergyLaw.lean']:
    path = BASE/name
    (snapshot/name).write_bytes(path.read_bytes())
    bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), supplied='Full source')
    prompt += '\nFILE '+name+'\n'+path.read_text(encoding='utf-8')
for name, selected in [('GaussianTwoColumnIntegration.lean', [(15, 39)]),
                       ('GaussianComplexColumnFrame.lean', [(19, 34)]),
                       ('GaussianGramDimensions.lean', [(77, 90)])]:
    path = BASE/name
    lines = path.read_text(encoding='utf-8').splitlines()
    bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), supplied_line_ranges=selected)
    for lo, hi in selected:
        prompt += f'\nSUPPORT {name} lines {lo}-{hi}\n'+'\n'.join(lines[lo-1:hi])
target = HERE/'p4-prompt.txt'
target.write_text(prompt, encoding='utf-8')
(HERE/'review-request.json').write_text(json.dumps(dict(inputs=bindings,
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
print('Prepared append-law P4 snapshot; characters:', len(prompt))
