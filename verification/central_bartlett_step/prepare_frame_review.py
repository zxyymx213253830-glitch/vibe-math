"""Bind the two checked frame targets for a limited cross-family review."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
prompt = '''P4 issues-only review, Codex authored these proofs; you are Qwen, another family.
Review the exact two new source files. Both have already passed local Lean standard-axiom checks,
4 + 8 statements. You do not independently compile. Check complex vs real linearity, all columns,
sqrt2 convention, direction of coordinate curry, and full actual matrix law vs scalar energy law.
The existential frame is fixed separately for each nonzero vector; NO measurable global choice
is claimed. The future fixed-fiber Bartlett matrix law is explicitly OPEN. Full matrix density
and G2 are not claimed. Do not call the absence of a global selector a bug in this target.
Report only concrete issues, max350 words. If none, state supplied scope and human-review limit.
'''
snapshot = HERE/'frame-review-snapshot'
snapshot.mkdir(exist_ok=True)
bindings = {}
for name in ['GaussianComplexFrameExists.lean', 'GaussianComplexMatrixFrame.lean']:
    path = BASE/name
    (snapshot/name).write_bytes(path.read_bytes())
    bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), supplied='Full source')
    prompt += '\nFILE '+name+'\n'+path.read_text(encoding='utf-8')
name = 'GaussianComplexColumnFrame.lean'
path = BASE/name
prompt += '\nSUPPORT '+name+' lines1-79\n'+'\n'.join(path.read_text(encoding='utf-8').splitlines()[:79])
bindings[name] = dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), supplied_lines=[1,79])
target = HERE/'p4-frame-prompt.txt'
target.write_text(prompt, encoding='utf-8')
(HERE/'frame-review-request.json').write_text(json.dumps(dict(inputs=bindings,
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
print('Prepared two checked frame sources, characters:',len(prompt))
