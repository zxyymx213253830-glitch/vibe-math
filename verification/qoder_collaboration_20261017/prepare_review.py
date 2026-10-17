"""Bind the precise supplied source snapshot for the cross-family review."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
names = ['GaussianGramDimensions.lean', 'GaussianGramProjector.lean',
         'GaussianRandomSubspaceLaw.lean']
parser = argparse.ArgumentParser()
parser.add_argument('--name', default='p4')
parser.add_argument('--clarify', action='store_true')
args = parser.parse_args()
prompt = '''You are a strict independent reviewer from a model family different from the Codex proof author.
P4: Report only concrete issues, do NOT rewrite proofs. For each issue identify
(a) undeclared measurability, Fubini, independence, dimensions or variance assumptions;
(b) unsupported steps needing lemmas; (c) mismatch between statement and proof.
Target is GaussianGramDimensions.lean; the other two files are supporting interfaces.
No tools: you cannot independently compile. Source header correctly leaves Gaussian a.e.
full rank and general Wishart density OPEN. Do not criticize these as if claimed proved.
Pay attention to n=0, n=m, impossible n>m under Gram nonsingularity, real/complex rank
doubling, the singular patched-zero space, and half-real-norm variance convention.
If no concrete issue is found, say so scoped to supplied source. At most 500 words.
This model review does not replace human review. Do not restate the whole proof.
'''
if args.clarify:
    prompt += '''\nFollow-up to your initial reviews: Lean rejected BOTH the ite_eq_left
and if_pos simplifications at totalGramColumnSpaceReal_finrank. Your claims that
these targets matched or that if_pos fixed it were not reliable. The supplied
FINAL source proves equality hK between submodules by split_ifs, then transports
the dimension through congrArg before applying the real rank lemma.
Do not claim to have independently compiled the code.
Also n<=m is a CONSEQUENCE of hA, not a missing assumption. The orthogonal dimension
proof has only hA and obtains the bound from nonnegative dimension plus its sum
identity, not from hnm. Positivity n>0 and n<m are intentional only in the probability
interface because Gamma shape parameters must be positive. Please distinguish
actual bugs from these deliberate domain differences. Report remaining concrete
issues only. If none, say none found in supplied source, with no human-review claim.\n'''
    prompt += '\nActual latest Lean log (local coordinator received exit code 0):\n' + (
        HERE/'gram-dimensions-4.txt').read_text(encoding='utf-8')
inputs = {}
snapshot = HERE/(args.name+'-snapshot')
snapshot.mkdir(exist_ok=True)
for name in names:
    path = BASE/name
    inputs[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    (snapshot/name).write_bytes(path.read_bytes())
    prompt += '\n\nFILE '+name+'\n'+path.read_text(encoding='utf-8')
target = HERE/(args.name+'-prompt.txt')
target.write_text(prompt, encoding='utf-8')
(HERE/(args.name+'-request.json')).write_text(json.dumps(dict(inputs=inputs,
    prompt_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
    author='Codex', reviewer_requested='Qoder Qwen3.8-Max',
    scope='Target dimension module plus two supplied support modules; no independent compilation'),
    indent=2)+'\n', encoding='utf-8')
print('Prepared 3-source review snapshot; characters:', len(prompt))
