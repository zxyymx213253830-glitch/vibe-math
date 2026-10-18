"""Supply exact variance/normalization dependencies omitted from interface P4."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
OUT = Path(__file__).resolve().parent
context = '''P4 follow-up: report remaining concrete issues only, <=400 words, no rewritten proofs or tools. Previous scoped interface review raised potential factor-two complex variance because actual sample definition was omitted. Here is exact previously checked dependency context. complexSampleMatrix maps real stdGaussian coordinates to (real+i*imag)/sqrt(2). Thus each real/imaginary ENTRY component has variance1/2, complex squared-norm mean1. Scaling source by sqrt(v) yields complex variance v, not 2v. Full actual CN density source below proves pi^-n exp(-norm²) from half-variance real Gaussian density, no convention assumed merely from a name. Bartlett leading energy shape equals full row count, rate1; already checked actual minimum Exp(n) for variance-one samples. Explicit finite product K, mass1, and factorial/Gamma conversion are checked, not a normalization assumption. Prior review's Frobenius factor '2^(n(n-1)/4) or similar' is inaccurate for VOLUME: every complex offdiagonal pair has two axes scaled sqrt2, giving volume2 per pair =>2^(n(n-1)/2). Current density deliberately uses canonical coordinate volume, not Frobenius. Does this exact additional context leave any actual source error on the claimed rate n/v? No need to endorse the whole dependency graph. Human review remains required. Do not treat this as independent compilation.
'''
pieces, inputs = [context], {}
for name, ranges in [('WishartProbability.lean', [(19, 28)]),
                     ('GaussianMatrixBlockLaw.lean', [(18, 24)])]:
    raw = (SRC/name).read_bytes()
    lines = raw.decode('utf-8').splitlines()
    inputs[name] = {'sha256': hashlib.sha256(raw).hexdigest(), 'supplied_line_ranges': ranges}
    for first, last in ranges:
        pieces.append(f'\nEXACT {name} lines {first}-{last}\n'+'\n'.join(lines[first-1:last]))
snapshot = OUT/'variance-review-snapshot'
snapshot.mkdir(exist_ok=True)
for name in ['GaussianComplexColumnDensity.lean', 'CentralWishartNormalization.lean']:
    raw = (SRC/name).read_bytes()
    inputs[name] = {'sha256': hashlib.sha256(raw).hexdigest(), 'supplied': 'Full source'}
    (snapshot/name).write_bytes(raw)
    pieces.append('\nFULL SOURCE '+name+'\n'+raw.decode('utf-8'))
prompt = OUT/'p4-variance-prompt.txt'
prompt.write_text('\n'.join(pieces), encoding='utf-8')
(OUT/'variance-review-request.json').write_text(json.dumps(dict(inputs=inputs,
    prompt_sha256=hashlib.sha256(prompt.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
