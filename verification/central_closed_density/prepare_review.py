"""Snapshot exact passed sources for one bounded cross-family semantic review."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
OUT = Path(__file__).resolve().parent
FILES = ['CentralWishartDensityAlgebra.lean', 'CentralBartlettDensityTransport.lean',
         'CentralWishartClosedDensity.lean']
context = '''P4: You are a skeptical mathematical referee, from a different family than the Codex proof author. Report concrete issues only, no rewrites, <=800 words. These exact three full sources passed the locked Lean kernel with only propext/Classical.choice/Quot.sound. No independent compilation by you. Review whether the actual CENTRAL CN(0,1) t-by-s Gram density is derived, not assumed; dimensions, normalization, restrictions, zero-dimensional base, product independence, variance. Target is all t>=s with row surplus d=t-s, canonical s^2 real coordinate volume (diagonal real, upper real, transposed upper imaginary), NOT Frobenius volume. K(d,s) is the displayed finite factorial product. At s=0 the coordinate measure is mass one on empty matrix; PD is vacuous and determinant one. z is a complex ROW, contribution conj(zi)*zj. Source joint law Gamma(d+n+1,rate1) x CN(n) x actual lower Wishart(d+n,n) is already checked as an entire matrix-block product law. Actual CN density is pi^-n exp(-norm²). The general weighted chart volume theorem already checked states (raw positive-r mixed volume withDensity r^n).map chart = canonical output volume restricted q00>0; proof is nonnegative Tonelli and fixed-fiber scaling, no target density premise. The chart is hermitianBlockCoordinateEquiv.symm composed with (r,z,Q)->(r,sqrt(r)z,Q+realcoords(z^H z)); the splitting equivalence preserves canonical coordinate volume exactly. H and R are inverse on Hermitian matrices; no ambient 2s² volume restriction. PD chart iff residual PD when r>0, det=r detB. Degree d is fixed across induction, row number d+n. Source density at r>0 is algebraically r^n times output density; actual Gamma has zero nonpositive mass. Actual recursion uses a.e. Hermitian residual and explicit joint map, not a random QR independence assumption. Review only supplied sources plus these precise dependency signatures. General noncentral density, spectral Jacobian, paper T1-4, and human semantic review are NOT claimed. Measure/variance/model interpretation remains [需人工审查].
'''
snapshot = OUT/'review-snapshot'
snapshot.mkdir(exist_ok=True)
inputs = {}
pieces = [context]
for name in FILES:
    raw = (SRC/name).read_bytes()
    (snapshot/name).write_bytes(raw)
    inputs[name] = {'sha256': hashlib.sha256(raw).hexdigest(), 'supplied': 'Full source'}
    pieces.append('\nFULL SOURCE '+name+'\n'+raw.decode('utf-8'))
prompt = OUT/'p4-prompt.txt'
prompt.write_text('\n'.join(pieces), encoding='utf-8')
(OUT/'review-request.json').write_text(json.dumps(dict(inputs=inputs,
    prompt_sha256=hashlib.sha256(prompt.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
print('Prompt characters:', len(prompt.read_text(encoding='utf-8')))
