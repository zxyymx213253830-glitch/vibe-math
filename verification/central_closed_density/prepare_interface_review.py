"""Snapshot exact passed normalization, scale, matrix, and memoryless interfaces."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT/'theory/jin_wishart_formalization/JinWishartFormalization'
OUT = Path(__file__).resolve().parent
context = '''P4: skeptical semantic review, only concrete problems, <=750 words, no rewrites or tools. Proof author Codex, you are different family Qwen. Four exact full passed Lean sources below, all standard propext/Classical.choice/Quot.sound. Prior checked dependencies: ACTUAL CN variance-one t=d+n rows/n columns Wishart has canonical n²-real coordinate density rho=K(d,n)*det(Hq)^d*exp(-traceHq) on PD and zero outside. K is product pi^-j/(d+j)!; mass1 derived from actual law. H/R inverse on Hermitian matrices, both continuous; coordinate measure Hn is nested Pi Lebesgue, not Frobenius volume. New normalization converts K to pi^-choose(n,2)/factorial-product and Gamma-product. New minimum dependency already checked: for EVERY n>0 actual central n-by-n Gram least eigenvalue Exp(rate n), tail exp(-nx) for x>=0 and full CDF, no assumed spectral joint density. New scaling must concern ACTUAL scaled sample a*z, complex variance a² and covariance vI => rate n/v. n>0, a>0,v>0 explicit. Generic spectral threshold equivalence (A-xI).PD iff x<lambda_min(A) is available for Hermitian A, n>0; multiplication by positive c is handled via this criterion, no ordered-eigenvalue permutation assumption. Matrix-density interface defines ambient reference as Hn.map H supported on Hermitian matrices, NOT restriction of ambient complex Lebesgue; actual W is recovered by H(RW)=W a.e. New stronger square matrix memorylessness: restricting actual coordinate law to W>xI and mapping W->W-xI gives exp(-nx) times the full same law, x>=0. Dividing by that positive finite event mass gives conditional law; unnormalized and normalized statements distinct. Whole COMPLEX-matrix residual identity is also proved. At n=0 only trivial matrix/cone identities, not minimum law. Positive-cone density shift uses canonical translation preserving Haar measure; restrictions correctly retained before subtraction. No target density/probability premise. Imported centralConeWeight_square_shift is trace exponential factorization; actual support/normalization from density already reviewed. Fubini/volume/variance/model mapping [需人工审查] remains. Review rates, matrix-vs-coordinate measures, inverse mass, restrictions, dimension-zero and theorem strength. General noncentral G2 and paper T1-4 not closed. Not independent compilation/human review.
'''
snapshot = OUT/'interface-review-snapshot'
snapshot.mkdir(exist_ok=True)
inputs = {}
pieces = [context]
for name in ['CentralWishartNormalization.lean', 'CentralWishartScaledMinimum.lean',
             'CentralWishartMatrixDensity.lean', 'CentralWishartConeMemoryless.lean']:
    raw = (SRC/name).read_bytes()
    (snapshot/name).write_bytes(raw)
    inputs[name] = {'sha256': hashlib.sha256(raw).hexdigest(), 'supplied': 'Full source'}
    pieces.append('\nFULL SOURCE '+name+'\n'+raw.decode('utf-8'))
prompt = OUT/'p4-interface-prompt.txt'
prompt.write_text('\n'.join(pieces), encoding='utf-8')
(OUT/'interface-review-request.json').write_text(json.dumps(dict(inputs=inputs,
    prompt_sha256=hashlib.sha256(prompt.read_bytes()).hexdigest()), indent=2)+'\n', encoding='utf-8')
print('Prompt characters:', len(prompt.read_text(encoding='utf-8')))
