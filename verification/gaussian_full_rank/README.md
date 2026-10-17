# Actual Gaussian full rank and random-subspace energy milestone

All proof bodies are by Codex. Qoder/Qwen3.8-Max delivered the real bounded,
tools-disabled P4 response recorded here; it did not compile or author these
proofs. This continues user-authorized work and starts no automation.

## Results

- `GaussianGramFullRank`: 9 declarations. For n<=m and **any fixed complex mean**,
  an actual m-by-n CN(0,1) sample has injective column map a.s.; column Gram is
  nonsingular and PD a.s. Real column rank 2n and complement rank 2(m-n) follow.
- `GaussianGramEnergyLaw`: 6 declarations. The actual preceding Gaussian matrix
  law has the full-rank event a.s. The previous abstract energy theorem now
  yields a product law for the entire preceding matrix and two energies,
  without any unproved full-rank or dimension hypothesis. Fresh Gaussian is
  independent and central; previous columns may have any deterministic mean.
- `GaussianGramSupport`: 9 declarations. Row-Gram analogues, actual smaller-side
  Gram PD a.s. for **every rectangular shape**, and noncentral column Wishart
  PD-support probability 1 when n<=m. Zero-size algebraic cases are included;
  energy theorems require 0<n<m for positive Gamma shapes.

`stdGaussian (EuclideanSpace Complex (Fin m))` has real-coordinate variance 1.
Its half squared projected norms have Gamma(n, rate1) and Gamma(m-n, rate1)
laws. Equivalently, divide that fresh complex vector by sqrt2 for CN(0,1).
The source and theorem headers state this convention; no unscaled CN(0,1)
variance claim is made about that stdGaussian itself.

## Reuse and excluded shortcuts

The exact assets were located before writing: `genericComplexGram_map`,
`genericComplexRowGram_map`, both diagonal witnesses and
`sampleEval_ne_zero_ae` in `ComplexGramSimpleSpectrum`. The last theorem
already proves polynomial-null-set transfer under Gaussian translation.
The new determinant polynomial is nonzero by the existing explicit diagonal
witness. No zero-set/Fubini proof, radial integral or measurable QR selection
was repeated. Simple spectrum was **not** treated as implying nonsingularity:
one zero eigenvalue could be simple. No target density is an assumption.

The earlier generic projector/dimension and splitting results are reused.
General actual matrix density, Cholesky Jacobian and joint Bartlett coefficient
law remain OPEN. This closes the actual full-rank/energy premises, not G2 or
the paper's general Theorems1-4.

## Validation

Before proofs, `experiments/gaussian_full_rank_control.py` ran seed20261017,
200000 actual samples for each of four shapes, with independent trace-Gamma
and known logdet moment controls. Wide-matrix zero-eigenvalue control passed.
Observing full rank in samples is not the null-set proof.

Final leaf checks: `full-rank-3.txt`, `energy-law-2.txt`, `support-1.txt`, exit0,
24 declarations printed with only propext/Classical.choice/Quot.sound. Failed
attempts are retained: wrong/ambiguous det-map name, mapMatrix-vs-map rewrite,
then an incorrect instance name and preimage API. Their generated sorryAx
diagnostics do not count as accepted proofs. No source proof placeholders.
All Lean checks used one bounded serial collaborative gate with cached imports;
facade/full Lake build NOT_RUN. Paper and frozen submission archives unchanged.

P4 used the three final target sources and precisely listed inherited support
excerpts. It reported no concrete issue in that scope. It did not re-review
the complete inherited Fubini proof or independently compile. [需人工审查]
Inherited measurability/Fubini/null-set, variance and paper/model correspondence.
Raw prompt, response, usage receipt, source snapshots, dependency/artifact hashes
and the explicit distinction from human review are preserved in audit.json.

Reproduce the fixed-seed script, compile the three leaves in dependency order
via collaborative_check.py with a fresh gate and library, then run audit.py.
Model calls are optional and consume account credits; no credentials are stored.
