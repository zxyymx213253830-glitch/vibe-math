# Canonical Fin coordinate transport

The three public theorems in `CanonicalFinGramTransport.lean` preserve the column Gram matrix under the fixed Sum row isometry, give a unit determinant for the Fin representation of the bijective column map, and compare the fixed smallest positive coordinate before and after that map. The bounds theorem explicitly assumes both dimensions positive, rank X = min(m,n), and i.val+1 = min(m,n). In the wide case i=m-1, not the final structural zero coordinate.

Writing F=T.submatrix id e.symm and C(F)=max(1, squared Euclidean operator norm of F), the two factors are max(C(F),C(F^H)) and max(C(F inverse),C((F^H) inverse)). They are finite bounds, not reciprocal constants. The row isometry preserves Gram exactly; the column map need not be isometric. This is deterministic full-small-side-rank transport, not a general singular inverse-moment theorem.

Evidence: seed 2026102228, 27 cases and 233 exact/calibrated numerical controls, including zero dimensions, determinant one conventions, complex isometries, Fin permutations, and positive-coordinate bounds. Controls are not proofs. Final source v2 and three independently stated literal target types passed the shared serial Lean gate with the standard three axioms. Failed source v1 and its diagnostics remain archived; it is not accepted.

## Qoder P4 resolution

The real Qwen3.8-Max response reviewed the full final source, with tools disabled. Its index concern is resolved by the explicit full-rank and i.val+1 hypotheses and the imported proved full-column/full-row positive-coordinate theorems. An array of n column-Gram eigenvalues correctly uses i=m-1 in the wide case. No additional random selector is assumed.

The sorting concern is explicitly classified by the reviewer as not a mathematical gap. The private equality lemma compares identical Hermitian matrices; proof irrelevance identifies their Hermitian proofs. It does not infer ordered-array equality merely from common spectrum.

The concern about a column-norm proxy is resolved by the actual imported definition: matrixColumnControl is max(1, squared Euclidean operator norm). The spectral inequalities are already proved dependencies; this source only enlarges their positive factors using max and nonnegative eigenvalues. The first two theorems do not assume positive dimensions; the bounds theorem needs nonzero smallest-positive coordinates. The determinant proof was recognized as valid; its explicit WithLp conversion connects raw mulVec functions with EuclideanSpace vectors.

P4 is a scoped different-family review, not blanket approval, human review, or independent compilation. [需人工审查] Subsequent model/measure/Fubini/limit/inverse-integrability transport. General singular B inverse-moment threshold remains OPEN. Frozen publication artifacts are unchanged; full Lake/mathlib build and Linux independent kernel are NOT_RUN.
