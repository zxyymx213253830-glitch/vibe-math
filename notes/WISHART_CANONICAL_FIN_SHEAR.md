# Fin canonical shear bounds

Three deterministic public theorems in `CanonicalFinShear.lean` transfer the explicit block shear through any fixed equivalence e:Sum(Fin b,Fin c)~Fin n. They prove both inverse products and Sminus inverse=Splus, bound both Euclidean operator norms by 1+||K||op, and bound C(Sminus),C(Sminus inverse) by (1+||K||op)^2. Here C=max(1,squared Euclidean operator norm), as defined in GramMinimumColumnComparison. Empty dimensions are included; the zero-dimensional identity operator has norm zero, while C still equals one.

This closes the finite-coordinate polynomial shear-factor bound. It does not yet prove integrability of a random factor or a general singular inverse-moment threshold. The explicit K is supplied; no inverse N is silently totalized.

Evidence: seed2026102229, 20 cases/203 coupled inverse, Fin permutation, determinant and norm controls, calibrated against the exact scalar shear squared norm (2+t^2+t*sqrt(t^2+4))/2, including t=100 and empty dimensions. These are controls, not proofs. Final source v2 and three literal target types passed the shared serial Lean gate with the standard three axioms. Source v1 failed at the explicit inverse-coordinate conversion and remains archived with its failed log; it is not accepted.

## Qoder P4 resolution

The real final-source Qwen3.8-Max response reports no hard mathematical errors. Its dimension question is already witnessed by the supplied equivalence e; Fintype.card_congr yields b+c=n whenever a consumer needs that equation. Adding an independent coherence assumption would be redundant. The private norm lemma only claims an upper bound, exactly what downstream polynomial control needs; norm equality is not claimed or required.

The imported C definition is the exact max(1,Euclidean operator norm squared), not a columnwise proxy. The proof reduces this definition and applies max_le; no missing geometric inequality is assumed. The [需人工审查] comment explicitly refers to subsequent work, not a claim that integration occurs in this file. Empty cases are included in both the universal theorem types and the 203 controls. Pinned source/dependency hashes prevent the speculative future API changes from silently changing this result; such changes would require rechecking.

Scoped P4 is not human review or independent compilation. [需人工审查] Actual random-factor moments, Holder/Tonelli/Fubini and the final model/threshold interpretation remain required. General singular B inverse-moment threshold remains OPEN. Frozen publication artifacts unchanged; full Lake/mathlib and Linux independent kernel NOT_RUN.
