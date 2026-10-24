# Ordered 2x2 eigenpair from trace coordinates — 2026-10-24

Codex proved two statements in `TwoByTwoOrderedEigenpair.lean`, final v4 exit0 with standard3axioms. The final-source Qoder Qwen3.8-Max P4 and two independent literal types are bound by `two-ordered`. Reuse seed2026102405's already accepted 322 controls (not rerun or recounted as new); signed Hermitian coordinates, norm radius and ordered eigenpair were checked before source. Failed v1/v2/v3 and compiler logs remain unaccepted.

For EVERY Hermitian 2x2 complex matrix A, including indefinite and repeated-root cases, descending eigenvalues0 are (Re A00+Re A11)/2 plus/minus the Euclidean norm of ((Re A00-Re A11)/2, Re A01, Im A01). The actual central Gaussian sample's existing `centralTwoByTwoEigenpair` equals this coordinate expression pointwise, for every original sample, not merely almost everywhere. No joint density, positivity, distinctness or independence is assumed or proved here.

## P4 adjudication

1. There is no missing permutation argument. Pinned `Matrix.IsHermitian.eigenvalues` is DEFINED as `eigenvalues₀` composed with the inverse of the literal cardinality equivalence e. The `Equiv.sum_comp`/`prod_comp` calculations use this exact definition. Equality of sum and product, together with the proved descending order, uniquely determines the two real roots. The squared-gap identity is explicitly proved from the squared sum, product and radius identity; nonnegative gap/radius select its sign using `sq_eq_sq₀`. The reviewer itself calls this part logically sound. No assumption about the enumeration being sorted is used.
2. The inherited signature is exactly `hermitian_twoRow_det_re (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) : A.det.re=(A 0 0).re*(A 1 1).re-(A 0 1).re^2-(A 0 1).im^2`. No PSD/sign hypothesis. Its complete checked proof explicitly derives BOTH diagonal imaginary parts zero from hA before expanding determinant. Thus the alleged representation gap in point4 is also already discharged by an exact dependency, not an ambient type assertion.
3. The smallest index is proved equal to1 for size2, and descending order is explicitly supplied by `eigenvalues₀_antitone`. Both definitions and imported sources are pinned in transitive hashes; a changed ordering cannot silently pass the immutable bundle.
5. The reviewer agrees no probability-model mismatch or joint-law overclaim occurs.

[需人工审查] Spectral ordering, coordinate convention and subsequent paper mapping. P4 is not human/independent kernel verification. R3 radial reduction and actual trace density are separately accepted; their full ordered joint measure assembly remains OPEN. FullLake/Linux independent kernel NOT_RUN, frozen publication artifacts unchanged.
