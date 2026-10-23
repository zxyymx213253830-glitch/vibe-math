# P4 Adversarial Review

## Source 1: `RectangularFullColumnFrame.lean`

**Mathematical gap (index coercion):** The hypothesis `hB : B.rank = n` implicitly requires `n ≤ p` for a `Matrix (Fin p) (Fin n) ℂ`, since rank cannot exceed the minimum dimension. This is never stated as an explicit assumption. If `n > p`, the premise is vacuously false and the theorem holds trivially, but the downstream source treats this as producing a concrete factorization with `IsUnit S.det`. A vacuous proof here would propagate a logically valid but semantically empty result into Source 2's measure-theoretic construction.

**API question:** The zero-row padding `(0 : Matrix (Fin 0) (Fin n) ℂ)` used in `hjoint` relies on `exists_joint_kernel_canonical_matrix` accepting a degenerate `Fin 0` row index. If that upstream lemma has an unstated positivity requirement on the second matrix's row count, this instantiation fails.

## Source 2: `RectangularFactorInverseCriterion.lean`

**Mathematical gap (measure space mismatch):** The sample space is `ComplexSample (m := m) (n := p)`, so `z` produces `m × p` matrices. After right-multiplication by `U : Matrix (Fin p) (Fin n) ℂ`, the product `complexSampleMatrix z * U` is `m × n`. However, `iidCriterion` is invoked with parameter `(m := m) (n := p)` on line 38, then the criterion's internal `actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff` and `actualWide_fixed_positive_inverse_realMoment_integrable_iff` are called with shape parameters `m n`. The eigenvalue index `i : Fin (Fintype.card (Fin n))` targets an `n × n` Gram matrix, but the `iidCriterion` statement passes `M*S : Matrix (Fin m) (Fin n) ℂ` while referencing `ComplexSample (m := m) (n := p)` in the outer measure. The equivalence between integrability over the `p`-column sample and the `n`-column canonical law via the isometry `Uᴴ*U=1` is asserted through `complexGaussianMatrixLaw_right_isometric_projection`, but the dimensional reduction from `p` to `n` in the sample space is not explicitly justified—this is the core transport step and it depends on `U` being a genuine isometric embedding of column spaces, which holds only if the factorization from Source 1 is non-vacuous.

**Mathematical gap (rank AE claim):** `hrank := actualCorrelatedRank_eq_generic_ae B M` is applied after rewriting through `matrix_fromRows_rank_eq B M` and `hstack`. The `hstack` proof uses `omega` on `hu := (Matrix.fromRows B M).rank_le_card_width`, but `fromRows B M` has shape `(p + m) × n`. The bound gives `rank ≤ n`, and combined with `hstack : rank = n` this is consistent. However, the AE rank equality `actualCorrelatedRank_eq_generic_ae` must hold μ-a.e. on the `m × p` sample space, not the `m × n` reduced space. The filter `hrank` is later used inside `hAE` at points `z : ComplexSample (m := m) (n := p)`, so its ambient measure must match. This is plausible but unstated.

**API question:** `matrixColumnControl_pos S` requires `S` invertible, which follows from `IsUnit S.det`. No issue if Source 1 is non-vacuous.

**Summary:** The critical dependency is Source 1's non-vacuity under implicit `n ≤ p`.
