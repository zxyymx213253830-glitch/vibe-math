## P4 Adversarial Review: `WidePositiveCoordinate.lean`

**1. Index Coercion Mismatch in `members` (Mathematical Gap)**

The theorem `members` asserts an equivalence between eigenvalue membership for `X : Matrix (Fin m) (Fin n) ℂ` and `Xᴴ`. The LHS existential quantifies over `i` while the RHS quantifies over `j`, but neither index type is explicitly annotated. Given that `complexGram_posSemidef X` produces an `m × m` matrix (indices `Fin m`) while `complexGram_posSemidef Xᴴ` produces an `n × n` matrix (indices `Fin n`), the unannotated existentials rely on implicit coercion or unified indexing. When `m ≠ n`, these are distinct finite types. The proof uses `gram_nonzero_root_mem_iff_conjTranspose` which should handle the rectangular correspondence, but the statement as written obscures whether `i` and `j` range over the correct dimensions. This is not merely cosmetic—if a downstream user instantiates `i : Fin m` on the left and expects `j : Fin m` on the right (rather than `Fin n`), the equivalence is ill-typed or semantically wrong.

**2. Rank Hypothesis Strength in `gram_full_row_rank_coordinate_eq_rowMinimum` (Potential Gap)**

The theorem assumes `hr : X.rank = m` where `X : Matrix (Fin m) (Fin n) ℂ`. This requires `m ≤ n` implicitly (rank cannot exceed min(m,n)), but `hmn : m ≤ n` is **not** an explicit hypothesis of this theorem—it only appears later in `actualWide_fixed_positive_coordinate_ae`. The theorem `gram_full_row_rank_coordinate_eq_rowMinimum` itself has no `m ≤ n` assumption. If `m > n`, then `X.rank = m` is impossible, making the theorem vacuously true but misleading. More critically, `hi : i.val + 1 = m` combined with `i : Fin (Fintype.card (Fin n))` means `i.val < n`, so `m ≤ n` is forced by `hi` alone only if we know such an `i` exists. The existence of `i` satisfying `hi` already encodes `m ≤ n`, but this should be an explicit dimensional hypothesis rather than buried in index arithmetic.

**3. Shifted Measure Transport in `actualWide_fixed_positive_inverse_realMoment_integrable_iff` (API Question, Not a Gap)**

The proof applies `integrable_map_measure` with `measurable_shiftedComplexSampleMatrix M` to transport from the sample space to the matrix law. This requires that pushing forward `stdGaussian (ComplexSample ...)` under `z ↦ complexSampleMatrix z + M` yields `complexGaussianMatrixLaw M` (a shifted Gaussian). This is mathematically standard (translation of Gaussian measure), but the exact signature of `wideRowMinimum_inverse_realMoment_integrable_iff` must accept the noncentral parameter `M`. If the imported theorem only handles `M = 0`, this is a semantic mismatch. However, given the theorem name includes "wide" and the source treats `M` as arbitrary fixed shift, this is likely fine—flagging only as a verification checkpoint, not a defect.

**4. Strict Inequality Boundary in Integrability Threshold (Minor)**

The integrability iff states `p < ((n - m + 1 : ℕ) : ℝ)`. The complementary lintegral-eq-top theorem uses `((n - m + 1 : ℕ) : ℝ) ≤ p`. These partition `(0, ∞)` correctly with no gap at the boundary. No issue here; included only to confirm the dichotomy is exhaustive given `hp : 0 < p`.

**Summary:** Item 1 (index type ambiguity in `members`) and Item 2 (missing explicit `m ≤ n` hypothesis, relying on index inhabitability) are actual structural concerns. Items 3–4 are not defects.
