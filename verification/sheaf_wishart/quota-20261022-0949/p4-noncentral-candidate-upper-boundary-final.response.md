## P4 Adversarial Review: `OriginalNoncentralCandidateUpperBoundary.lean`

**1. Missing Nonnegativity Hypothesis on Eigenvalues (`lambda`)**

In `natural_nuttall_tail`, the term `Real.sqrt (2*lambda ⟨j.val,hj⟩)` requires its argument to be nonnegative for the square root to behave as expected in asymptotic analysis. The theorem signature assumes only `(lambda : Fin L → ℝ)` with no constraint `0 ≤ lambda j`. If any `lambda j < 0`, then `2 * lambda j < 0`, making `Real.sqrt` return `0` constantly for those negative values rather than diverging to `atTop`. The composition `.comp hb` where `hb : Tendsto (fun x => Real.sqrt (2*x)) atTop atTop` implicitly treats `lambda j` as a fixed parameter scaling `x`, but the written code passes `Real.sqrt (2*lambda ⟨j.val,hj⟩)` as a **constant** to `nuttallQ`. A constant does not tend to `atTop`; the composition logic is semantically broken unless `lambda` is intended to scale with `x`, which contradicts the signature.

**2. Type Mismatch / Coercion Gap in Constant Multiplication**

In the first branch of `theorem1PsiMatrix_tendsto_zero`:
```lean
((natural_nuttall_tail ...).comp hb).const_mul ((Real.rpow 2 (...) : ℝ) : ℂ)
```
`natural_nuttall_tail` yields a `Tendsto ... (𝓝 (0 : ℝ))` (assuming `nuttallQ` is real-valued). However, the target limit is `(0 : Matrix (Fin s) (Fin s) ℂ)`, meaning entries are complex. The coercion `(... : ℝ) : ℂ` is applied to the scalar multiplier, but `tendsto_pi_nhds` expects the underlying entry type to match uniformly. If `nuttallQ` returns `ℝ`, composing with `hb` and multiplying by a coerced `ℂ` constant requires an explicit continuity argument for the embedding `ℝ →+* ℂ` preserving the zero limit. This is likely true but represents a semantic gap in the stated proof body.

**3. Division by Norm Without Nonzero Guarantee in Candidate 1**

In `theorem1CdfCandidate_tendsto_one`:
```lean
(hn.div_const ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖)
```
This divides by the constant `‖(... 0).det‖`. There is **no hypothesis** guaranteeing this norm is nonzero. Unlike `theorem2CdfCandidate_tendsto_one` which correctly includes `hden` backed by `theorem1PsiMatrix_zero_det_ne_zero`, candidate 1 lacks `hpos`/`hinj` assumptions entirely. If the determinant at zero vanishes, this division is undefined or collapses, invalidating the limit claim.

**4. `upperGammaComplement_eq_tail` Domain Constraint**

In `gamma_nat_tail`, the identity `upperGammaComplement_eq_tail (s := ((k+1 : ℕ) : ℂ))` is invoked with guard `hx : 0 ≤ x`. The complement equation typically holds for `Re(s) > 0`. Here `s = k+1 ≥ 1 > 0` is satisfied, but the proof relies on `by simp; positivity` discharging the complex real-part condition through a natural number coercion. This is valid only if the library lemma accepts `ℕ ⊆ {z | 0 < z.re}` directly via coercion; otherwise it's an API mismatch.

**5. Vacuous Quantification When `L = 0`**

When `L = 0`, `Fin 0` is empty, so `hpos : ∀ j, 0 < lambda j` and `hinj` hold vacuously. The matrix reduces to `s × s` with no eigenvalue dependence. All claims become trivial determinantal limits of zero matrices. Not a logical error, but the injectivity condition carries no structural content in this boundary case.
