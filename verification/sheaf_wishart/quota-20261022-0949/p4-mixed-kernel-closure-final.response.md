# P4 Adversarial Review

## Actual Mathematical Gaps

**1. `finiteMixedKernel_tendsto` requires unstated summability conditions.**
The infinite kernel's noncentral entry uses `∑' m : ℕ, x i ^ m * (noncentralKernelSeriesWeight q m * lambda b ^ m)`. The proof imports pointwise convergence from `finiteNoncentralFullKernel_tendsto`, but that theorem's validity depends on convergence of the power series. The hypotheses `hxp : ∀ i, 0 ≤ x i` and `hlp : ∀ i, 0 ≤ lambda i` provide **no bound** on `x i` or `lambda i`. If `x i * lambda b ≥ 1` (or exceeds the radius of convergence of `noncentralKernelSeriesWeight`), the `tsum` diverges and `infiniteMixedKernel` is ill-defined as a real matrix. The proof treats `finiteNoncentralFullKernel_tendsto` as a black box, but without verifying its preconditions hold under the stated assumptions, this is a semantic gap, not merely an API question.

**2. `ge_of_tendsto` applied to a limit that may not exist in ℝ.**
In `infiniteMixedKernel_det_lower_bound`, the argument applies `ge_of_tendsto` to pass the finite inequality through the limit. This requires that `(infiniteMixedKernel p L q x lambda).det` is a well-defined real number. But if any tsum entry diverges (see point 1), the matrix entries are not real-valued, and the determinant operation is undefined. The continuity argument `continuous_id.matrix_det` is valid only on matrices with real entries; it does not handle extended reals or conditional convergence.

**3. `mixedLowestMinor` instantiation silently fixes N = p + L.**
`mixedLowestMinor` hardcodes `N := p + L` and uses `finSumFinEquiv` as the selection. In `finiteMixedKernel_det_lower_bound`, the sum ranges over all `f : Fin (p+L) → Fin N` where `N ≥ p + L`. The term identified as `mixedLowestMinor` corresponds to `f0 := Fin.castLE hN`, which maps into the first `p + L` indices of `Fin N`. This is correct, but the claim that this single term lower-bounds the full Cauchy–Binet sum relies on every other term being nonneg—which is established. No gap here, but worth noting the logic depends critically on `hw : ∀ m, 0 < w m` holding for **all** natural numbers, not just those below N.

**4. `noncentralKernelSeriesWeight` positivity proof is incomplete.**
Both `infiniteMixedKernel_det_lower_bound` and `infiniteMixedKernel_det_pos` discharge `hw` via `fun m => by unfold noncentralKernelSeriesWeight; positivity`. This tactic succeeds only if `noncentralKernelSeriesWeight q m > 0` is definitionally true or follows from imported lemmas. If the weight involves alternating signs, factorials in denominators, or conditional expressions, `positivity` may silently fail or succeed only because of how the definition unfolds—not because the mathematical claim holds for all `q, m`. The review cannot verify the body of `noncentralKernelSeriesWeight`, but flagging: this one-liner carries the entire positivity burden for the infinite case.

**5. Missing injectivity check in `hterm` rewrite.**
In `finiteMixedKernel_det_lower_bound`, the identity `hterm` equates the Cauchy–Binet summand to `mixedSelectionMinorProduct ... (f ∘ e)`. The subsequent call to `mixedSelectionMinorProduct_nonneg` does **not** require injectivity of `f ∘ e` (it handles the non-injective case by returning 0). This is logically sound. However, the decomposition in `hA`/`hB` uses `Matrix.det_submatrix_equiv_self`, which requires `e` to be an equivalence—true here—but the orientation `(f ∘ e)` versus `(e ∘ f)` matters for whether rows or columns are permuted. The proof writes `submatrix e e` on both factors; verify this matches the actual index structure of `mixedSelectionMinorProduct`, which takes `f : (Fin p ⊕ Fin L) → Fin N` as a **column** selector.

## Optional / Minor

None elevated to gap status.
