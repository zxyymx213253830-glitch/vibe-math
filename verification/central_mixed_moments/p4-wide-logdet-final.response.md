I have reviewed the provided Lean source text and imported statements as a mathematical reviewer. I identify the following concrete mathematical issues within the scope of these statements:

**1. Incorrect use of `Matrix.det_one_add_mul_comm` in `det_one_add_gram_transpose`**

In `GramLogDetTranspose.lean`, the theorem `det_one_add_gram_transpose` concludes with:
```lean
simpa only [Matrix.mul_smul,Matrix.smul_mul,complexGram] using
  Matrix.det_one_add_mul_comm Xᴴ ((r : ℂ) • X)
```
The identity `det(I + AB) = det(I + BA)` requires matching the product `AB` to the left-hand side. Here, `A = Xᴴ` and `B = (r : ℂ) • X`. This yields:
- `AB = Xᴴ * ((r : ℂ) • X) = (r : ℂ) • (Xᴴ * X) = (r : ℂ) • complexGram X` ✓
- `BA = ((r : ℂ) • X) * Xᴴ = (r : ℂ) • (X * Xᴴ)` 

However, the goal after the `hsmall` rewrite is to establish equality with `det(1 + (r : ℂ) • complexGram Xᵀ)`, where `complexGram Xᵀ = Xᵀ * conjTranspose(Xᵀ) = Xᵀ * X̄`. The expression `(r : ℂ) • (X * Xᴴ)` is **not** equal to `(r : ℂ) • complexGram Xᵀ` in general—these are different matrices (`X * Xᴴ` is m×m while `complexGram Xᵀ` is n×n when X is m×n). The Sylvester identity correctly relates the determinants, but the specific invocation here appears to conflate `X * Xᴴ` with `complexGram Xᵀ`, which are only equal when m = n. The `simpa` step with `Matrix.mul_smul` and `Matrix.smul_mul` does not resolve this dimensional mismatch.

**2. Missing integrability justification for `integral_map_equiv` application**

In `WideGaussianLogDet.lean`, the theorem `expected_actualNoncentralMatrixLogDet_transpose` applies `integral_map_equiv` to the function `actualNoncentralMatrixLogDet Mᵀ r`. The imported asset states `integral_map_equiv is exact integral transport along measurable equivalence`, but this theorem requires the function to be integrable (or at least quasi-integrable) with respect to the source measure. The proof does not establish that `actualNoncentralMatrixLogDet Mᵀ r` is integrable before invoking `integral_map_equiv`. While the imported assets mention "Full actual logdet integrable all shapes, rho >= 0," this integrability fact is not explicitly invoked or referenced in the proof term. The same issue appears in `integral_actualRowGram_logdet_eq_transpose` where `integral_map_equiv` is applied to `fun z => Real.log ((complexGram (complexSampleMatrix z+Mᵀ)).det.re)` without an explicit integrability hypothesis discharging the requirement.

**3. Type coercion gap in prelog limit target**

In `actualNoncentralMatrixLogDet_allShapes_prelog`, the limit target is `(min m n : ℕ)` cast through `𝓝`. The division `(∫ ...)/Real.log r` produces a real number, and the filter convergence is in `ℝ`. The statement relies on the canonical coercion `ℕ → ℝ`, but when `hnm : n ≤ m` yields `Nat.min_eq_right hnm`, the rewrite produces `(n : ℕ)` which must then be coerced to match the real-valued filter target. The `simpa` tactic should handle this, but the intermediate theorem `actualNoncentralMatrixLogDet_expected_prelog hn hnm M` must return exactly `(n : ℝ)` in its limit—not merely something definitionally equal after coercion—for `simpa` to close the goal without an explicit `norm_cast` or `simp` lemma bridging `(min m n : ℕ)` to `(min (m : ℝ) (n : ℝ))`.

---

**Summary:** Issue (1) is a concrete mathematical error in the application of the Sylvester determinant identity where the matrix dimensions and products do not align as claimed. Issues (2) represent missing integrability preconditions for the integral transport theorems. Issue (3) is a minor type-coercion gap that may be resolvable by automation but represents a semantic mismatch as written.
