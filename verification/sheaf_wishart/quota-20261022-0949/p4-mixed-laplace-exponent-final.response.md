## P4 Adversarial Review: `MixedLaplaceExponent.lean`

### 1. Critical Mathematical Gap: `vandermonde_det_div_scale` Proof Body

The proof of `vandermonde_det_div_scale` contains a substantive algebraic error in the matrix factorization step. The claim is that scaling Vandermonde nodes by `c⁻¹` factors out column-wise powers of `c`.

**The gap:** The proof asserts pointwise equality:
```
(c^j.val)⁻¹ * (lambda i / c)^j.val = (c^j.val)⁻¹ * (lambda i)^j.val
```
This is **false**. Expanding the left side:
```
(lambda i / c)^j.val = (lambda i)^j.val * (c^j.val)⁻¹
```
So the full entry is `(c^j.val)⁻¹ * (lambda i)^j.val * (c^j.val)⁻¹ = (c^(2*j.val))⁻¹ * (lambda i)^j.val`, not `(c^j.val)⁻¹ * (lambda i)^j.val`.

Alternatively, if the intent was to write `Matrix.vandermonde (fun i => lambda i/c)` as a product `D * Matrix.vandermonde lambda` where `D` is diagonal with entries `(c^j.val)⁻¹`, this doesn't work because the scaling `(lambda i/c)^j = lambda^j * c^{-j}` applies per-entry as a **column** scaling, not a row scaling. The correct statement should be:
```
det(Vandermonde(lambda/c)) = (∏ j, c^{-j}) * det(Vandermonde(lambda))
```
which follows from factoring `c^{-j}` out of column `j`. However, the intermediate matrix equality written using `Matrix.det_mul_row` is misapplied—this is a column operation, not a row operation, and the pointwise `ext i j` step as written does not typecheck correctly for the claimed factorization form.

**Verdict:** Actual mathematical gap. The theorem statement is likely correct; the proof body is wrong.

---

### 2. Missing Side Condition: Division by Zero

Both `vandermonde_det_div_scale` and `mixedNoncentralMomentMatrix_det_div_scale` take `c : ℝ` with no hypothesis `c ≠ 0`. The expressions `lambda i / c` and `(c^j.val)⁻¹` are undefined/zero-divisive when `c = 0`. In Lean's total division semantics these may evaluate without panic but the resulting identities are mathematically meaningless or require separate handling. This is an **actual gap** for any downstream application where `c` could be zero.

---

### 3. Dependency on Unverified `mixedNoncentralMomentMatrix_det`

The theorem `mixedNoncentralMomentMatrix_det_div_scale` rewrites using `mixedNoncentralMomentMatrix_det` twice. Per instructions, imported results are treated as separately checked dependencies. However, the rewrite pattern `rw [det, det, vandermonde_div]` assumes the determinant formula factors through the Vandermonde determinant in a way that makes the scaling identity a direct consequence. If `mixedNoncentralMomentMatrix_det` has additional prefactors depending on `lambda` beyond the Vandermonde determinant, those prefactors would also need scaling analysis. This is not a gap per se given the dependency assumption, but the proof structure is fragile—it works **only** if the imported determinant theorem has exactly the multiplicative form assumed.

---

### 4. Minor: `triangularIndexSum_double` Coercion Noise

The step `simp only [Nat.cast_add, Nat.cast_id]` suggests ℕ → ℤ or ℕ → ℝ coercion arithmetic is happening silently. Not a logical gap, but obscures whether `nlinarith` closes the goal over ℕ or requires ring homomorphism properties. Low severity.

---

**Summary:** One actual proof-body error (Vandermonde factorization), one missing nonzero hypothesis on `c`, one structurally fragile rewrite chain.
