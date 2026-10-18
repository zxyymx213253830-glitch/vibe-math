# P4 Independent Issues-Only Review: Central Complex Wishart Determinant-Power Size-Bias

## 1. Positivity / Zero-Dimension / p=0 Edge Cases

**`centralDeterminantPowerMoment_pos` is false at `n = 0`.**
The theorem states `0 < centralDeterminantPowerMoment d n p` for all `d n p : ℕ`. But when `n = 0`, the product over `Fin 0` is empty, yielding `1`. While `0 < 1` holds, the deeper issue is that `centralWishartMatrixDensity d 0 A` and the Wishart measure itself are degenerate at dimension 0. The positivity proof uses `apply Finset.prod_pos` which vacuously succeeds, but downstream theorems (e.g., `centralWishartMatrixDensity_power_bias`) use `(centralDeterminantPowerMoment_pos d n p).le` to justify `ENNReal.ofReal_mul`. At `n = 0` this is technically sound but masks that the entire statement is vacuous. **This is a concrete local error in mathematical intent**, not merely an imported obligation.

**`p = 0` case is correct but relies on imported normalization.**
When `p = 0`, `centralDeterminantPowerMoment d n 0` should equal `1`. The factorial ratio becomes `(d+j.val)!/(d+j.val)! = 1`. This is fine. However, `centralWishartDensityConstant_power_bias` at `p = 0` reduces to `centralWishartDensityConstant d n = 1 * centralWishartDensityConstant d n`, which is tautological. No local error here; this is correctly handled.

**`d = 0` is not guarded.**
The Wishart parameter `m := d + n` requires `m ≥ n` (i.e., `d ≥ 0`, which holds for `ℕ`). But `d = 0` gives a singular Wishart. The density formula uses `A.det.re ^ d`, which at `d = 0` becomes `A.det.re ^ 0 = 1` even when `A.det = 0`. The `if A.PosDef` guard saves this: positive definite matrices have strictly positive determinant. **No local error**, but human interpretation must note that `d = 0` Wishart is supported on PSD matrices, not PD, so the density is zero a.e. under the PosDef indicator. This is an **imported modeling obligation**.

---

## 2. Actual-Law vs Assumed Density

**This is NOT an assumed target density — confirmed correct.**
The file explicitly constructs `centralWishartMatrixDensity` as a concrete function and proves `complexWishart_eq_matrixDensity` from `CentralWishartMatrixDensity.lean`. The size-bias identity `complexWishart_determinant_power_bias` is derived by rewriting the actual law's density, not by postulating a tilted measure. This is the strongest aspect of the file.

**However, the density constant convention is imported and unverified locally.**
`centralWishartDensityConstant` comes from `CentralWishartNormalization`. The power-bias theorem `centralWishartDensityConstant_power_bias` asserts:
```
C(d,n) = moment(d,n,p) * C(d+p, n)
```
This is an algebraic identity about Gamma/factorial ratios. The proof unfolds both constants and does field arithmetic. **Locally valid** given the import, but if the imported constant uses a different variance convention (e.g., `Σ = I` vs `Σ = 2I` for complex Wishart), the numeric value of the moment shifts. This is the flagged `[需人工审查]` item and remains a **human measure/model interpretation obligation**, not a Lean-level error.

---

## 3. Full Matrix Reference Measure

**Correctly Hermitian-coordinate, not ambient complex Lebesgue — no error.**
`hermitianAmbientCoordinateMeasure` is defined as `(hermitianRealCoordinateMeasure n).map hermitianOfRealCoordinates`. The docstring explicitly disclaims ambient `2n²`-dimensional volume. Theorem `complexWishart_eq_matrixDensity` proves the Wishart law equals this reference measure with the matrix density. The chain:
```
complexWishart → realCoordinates → hermitianOfRealCoordinates → withDensity matrixDensity
```
is compositionally sound. `setLIntegral_map` is applied with measurability side conditions proved locally (`measurable_centralWishartMatrixDensity`, `continuous_hermitianOfRealCoordinates.measurable`). **No concrete local errors.**

**Imported obligation:** `hermitianRealCoordinateMeasure` and the coordinate maps come from `CentralWishartMatrixDensity.lean`'s imports. Their correctness as the "right" reference for Wishart is a modeling choice, not verified here.

---

## 4. Higher-Row Dimension Interpretation

**The claim "det(W)^p adds p rows" is mathematically standard and locally consistent.**
The parameter shift `m := d + n` → `m := (d+p) + n` corresponds to adding `p` degrees of freedom. For complex Wishart, `E[det(W)^p]` under `W ~ CW_n(m, I)` equals `∏_{j=1}^n (m-j+p)!/(m-j)!` when `m ≥ n`. Here `m = d+n`, so `m - j = d + n - j`, and the product index `j : Fin n` gives `j.val ∈ {0,...,n-1}`, so `d + j.val + p` ranges over `{d+p, ..., d+n-1+p}`. 

**Concrete verification:** The factorial ratio in `centralDeterminantPowerMoment` is `(d+j.val+p)! / (d+j.val)!`. With `m = d+n`, the standard moment is `Γ(m-j+p+1)/Γ(m-j+1)` for `j=1,...,n` (1-indexed). Reindexing to 0-indexed `j.val`: `m - (j.val+1) + p = d + n - j.val - 1 + p`. The file uses `d + j.val + p`. These match only if `n - 1 - j.val = j.val`, i.e., `n = 2*j.val + 1`, which is NOT generally true.

**THIS IS A CONCRETE LOCAL ERROR.** The indexing in `centralDeterminantPowerMoment` does not match the standard complex Wishart determinant moment formula. The product should be over `(d + n - 1 - j.val + p)! / (d + n - 1 - j.val)!` or equivalently reindex. As written, `d + j.val + p` increases with `j.val`, whereas the correct Wishart moment factors decrease (or increase depending on convention, but must align with `m - j`). **Human review required to confirm whether this is a notational choice in the imported `centralWishartDensityConstant` definition or an actual bug.**

---

## 5. ENNReal Integral Manipulations

**All manipulations are locally sound with explicit side conditions.**

- `ENNReal.ofReal_mul` is guarded by nonnegativity proofs (`hD`, `(centralDeterminantPowerMoment_pos _ _ _).le`). **Correct.**
- `withDensity_mul`, `withDensity_smul'` require measurability — provided via `hD`, `hP`, `hf`. **Correct.**
- `ENNReal.ofReal_ne_top` is used for `withDensity_smul'`. **Correct** (reals embed finitely).
- `lintegral_withDensity_eq_lintegral_mul` and `lintegral_smul_measure` are standard MeasureTheory API. **No local error.**
- `ae_of_all` for `withDensity_congr_ae` uses pointwise equality from `centralWishartMatrixDensity_power_bias`. **Correct.**
- `complex_norm_eq_re_of_nonneg` applied to `hA.det_pos.le` extracts `‖A.det‖ = A.det.re` for PosDef. **Correct.**

**One subtle point:** `ENNReal.ofReal (‖A.det‖^p)` — the norm is always nonneg, so `ofReal` is well-defined. At `A.det = 0` (non-PosDef branch), both sides are `0` and the `if_neg` handles it. **No error.**

---

## 6. Nested-Minor Mixed Moments (NOT Arbitrary Partial Overlap)

**The scope is correctly limited — no overclaim.**

`complexWishart_nested_determinant_moment` computes:
```
∫ ‖A.det‖^p * ‖(A.submatrix e e).det‖^q dμ(A)
```
by first applying the full-matrix size-bias (shifting `d → d+p`), then computing the minor moment under the shifted law. This works because:

1. The size-bias identity is exact (proven above).
2. `complexWishart_principalSubmatrix_norm_moment` gives the minor moment under any Wishart law.
3. The composition yields `moment_full(d,n,p) * moment_minor((d+p)+n-k, k, q)`.

**Why this is NOT arbitrary partial overlap:** The theorem requires `e : Fin k → Fin n` injective, defining a principal submatrix of the SAME matrix `A`. Both determinants are evaluated on the same sample. The size-bias transforms the joint law, after which the marginal minor law is extracted via `complexWishart_principalSubmatrix_law` (imported). There is no claim about two independent minors or overlapping index sets with different embeddings. The docstring accurately scopes this.

**Concrete check on parameters:** After bias, the law is `CW_n((d+p)+n, I)`. The minor of size `k` has law `CW_k((d+p)+n - (n-k), I) = CW_k((d+p)+k, I)`? No — `complexWishart_principalSubmatrix_law` states the minor of `CW_n(m)` is `CW_k(m - n + k)` (imported obligation to verify this formula). The file writes `(d+p)+n-k` as the new degree parameter. With `m' = (d+p)+n`, minor parameter is `m' - n + k = (d+p)+n - n + k = (d+p)+k`. But the code says `(d+p)+n-k`. 

**THIS IS A CONCRETE LOCAL ERROR or an imported convention mismatch.** If the principal submatrix law subtracts `(n-k)` rather than adding `k`, then `(d+p)+n-k` is wrong; it should be `(d+p)+k`. Alternatively, if the parameterization is `m = d + n` where `d` is the "excess", then excess for minor is `(d+p) + (n-k)`, giving `m'_minor = (d+p)+(n-k)+k = (d+p)+n`. Confusion between these conventions is likely. **Requires human review against imported `complexWishart_principalSubmatrix_law`.**

Additionally, `ht : k ≤ t` hypothesis in `complexWishart_principalSubmatrix_norm_moment` is satisfied by `(by omega)` using `hk : k ≤ n`. Since `t = (d+p)+n ≥ n ≥ k`, this is fine. **No error in the inequality discharge.**

---

## Summary of Issues

| # | Type | Location | Severity | Description |
|---|------|----------|----------|-------------|
| 1 | **Concrete Local Error** | `centralDeterminantPowerMoment` indexing | HIGH | Factorial ratio uses `d+j.val+p` but standard Wishart moment requires alignment with `m-j = d+n-1-j.val`. Verify against imported constant convention. |
| 2 | **Concrete Local Error** | `complexWishart_nested_determinant_moment` parameter | HIGH | Post-bias minor parameter `(d+p)+n-k` may be incorrect; expected `(d+p)+k` or `(d+p)+n` depending on submatrix law convention. |
| 3 | **Imported Obligation** | `centralWishartDensityConstant` | MEDIUM | Variance/scaling convention not verified locally; affects numeric correctness of moment values. |
| 4 | **Imported Obligation** | `complexWishart_principalSubmatrix_law` | MEDIUM | The degree-of-freedom shift formula for minors is imported; local usage assumes a specific form. |
| 5 | **Modeling Interpretation** | `d = 0` / `n = 0` | LOW | Vacuous or degenerate cases not explicitly excluded; proofs go through but semantic meaning requires human judgment. |
| 6 | **Positive** | Overall structure | — | Actual-law derivation (not assumed density), correct ENNReal hygiene, proper reference measure, honest scope limitation on nested minors. |

**Bottom line:** Two concrete local indexing/parameter errors (Issues 1 and 2) require human verification against the imported definitions. The ENNReal machinery, measure-theoretic reference construction, and logical structure are sound. The `[需人工审查]` flags are appropriately placed on the Gaussian convention and model interpretation.
