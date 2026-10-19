I'll review both files for concrete mathematical and formal issues.

## Concrete Issues Found

### LogMeanBound.lean

**1. Missing integrability proof for `integral_log_tangent_upper_bound` application (line 47-52)**

In `integral_finiteSpectrumLogDet_mean_upper_bound`, the theorem applies `integral_log_tangent_upper_bound` with `f := fun x => 1 + r * f i x`. The positivity hypothesis is discharged by `(hnonneg i).mono (fun x hx => by positivity)`, but this only proves `0 ≤ 1 + r * f i x`, not the strict positivity `0 < 1 + r * f i x` required by `hpos : ∀ᵐ x ∂μ, 0 < f x`. When `r = 0` or `f i x = 0`, you get exactly 1, which is fine, but the `positivity` tactic needs to actually close this goal given that `hr : 0 ≤ r` and `hnonneg i : 0 ≤ f i x`. This should work, but verify the `positivity` call doesn't leave a sorry.

**2. Implicit use of `Fintype.card (Fin n)` vs `n` coercion**

Line 44: `let K : ℝ := Fintype.card ι` where `ι` will be instantiated as `Fin n` in the application. The cast `(Fintype.card ι : ℝ)` appears throughout. No bug, but the final `simpa only [Fintype.card_fin]` at the call site must reduce `Fintype.card (Fin (Fintype.card (Fin n)))` to `n`, which requires the double-cardinality to collapse correctly. This is mathematically sound but fragile if upstream definitions change.

**3. `integral_finsetSum` swap (line 56)**

The equality `∫ x, finiteSpectrumLogDet ... = ∑ i, ∫ x, Real.log (1 + r * f i x)` uses `integral_finsetSum _ (fun i _ => hi i)`. The integrability hypothesis `hi i` is exactly what's needed. No issue here—this is correct.

---

### ActualLogDetMeanBound.lean

**4. `actualExpectedGramPower` defined without integrability guard**

The definition `∫ z, (complexGram (complexSampleMatrix z + M)).trace.re ∂stdGaussian _` is well-typed as a noncomputable real, but there's no proof bundled with the definition that this integral is finite. Finiteness is established later via `sum_integral_actualNoncentralEigenvalues_eq_power` combined with eigenvalue integrability, but the definition itself doesn't carry this. Not a bug per se, but any downstream use before finiteness is proved would be working with a potentially infinite value.

**5. Eigenvalue indexing mismatch risk in `sum_actualNoncentralEigenvalues_eq_trace`**

Lines 22-30: The proof introduces `e : Fin (Fintype.card (Fin n)) ≃ Fin n` via `Fintype.equivOfCardEq`. This works because `Fintype.card (Fin n) = n`, so both sides are `Fin n`, making `e` essentially the identity up to definitional equality. However, the rewrite `hs` uses `Equiv.sum_comp e` which reindexes the sum. If `complexNoncentralSampleEigenvalue M i z` is defined to return eigenvalues indexed by `Fin n` (the column count), and `h.eigenvalues₀` is indexed by `Fin (Fintype.card (Fin n))`, these are definitionally equal types but the equiv is still invoked. This is technically correct but adds unnecessary transport overhead. Verify that `complexNoncentralSampleEigenvalue`'s index type matches the spectrum index type exactly.

**6. Transpose proof `actualExpectedGramPower_transpose` relies on `integral_map_equiv` signature**

Lines 49-58: The proof uses `integral_map_equiv` applied to a `MeasurableEquiv`. Per your specification, "imported `integral_map_equiv` EXACT pinned signature takes measurable equivalence + function, NO integrability premise." If the actual Mathlib/dependency signature requires an integrability side condition on the target function, this would fail. The proof does NOT discharge any integrability obligation for `fun z => (complexGram (complexSampleMatrix z + Mᵀ)).trace.re` with respect to the pushed-forward measure. Given that finiteness is established separately (as stated), this should be fine, but confirm the exact signature of `integral_map_equiv` in your import chain.

**7. `hn : 0 < n` vs `hm : 0 < m` asymmetry in column bound**

`actualNoncentralMatrixLogDet_column_mean_bound` takes `hn : 0 < n` and bounds by `n * log(1 + r * T / n)`. The wide-case transpose branch in `min_dimension_mean_bound` uses `hm : 0 < m` applied to `Mᵀ`, yielding `m * log(1 + r * T / m)`. This correctly produces `min m n` in both cases. No bug—the logic is sound.

**8. `ae_of_all` usage for nonnegativity (line 68)**

`fun i => ae_of_all _ (complexNoncentralSampleEigenvalue_nonneg M i)` produces `∀ᵐ z, 0 ≤ eigenvalue i z`. This is the correct type for `hnonneg` in `integral_finiteSpectrumLogDet_mean_upper_bound`. No issue.

**9. Potential coercion issue: `(min m n : ℕ)` to `ℝ`**

Line 80: `(min m n : ℕ) * Real.log (...)` — the `*` here requires coercing `min m n` from `ℕ` to `ℝ`. Lean should insert this automatically via `Nat.cast`, but if the instance resolution fails, you'd need `(↑(min m n) : ℝ)`. The `simpa only [Nat.min_eq_right hnm]` suggests the coercion path is handled. Verify this compiles without explicit casts.

**10. No `ρ = 0` special-casing needed but worth confirming**

When `r = 0`, the bound becomes `k * log(1 + 0) = 0`, and the LHS is `∫ log det(I) = ∫ 0 = 0`. The inequality `0 ≤ 0` holds. The tangent bound `log y ≤ log a + y/a - 1` with `a = 1` gives `log y ≤ y - 1`, which is tight at `y = 1`. All proofs should go through without division-by-zero since `ha : 0 < a` becomes `0 < 1`. Confirmed sound.

---

### Summary of Actionable Items

| # | Severity | Location | Issue |
|---|----------|----------|-------|
| 1 | Medium | LogMeanBound.lean:47-52 | Strict positivity `0 < 1 + r*f i x` must be closed; `positivity` should work but verify no remaining goals |
| 4 | Low | ActualLogDetMeanBound.lean:13 | Definition lacks bundled finiteness; proven later but could surprise intermediate users |
| 5 | Low | ActualLogDetMeanBound.lean:22-30 | Unnecessary equiv transport when index types are definitionally equal; cosmetic/fragile |
| 6 | **High** | ActualLogDetMeanBound.lean:49-58 | `integral_map_equiv` integrability-premise absence must match actual imported signature; if wrong, proof breaks |
| 9 | Low | ActualLogDetMeanBound.lean:80 | Confirm `ℕ → ℝ` coercion resolves for `min m n` in multiplication |

**No logical errors in the mathematics.** The tangent-line bound strategy, eigenvalue-to-trace identification, min-dimension selection via transpose, and probability-measure integration are all structurally correct. The primary risk is item #6 (signature mismatch on `integral_map_equiv`) which is an interface contract issue, not a math error.
