## P4 Adversarial Review: TwoSurplusOverlapKernel.lean

**1. Missing subset hypotheses in main theorems (Mathematical gap)**

`centralMixedMinorMoment_first_product_closed` applies `byCards_first_product_closed` with hypotheses derived from `Finset.subset_univ S/T` and `Finset.inter_subset_left/right`. These yield `S.card ≤ n`, `T.card ≤ n`, `(S ∩ T).card ≤ S.card`, and `(S ∩ T).card ≤ T.card` — exactly matching `ha, hb, hca, hcb`. This is correct. However, `twoExtraRowMinimumPolynomial_eq_overlapKernel` then uses `centralMixedMinorMoment_first_product_closed` to substitute directly into the polynomial definition. The closed-form denominator contains factors `(n - S.card)`, `(n - T.card)`, and `(n - (S ∩ T).card + 1)`. While the cardinality bounds guarantee these are well-defined natural numbers, the theorem statement itself does not require `S ⊆ Finset.univ` or `T ⊆ Finset.univ` as explicit assumptions — it quantifies over all `S T : Finset (Fin n)`. This is fine because `Finset (Fin n)` forces elements into `Fin n` by type, so `card ≤ n` is automatic. No actual gap here; the type system enforces the bounds.

**2. Division-by-zero risk in final simplification (Potential mathematical gap)**

In `twoExtraRowMinimumPolynomial_eq_overlapKernel`, after applying `centralMixedMinorMoment_first_product_closed`, the proof clears `n.factorial` and `(n+1).factorial` via `field_simp` using `h0` and `h1`. But `field_simp` must also discharge that the remaining denominator factors are nonzero: specifically `(n - (S ∩ T).card + 1 : ℕ) : ℝ`, `(n - S.card).factorial`, and `(n - T.card).factorial`. The factorial terms are always positive for natural inputs, so `positivity` would handle them. The linear term `n - (S ∩ T).card + 1 ≥ 1 > 0` since `(S ∩ T).card ≤ n`. The proof does not explicitly invoke these nonzeroness facts before calling `field_simp`. If `field_simp` succeeds silently, Lean's simplifier found them automatically; if it fails, the proof body is incomplete. **This is the only concrete verification concern**: whether `field_simp` alone discharges all denominator nonzeroness obligations without explicit `have` statements for the intersection-cardinal term.

**3. Implicit coercion behavior (Minor API question, not a gap)**

The expression `((n-(S ∩ T).card+1 : ℕ) : ℝ)` performs arithmetic in `ℕ` then coerces to `ℝ`. Since subtraction on `ℕ` is truncated, `n - (S ∩ T).card + 1` could behave unexpectedly if `(S ∩ T).card > n + 1`, but this is impossible given `(S ∩ T).card ≤ n`. The coercion is semantically correct under the established bounds. Not a gap.

**4. Summation exchange and `classical` usage (No issue)**

The double `Finset.sum_congr rfl` correctly restructures the iterated sum. The `classical` declaration enables `Finset` operations without decidability instances. Standard and acceptable.

**5. Dependency signatures (No mismatch detected)**

The rewrite uses `centralMixedMinorMoment_eq_byCards`, `centralDeterminantPowerMoment_add/one`, and `Nat.factorial_succ` as imported dependencies. Their application sites match expected argument structures based on the visible unfolding pattern. No semantic mismatch evident from the source alone.

**Summary**: One actionable concern — verify that `field_simp` in the final theorem actually discharges all denominator nonzeroness conditions automatically, particularly for `(n - (S ∩ T).card + 1)`. If the pinned Lean check exits 0, this is already confirmed and no fix is needed.
