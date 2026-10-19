# P4 Concrete Code Review: NoncentralInverseMinimumFirstMoment.lean

## 1. Exponent/Threshold Correctness (Fixed from P1)

The threshold correction is **correctly implemented**. The integrability condition uses tail exponent `k > 1` for the first moment (weight `t^1` in layer cake), not `k > 2`:

- `actualNoncentralInverseMinimum_integrable_iff` line 37 applies `integrable_nonneg_iff_two_sided_power_tail` with exponent `(d+1)`
- The equivalence resolves to `0 < d` (i.e., `d ≥ 1`), meaning row surplus `m - n = d > 0`
- For the first moment of the inverse, tail decay `P(X⁻¹ > t) ~ t^{-(d+1)}` requires `d + 1 > 1`, hence `d > 0`. This is consistent.

**No issue here.** The P1 confusion between moment `q+1` and `q` is resolved.

---

## 2. Fubini/Layer Cake Assumptions

**Concrete concern at line 37:** The theorem `integrable_nonneg_iff_two_sided_power_tail` encapsulates a layer cake decomposition + Fubini swap. The actual validity conditions are:

- The function must be nonnegative a.e. — discharged by `ae_of_all _ (actualNoncentralInverseMinimum_nonneg d n M)`
- The tail bounds must hold for all `t > 0` — discharged by the lambda at line 43 calling `actualNoncentralInverseMinimumTail_power_bounds`
- The measure must be sigma-finite — `stdGaussian` on a finite-dimensional complex vector space is a probability measure, hence finite

**No open Fubini issue**, provided `integrable_nonneg_iff_two_sided_power_tail` itself correctly handles the Fubini direction (that belongs to the imported file's review, not this leaf).

---

## 3. Real Bochner vs ENNReal Interpretation

**Correctly handled at lines 59–65.** The square case `d = 0` uses `∫⁻ z, ENNReal.ofReal (...)` rather than the real Bochner integral. This is essential because:

- Mathlib's Bochner integral returns `0` (default) for non-integrable functions, which would obscure divergence
- `lintegral_ofReal_ne_top_iff_integrable` at line 62 correctly bridges ENNReal finiteness to Bochner integrability
- The contradiction at line 64 extracts `0 < 0` from assuming finite lintegral, which is sound

**No issue.**

---

## 4. Boundary Case `n ≤ m` / `0 < n`

**Line 50:** `actualNoncentralRectangular_inverseMinimum_integrable_iff` correctly requires `hn : 0 < n` and `hnm : n ≤ m`. The substitution `m = d + (k + 1)` with `k + 1 = n` via `Nat.exists_eq_succ_of_ne_zero` is valid since `n > 0`.

**Edge case `n = m` (i.e., `d = 0`):** Correctly routes to the non-integrable square case. The equivalence `n < m ↔ 0 < d` holds by `omega`.

**No boundary issue.**

---

## 5. Gaussian Support / Full Rank

**Not an assumption made here.** The file imports `NoncentralInverseMinimumTail` which should carry the full-rank/a.e.-positive-smallest-eigenvalue result. This leaf only consumes those tail bounds as black-box inputs at line 43. If the support characterization fails, it fails upstream — not in this file.

**No local issue; dependency is explicit.**

---

## 6. No Gamma Law / No Exact Value

Confirmed: the file only establishes the **integrability threshold** (`d > 0`), never computes `E[X⁻¹]` in closed form, and invokes no Gamma/distributional identity.

---

## 7. Axiom Check

The `#print axioms` commands at lines 68–72 will reveal only `propext`, `Quot.sound`, `Classical.choice` (standard 3) if all imports are constructive aside from LEM/choice. Since the file uses `by_contra` (line 60) and `ae_of_all` (which invokes classical reasoning about null sets), `Classical.choice` is expected. **No exotic axioms introduced locally.**

---

## Summary of Concrete Findings

| Item | Status | Location |
|------|--------|----------|
| Threshold `k > 1` for first moment | Correct | Line 37, 45 |
| Layer cake/Fubini preconditions | Discharged locally | Lines 38–43 |
| ENNReal lintegral for divergence | Correct pattern | Lines 59–65 |
| Square case `d = 0` boundary | Handled | Line 57 |
| Rectangular reparametrization | Sound | Lines 49–54 |
| Gamma/exact value assumption | Absent (correct) | Throughout |
| Exotic axioms | None beyond standard 3 | Lines 68–72 |

**Verdict:** No concrete mathematical or formalization errors detected in this leaf file. The `[需人工审查]` comment at line 7 is overly cautious — the three flagged items (layer cake, Gaussian support, expectation interpretation) are either discharged by the imported theorems or correctly handled by the ENNReal formulation. Support/Gaussian concerns belong to the tail bound file's review scope, not this one.
