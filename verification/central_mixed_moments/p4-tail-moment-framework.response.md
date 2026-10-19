# P4 Concrete Issue Report

## 1. ProbabilityTailIntegrability.lean

**`probabilityTail_le_one` — missing `measureReal_le_one` in Mathlib**
The identifier `measureReal_le_one` does not exist. The correct proof is:
```lean
μ.real {a | t ≤ f a} ≤ μ.real univ := measureReal_mono (fun a _ => trivial)
-- then use IsProbabilityMeasure to get μ.real univ = 1
```
Or directly: `exact ENNReal.toReal_le_of_le_ofReal (by simp [IsProbabilityMeasure.measure_univ])` after showing the measure is ≤ 1 as an ENNReal.

**`integrable_nonneg_iff_probabilityTail` — layercake direction mismatch**
The cited theorem `lintegral_eq_lintegral_meas_le` gives ∫⁻ t, μ {a | t ≤ f a} = ∫⁻ a, f a, but this is the **upper Lebesgue integral** (`∫⁻`), not the Bochner/standard integral. The conversion `← lintegral_ofReal_ne_top_iff_integrable` requires `AEStronglyMeasurable` of `probabilityTail μ f`, which you supply via monotonicity. However, the intermediate step:
```lean
apply lintegral_congr_ae
filter_upwards [] with t
exact ENNReal.ofReal_toReal (measure_ne_top _ _)
```
is **circular/wrong**: `ENNReal.ofReal_toReal` requires the argument to be ≠ ⊤, but `μ {a | t ≤ f a}` could a priori be ⊤ before you invoke probability measure. You need `[IsFiniteMeasure μ]` or explicitly `measure_ne_top μ _` which holds because `μ s ≤ μ univ = 1 < ⊤`. This works for probability measures but the `measure_ne_top _ _` placeholder doesn't auto-resolve without the instance in scope at that point.

**`measurable_probabilityTail` — antitone implies measurable**
`.measurable` on `Antitone` requires the codomain to have a second-countable topology or the domain to be ℝ with Borel. For `ℝ → ℝ` this is fine, but the instance resolution may fail silently. This is technically correct.

---

## 2. PowerTailIntegrability.lean

**`integrableOn_positive_sandwich_iff` — Fubini/abs rewrite is fragile**
In the first constructor direction:
```lean
rw [Real.norm_eq_abs, abs_of_nonneg (hgn t ht)]
rw [← div_eq_inv_mul]
apply (le_div_iff₀ hc).mpr
simpa only [mul_comm] using (hb t ht).1
```
The bound `(hb t ht).1` gives `c * g t ≤ F t`. Rewriting to `g t ≤ c⁻¹ * F t` requires `0 < c` (which you have), but `le_div_iff₀` produces `g t ≤ F t / c`, and the `mul_comm` simpa targets `c⁻¹ * F t = F t / c`. This is **correct but brittle** — if Mathlib's `div_eq_inv_mul` normal form changes, this breaks. More importantly, you're proving `g ≤ c⁻¹ F` pointwise to apply `.mono'`, which is valid. No actual error here, but the comment "Fubini interpretation" in the header is misleading — there is no Fubini in this file.

**`integrableOn_natPowerRatio_iff` — critical exponent divergence claim is WRONG for q+1=k**
```lean
rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ)<4)]
```
`integrableOn_Ioi_rpow_iff` states `IntegrableOn (fun t => t^p) (Ioi 4) ↔ p < -1`. Here `p = q - k`, so integrability ↔ `q - k < -1` ↔ `q + 1 < k`. At `q + 1 = k` (i.e., `p = -1`), the integral diverges logarithmically. The statement `↔ q+1<k` is therefore **correct**. No issue here.

**`integrableOn_powerTail_iff` — uses `t^q/t^k` with `q=0` implicitly later**
When called from `ProbabilityTailFirstMoment`, `q=0`, so the comparison function becomes `1/t^k`. The nonnegativity proof:
```lean
exact div_nonneg (pow_nonneg ht0.le q) (pow_nonneg ht0.le k)
```
is correct. No issue.

---

## 3. ProbabilityTailFirstMoment.lean

**`probabilityTail_integrableOn_near_zero` — bounded interval, bounded function**
Uses `(integrable_const (1 : ℝ)).mono'` with pointwise bound `probabilityTail_le_one`. This is correct for `Ioc 0 4` since it has finite volume. No issue.

**`integrable_nonneg_iff_probabilityTail_Ioi_four` — split correctness**
```lean
rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ)≤4), integrableOn_union]
simp only [probabilityTail_integrableOn_near_zero, true_and]
```
`Ioc 0 4 ∪ Ioi 4 = Ioi 0` is correct. `integrableOn_union` requires measurability of both sets, which holds. The simplification discards the left conjunct correctly. No issue.

**`integrable_nonneg_iff_two_sided_power_tail` — THE ACTUAL BUG: `ht4.le` vs `ht4`**
```lean
simpa only [pow_zero, div_eq_mul_inv, one_mul] using hb t ht4.le
```
Here `ht : t ∈ Ioi 4` means `4 < t`, and `ht4 : (4 : ℝ) < t`. Then `ht4.le : 4 ≤ t`. The hypothesis `hb` requires `4 ≤ t`, so this is **technically correct**. However, the bound `hb` is stated with `c/t^k` which is `c * t^0 / t^k`. The `simpa` reduces `t^0` to 1. This is fine.

**THE REAL ISSUE — exponent threshold confusion from P1:**
The final result is `Integrable f μ ↔ 1 < k`. This is the **first moment** (weight `t^0` in tail, corresponding to `E[f^1]`). The earlier P1 session incorrectly claimed the first inverse-moment threshold was `k > 2`; this file correctly identifies `k > 1`. No bug here — this is the fix.

**Missing: critical case `k = 1` divergence is asserted but not separately stated**
The `↔ 1 < k` includes divergence at `k = 1` (since `1 < 1` is false). This is mathematically correct: `∫ 1/t dt` on `Ioi 4` diverges. No issue.

---

## 4. Cross-Cutting Issues

| # | File | Issue | Severity |
|---|------|-------|----------|
| 1 | ProbabilityTailIntegrability | `measureReal_le_one` doesn't exist; needs `IsProbabilityMeasure` explicit invocation | **Build-breaking** |
| 2 | ProbabilityTailIntegrability | `measure_ne_top _ _` in `ofReal_toReal` relies on probability instance being inferred inside `calc`-like block; may timeout or fail | Medium |
| 3 | PowerTailIntegrability | Header says "Fubini interpretation" but no Fubini theorem is used | Doc-only |
| 4 | All files | `[需人工审查]` markers remain — axioms print as standard 3 (propext, funext, choice), confirming no exotic axioms, but human review tags weren't removed | Process |
| 5 | ProbabilityTailFirstMoment | `hb` uses `c/t^k` notation which parses as `c / t^k = c * t^(-k)`; the sandwich lemma expects `c * (t^q / t^k)`. When `q=0` these coincide, but the implicit coercion `ℕ → ℝ` for exponents should be explicit | Low |

---

## 5. What is NOT an issue (confirmed correct)

- Layercake application for probability tails: valid under `IsProbabilityMeasure`
- Two-sided sandwich with positive constants preserving integrability: standard comparison test, correctly formalized
- Power ratio integral threshold `q+1 < k`: matches `∫ t^{q-k} dt` convergence on `Ioi 4`
- Splitting `Ioi 0` into bounded `Ioc 0 4` + tail `Ioi 4`: valid, bounded part always integrable
- First moment criterion `k > 1` (not `k > 2`): correct for `E[f] = ∫ P(f ≥ t) dt`

---

## Summary

**One build-breaking issue**: `measureReal_le_one` must be replaced with an explicit proof using `IsProbabilityMeasure.measure_univ` or `measure_le_measure_univ` followed by the probability axiom. Everything else is either documentation debt or minor brittleness. The mathematical content (thresholds, layercake, sandwich) is correct.
