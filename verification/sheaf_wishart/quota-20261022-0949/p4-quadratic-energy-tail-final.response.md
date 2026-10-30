## P4 Adversarial Review: `QuadraticEnergyTailChange.lean`

**1. Critical Mathematical Gap: Missing Integrability Hypothesis**

The theorem `quadraticEnergy_tail_substitution` asserts an unconditional equality between two integrals without any integrability assumption on `g`. The substitution rule `integral_image_eq_integral_abs_deriv_smul` requires that the transformed integrand be integrable (or at least that one side exists). As stated, if `g` is not integrable on `Ioi (a^2/2)`, the left-hand side may be undefined while the right-hand side could diverge differently. The equality `∫ y in Ioi (a^2/2), g y = ∫ r in Ioi a, r * g (r^2/2)` needs an explicit hypothesis such as `IntegrableOn g (Ioi (a^2/2))` or must be framed in terms of extended nonneg reals with `ENNReal` integration. This is a **mathematical gap**, not merely an API question—the logical statement is incomplete without specifying the function space or integrability class of `g`.

**2. Potential API Mismatch: Substitution Theorem Signature**

The invocation `integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g` passes `g` directly. Depending on the exact Mathlib signature, this theorem may require `g` to satisfy a measurability condition (`AEMeasurable g`) or integrability condition explicitly. If the Codex-generated proof compiles, this is resolved by typeclass inference, but the review cannot verify compilation. Flagging as a **concrete semantic concern**: if `g : ℝ → ℝ` carries no measurability structure, the application may be ill-typed.

**3. Endpoint Behavior at `a = 0`**

When `a = 0`, the domain `Ioi 0 = (0, ∞)` and the map `r ↦ r²/2` sends `(0,∞) → (0,∞)`. The proof handles this correctly via `ha : 0 ≤ a`, but the strict inequality `a < r` combined with `ha` yields `0 < r` only when `a = 0` through `lt_of_le_of_lt ha hr`, which gives `0 < r`. This step is logically sound. No gap here; noting for completeness.

**4. Absolute Value Reduction Logic**

The final step `rw [abs_of_pos (lt_of_le_of_lt ha hr)]` correctly reduces `|r|` to `r` since `r > a ≥ 0` implies `r > 0`. This is valid.

**5. Image Theorem: Surjectivity Direction**

In `quadraticEnergy_image_Ioi`, the reverse direction constructs `⟨Real.sqrt (2*y), ...⟩`. The hypothesis `hypos : 0 ≤ 2*y` is derived from `a²/2 < y` and `a² ≥ 0`, giving `y > 0`, hence `2y > 0`. The use of `Real.sq_sqrt hypos` is correct. However, the proof that `a < Real.sqrt (2*y)` uses `nlinarith` after `change a < Real.sqrt (2*y)`. This requires `a² < 2y`, which follows from `a²/2 < y`. Sound.

**Summary of Problems:**
- **Actual gap**: Missing integrability/measurability hypothesis on `g` in `quadraticEnergy_tail_substitution`. The unconditional equality for arbitrary `g : ℝ → ℝ` is mathematically false without restricting to integrable functions or working in `ℝ≥0∪{∞}`.
- **API concern**: Exact signature match for `integral_image_eq_integral_abs_deriv_smul` regarding implicit measurability requirements on `g`.
