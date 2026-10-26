# P4 Adversarial Review

## PoissonFactorialMoments.lean

**1. `choose_factorial_shift` domain gap.** The identity `Nat.add_choose_mul_factorial_mul_factorial n j` is applied for all `n : ℕ`, but when the summation index in `poisson_choose_hasSum` is shifted via `hasSum_nat_add_iff`, the term at `n = 0` in the shifted series corresponds to original index `j`. The lemma statement uses `x^(n+j)` with `n : ℕ` starting from 0, which correctly covers indices ≥ j, but the proof of `hz` (vanishing for `n < j`) combined with `hfull` implicitly assumes the series reindexing is exact. This is algebraically correct but the `linear_combination` step in `choose_factorial_shift` multiplies by `x^n * x^j` without addressing whether `x = 0` creates a `0^0` issue when `n = j = 0`. Mathlib's `pow_zero` handles this (giving 1), so this is not a true gap—only a verification point. **No actual mathematical error.**

**2. `factorial_ratio_vandermonde` cast precision.** The Vandermonde identity `Nat.add_choose_eq n (q+k) k` produces natural numbers, and `exact_mod_cast` lifts it to ℝ. The division step requires `(n+q).factorial ≠ 0`, discharged by `positivity`. Correct. **No gap.**

## NoncentralRadialFullMoments.lean

**3. Fubini/Tonelli justification is structurally valid but has one subtle dependency.** The proof of `noncentralChiEvenRadialKernel_energyMoment` uses `integral_tsum_of_summable_integral_norm hF hsum`. The hypothesis `hF` claims `Integrable (radialMomentTerm q k a n) μ` for all `n`, proven in `radialMomentTerm_integrable`. However, `radialMomentTerm_integrable` proves `IntegrableOn ... (Ioi 0)` with respect to Lebesgue measure, while `hF` requires integrability with respect to `μ = volume.restrict (Ioi 0)`. These are definitionally equivalent in Mathlib (`IntegrableOn f s` := `Integrable f (volume.restrict s)`), so **no actual gap**, but the proof could be more explicit about this identification.

**4. Positivity claim in `radialMomentPolynomial_pos` requires scrutiny.** The theorem states `0 < poissonFactorialMomentPolynomial q k x` for `0 ≤ x`. The proof extracts the `j = 0` term: `((q+k).choose k : ℝ) * x^0 / 0! = ((q+k).choose k : ℝ)`. It then uses `single_le_sum` to bound the full sum below by this positive term. **This is valid only if all terms are nonneg**, which the proof discharges via `fun j _ => by positivity`. Since `x ≥ 0`, all binomial coefficients are positive naturals, and factorials are positive, each summand is indeed ≥ 0. The strict inequality follows because the `j=0` term is strictly positive and all others are ≥ 0. **No gap.**

**5. `gaussianOddMoment_general` dependency.** The proof of `radialMomentTerm_integral` invokes `gaussianOddMoment_general` (imported from `NaturalNuttallNormalization`). This is treated as a separately checked dependency per instructions. The exponent `2*(n+q+k)+1` is always odd and ≥ 1, matching the expected signature for Gaussian odd moments on `(0, ∞)`. **No semantic mismatch detected.**

## Theorem1ZeroMomentMatrix.lean

**6. `zeroMoment_prefactor` exponent arithmetic.** The identity `he` claims `((((2*(i.val+1)) - s - t)/2) + ((t-s)/2) + (s-(i.val+1))) = 0`. Expanding: the first term gives `(i.val+1) - s/2 - t/2`, the second gives `t/2 - s/2`, the third gives `s - i.val - 1`. Summing: `(i.val+1) - s/2 - t/2 + t/2 - s/2 + s - i.val - 1 = 0`. **Algebraically correct. No gap.**

**7. `Real.sqrt` domain in `ha`.** The proof requires `(Real.sqrt (2*lambda ⟨j.val,hj⟩))^2 = 2*lambda ⟨j.val,hj⟩`, which holds iff `2*lambda ≥ 0`. This is guaranteed by `hLambda _` giving `0 ≤ lambda j` and `mul_nonneg (by norm_num)`. **No gap.**

**8. Matrix entry type coercion.** The definition of `theorem1ZeroMomentMatrix` returns `ℂ` entries. The branch for `j.val < L` coerces from `Real.rpow` and `poissonFactorialMomentPolynomial` (both real-valued) into `ℂ`. The else branch uses `Nat.factorial` coerced to `ℂ`. The proof of `theorem1PsiMatrix_at_zero_eq_finiteMoments` applies `congrArg (fun y : ℝ => (y : ℂ))` to transfer the real prefactor identity into `ℂ`. **Type-correct. No gap.**

## Summary

**Actual mathematical gaps found: 0.** All core identities (Vandermonde convolution, exponential series manipulation, Fubini-Tonelli application, Gamma-factorial reduction at zero, prefactor exponent cancellation) are logically sound given the stated assumptions. The flagged `[需人工审查]` notes concern external dependency signatures and measure-theoretic conventions, not internal proof errors.
