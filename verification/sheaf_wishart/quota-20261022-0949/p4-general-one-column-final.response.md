# P4 Adversarial Review

## EvenRadialProbability.lean

**1. `integral_withDensity_eq_integral_toReal_smul₀` API mismatch (actual gap risk).** The theorem name ends in `_smul₀`, suggesting it requires the density to be finite a.e. or integrable in a specific sense beyond what's provided. The proof supplies `ENNReal.ofReal_lt_top` pointwise, but if this lemma actually requires global integrability of the density (not just pointwise finiteness), the application is incomplete. Verify the exact signature: does it need `Integrable` of the ENNReal-valued function, not merely pointwise `< ⊤`?

**2. `evenRadialMeasure_integrable_exp_energy` uses `Integrable.of_integral_ne_zero` (logical error).** This API claims that if an integral is nonzero, the function is integrable. This is mathematically false in general—a non-integrable function can have a nonzero extended integral. The correct direction is: integrability plus nonzero integral gives information, not the reverse. Unless Mathlib has a very specific lemma with this exact name requiring additional hypotheses (e.g., positivity + finite measure space + measurable), this proof body is unsound. The MGF being well-defined and nonzero does not automatically certify integrability without already knowing the integral is finite.

**3. Instance attribute on parameterized theorem.** `attribute [instance] evenRadialMeasure_isProbabilityMeasure` makes a theorem with free parameters `(q : ℕ) (a : ℝ)` into a typeclass instance. Lean's instance resolution will not know how to infer `q` and `a`. This creates a dangling instance that either never fires or causes performance issues. It should be a `def` or restricted to fixed parameters.

## GaussianEvenRadialLaw.lean

**4. `map_pi_eq_stdGaussian` direction/signature.** The rewrite `← map_pi_eq_stdGaussian` is used to replace `Measure.pi (fun _ => gaussianReal 0 1)` with `stdGaussian (EuclideanSpace ℝ ι)`. Verify this imported lemma actually states equality in this direction for the product-of-1D-Gaussians construction of `stdGaussian` on `EuclideanSpace`. If it's stated as `stdGaussian = pi ...`, the `←` is correct, but semantic mismatches in how `EuclideanSpace` vs `ι → ℝ` are identified matter here.

**5. `hpow` exponent arithmetic assumes `1 - t > 0` for `Real.sq_sqrt`.** The proof writes `Real.sq_sqrt hp` where `hp : 0 ≤ 1 - t`. But `ht : t < 1` gives `0 < 1 - t`, so `hp` should be strict. Using `le_of_lt` loses strictness. While `sq_sqrt` only needs `≥ 0`, the subsequent `inv_pow` manipulations require the base to be nonzero—i.e., `1 - t ≠ 0`, which follows from `ht` but isn't explicitly invoked when rewriting inverses. Minor but worth confirming Lean doesn't silently divide by zero in `inv_pow`.

## GeneralOneColumnActualCDF.lean

**6. `hI` integrability restriction via `.mono_set` with wrong set relation.** The proof uses `(integrableOn_noncentralChiEvenRadialKernel q a).mono_set (fun _ hr => hr.1)`. Here `hr : r ∈ Ioc 0 (Real.sqrt (2*x))` and `hr.1 : 0 < r`. But `mono_set` requires proving the new domain is a subset of the old one. The original integrability is on `Ioi 0` (from `evenRadialMeasure`). The argument `fun _ hr => hr.1` shows `Ioc 0 R ⊆ Ioi 0`, which is correct. No issue here upon close reading.

**7. `complexNoncentralSampleSmallestEigenvalue M (by norm_num)` — proof obligation suppressed.** The `(by norm_num)` fills a proof argument (likely `n = 1` or `0 < n`). If this is a positivity proof for column count, `norm_num` succeeding means it's trivially `0 < 1`, which is fine. But ensure this isn't masking a hypothesis that should be explicit.

**8. `theorem12OneColumnCandidates_eq_radialCDF` imported without signature check.** This is treated as a dependency. However, the final `.trans hF.symm` chains equalities—if `theorem1CdfCandidate` outputs a CDF expression and `hF` equates `F` to the radial integral, the transitivity direction must match. Verify the LHS/RHS orientation in the imported theorem aligns with how `.1.trans` is applied.
