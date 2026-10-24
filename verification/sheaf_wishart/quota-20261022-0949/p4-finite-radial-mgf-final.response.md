# P4 Adversarial Review

## GaussianFiniteSquareMGF.lean

**1. Missing nonnegativity constraint on `t` (Mathematical Gap).**
Both theorems assume only `ht : t < 1`. The imported scalar result `gaussianReal_integral_exp_shifted_square_sum` almost certainly requires `0 ≤ t` for convergence of the moment-generating function (the integral diverges for `t < 0` when applied to a squared Gaussian). If the scalar lemma has hypothesis `0 ≤ t ∧ t < 1`, then `simp_rw [gaussianReal_integral_exp_shifted_square_sum _ t ht]` will fail to unify. If `ht : t < 1` is genuinely sufficient in the scalar source, this is fine—but this should be verified as a concrete semantic match, not assumed.

**2. Empty index type edge case (Minor Gap).**
When `Fintype.card ι = 0`, the product measure is the Dirac at the unique empty function, and the integral equals 1. The RHS becomes `(sqrt (1-t))⁻¹)^0 * exp(0) = 1`, which works. However, `integral_fintype_prod_eq_prod` must handle the empty product correctly. This is likely fine in Mathlib but worth confirming the API contract.

**3. Integrability proof logic (Methodological Concern).**
`Integrable.of_integral_ne_zero` requires proving the integral is nonzero to conclude integrability. This is circular if the integral computation itself presupposes integrability. The tactic `rw [gaussianPi_integral_exp_shifted_square_sum ...]` uses the first theorem to compute the integral, but that theorem's statement with `∫ x, ... ∂μ` implicitly asserts the function is integrable (otherwise the integral is defined as 0 in Lean, breaking the equality). Verify that `gaussianPi_integral_exp_shifted_square_sum` does not have a hidden integrability side-condition.

## EvenRadialWeightedIntegral.lean

**4. `integral_comp_mul_left_Ioi` domain mismatch (Potential API Gap).**
The substitution `r ↦ c*r` maps `Ioi 0` to `Ioi 0` only when `c > 0` (given), but the lemma `integral_comp_mul_left_Ioi _ 0 hc` must produce exactly the Jacobian factor `1/c` without additional boundary terms. Confirm the exact signature: some change-of-variables lemmas require `c ≠ 0` rather than `0 < c`, and the orientation matters for signed measures.

**5. Power arithmetic error risk in `evenRadialKernel_weighted_integral` (Algebraic Gap).**
The final simplification chain `rw [show 2*(q+1)=(2*q+1)+1 by omega, pow_succ]; field_simp; simp [pow_succ, mul_comm]` rewrites `c^(2*q+1)` in the denominator against `c^(2*(q+1))` from the scaling identity. Verify that the exponent bookkeeping yields exactly `c^(2*(q+1))` in the denominator of the RHS, not `c^(2*q+1)`. The `omega` proof confirms `2*(q+1) = (2*q+1)+1`, so `c^(2*(q+1)) = c^(2*q+1) * c`, meaning an extra factor of `c` must be absorbed. If `evenRadialKernel_scaling` produces `c^(2*q+1)` on the LHS, the division should leave `c^1` unaccounted for unless the kernel normalization `noncentralChiEvenRadialKernel_integral_eq_one` carries a compensating factor. Trace the powers explicitly.

**6. Nonnegativity of `a` never assumed (Correctness Observation).**
The parameter `a : ℝ` appears in `noncentralChiEvenRadialKernel q a r`, which typically represents a noncentrality parameter requiring `0 ≤ a`. However, all identities are purely algebraic in `a` (via `a^2` and `a*r`), so no gap exists—just noting this is intentionally general.

**7. Same integrability circularity as Source 1.**
`evenRadialKernel_weighted_integrable` and `evenRadialKernel_mgf_integrable` both use `Integrable.of_integral_ne_zero` after rewriting via the computed integral. Same concern as point 3.
