## P4 Adversarial Review

### PositiveModeFirstCoefficient.lean

**1. Division-by-zero in `squeeze_zero'` application (Mathematical Gap)**

The theorem `scaled_log_inverse_first_correction_bounds` is applied with parameters `t x ht hp`, producing bounds on the gap `x⁻¹ - t*positiveModeOffsetError x t`. The upper bound is `(1/(2*x^2))/t`. When applying `squeeze_zero'`, the proof requires that this upper bound tends to 0, which it does for fixed `x > 0`. However, the squeeze theorem also requires the lower bound to be non-negative. The source asserts this via `hh := (...).1` but never states what the lower bound actually is. If the lower bound from `scaled_log_inverse_first_correction_bounds` is negative or has different asymptotic behavior, the `squeeze_zero'` application is invalid. The explicit form of both bounds should be visible in this proof body to verify the squeeze conditions.

**2. Missing justification for `Real.log_mul` preconditions (Mathematical Gap)**

The step `rw [Real.log_mul htx harg.ne']` requires proving `1 + (t*x)⁻¹ ≠ 0`. The proof discharges this with `have harg : 0 < 1+(t*x)⁻¹ := by positivity`. While `positivity` can handle simple inequalities, the expression `1 + (t*x)⁻¹` with hypotheses `0 < t` and `0 < x` requires knowing that `(t*x)⁻¹ > 0`, hence `1 + (t*x)⁻¹ > 1 > 0`. This is mathematically correct but relies on `positivity` successfully chaining through the inverse. This is a minor verification concern, not a gap, but worth confirming the tactic succeeds.

### ActualPositiveFirstCoefficient.lean

**3. Index substitution assumes uniqueness without justification (Mathematical Gap)**

The proof obtains `i0` as the smallest positive eigenvalue coordinate via `exists_actualCorrelated_smallest_positive_coordinate`, then asserts `he : i = i0` by `Fin.ext (by rw [← hr] at hi0; omega)`. This reasoning is incomplete. The hypothesis `hi : i.val + 1 = min m r` fixes `i` to a specific index. The existence lemma provides some `i0` satisfying the minimum-eigenvalue property. Equating them requires that the index satisfying `hi` is *unique* and that `i0` satisfies the same constraint. The `omega` call may close the goal if `hi0` also constrains `i0.val + 1 = min m r`, but this depends on the exact statement of the existence lemma, which is not visible here. If the existence lemma returns an arbitrary witness not satisfying `hi`, this substitution is unsound.

**4. Dominated convergence bound uses AE rank equality without integrability check (Mathematical Gap)**

The domination bound `hFb` filters over `[hMin, hRank]` where `hRank` is the AE statement `actualCorrelatedRank_eq_generic_ae B M`. The pointwise bound `finiteSpectrumOffsetError_nonneg_le_min_inverse` requires the rank condition `hzr` to hold. Since `hRank` is only almost-everywhere true, the domination inequality `‖F t z‖ ≤ (n : ℝ)*(actualCorrelatedEigenvalue B M i z)⁻¹` holds only almost-everywhere. This is sufficient for `tendsto_integral_filter_of_dominated_convergence`, which requires AE domination. **No gap here**—this is correctly handled.

**5. Integrability of `L` via domination (Potential Gap)**

The proof shows `Integrable L μ` by dominating it with `(n : ℝ)*(actualCorrelatedEigenvalue B M i z)⁻¹`, whose integrability follows from `hI.const_mul (n : ℝ)`. However, `hI` establishes integrability of the single term `(actualCorrelatedEigenvalue B M i z)⁻¹` under measure `μ`. The domination argument `hLb` shows `‖L z‖ ≤ n * (eigenvalue i z)⁻¹` almost everywhere. Applying `.mono'` requires the dominating function to be integrable—this is `hI.const_mul _`, which is correct. No gap.

**6. `offsetEqModes` uses `ht0` but is called inside integral context (Minor Concern)**

The lemma `offsetEqModes` requires `0 < t`. Inside the dominated convergence argument, it is applied with `t` satisfying `eventually_ge_atTop 1`, giving `0 < t` via `zero_lt_one.trans_le ht`. This is correctly handled. No gap.
