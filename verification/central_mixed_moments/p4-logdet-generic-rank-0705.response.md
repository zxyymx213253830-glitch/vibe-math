# P4 Adversarial Review: `CorrelatedLogDetGenericRank.lean`

## Issues Only

### 1. Rank-Nullity Application to Non-Square/Rectangular Matrices
**`matrix_fromRows_rank_eq`**: The proof applies `finrank_range_add_finrank_ker` (h₁, h₂) which requires the linear map to be between finite-dimensional spaces. While `Fin n → ℂ` is finite-dimensional, the invocation of `linearMap_pair_rank` is not verified against its exact statement in Mathlib. If `linearMap_pair_rank` assumes specific dimension constraints or uses a different notion of rank (e.g., module rank vs. finrank), this step is unsupported. The `change` tactic at line 28 hides the actual type being manipulated—if the target expression doesn't definitionally match what `linearMap_pair_rank` produces, this is a **statement/proof scope mismatch**.

### 2. `omega` on Casted Naturals
The terminal `omega` call operates after `change` casts natural numbers to an arithmetic context. If any coercion from `ℕ` to the ambient type leaves residual non-linear terms or if `finrank` returns a value whose cast interacts poorly with `omega`'s decision procedure (e.g., involving `Int.ofNat` inequalities that `omega` doesn't normalize), this silently fails or masks a gap. No explicit `norm_cast` or `simp [Nat.cast_add]` is shown before `omega`.

### 3. Integrability / DCT Inheritance Gap
**`actualCorrelatedMatrixLogDet_prelog_generic_rank`**: The rewrite `rwa [he] at h` substitutes the integral of the rank for the limit value. This is only valid if `h` (from `actualCorrelatedMatrixLogDet_prelog_expected_rank`) has **exactly** the form `Tendsto (fun r => ... / log r) atTop (𝓝 (∫ rank))`. Any mismatch in the integrand's domain, measure, or the rank expression's coercion (`: ℝ` placement) makes `rwa` fail or silently match the wrong subterm. The proof does not display `h`'s type—this is a **hidden assumption**.

### 4. `integral_congr_ae` Requires Measurability and Integrability
The step `apply integral_congr_ae` followed by `filter_upwards [actualCorrelatedRank_eq_generic_ae B M]` assumes:
- The set where ranks differ is measurable (inherited, marked [需人工审查]).
- Both integrands are integrable w.r.t. `stdGaussian _`.
If the generic-rank expression `(min m (...): ℝ)` is treated as a constant function but the original rank integrand was only a.e.-defined or required a specific measurability proof not carried by `exact_mod_cast hz`, the integral equality is unsupported. The `simp` discharge at the end (`_ = _ := by simp`) must handle `measure_univ`, `volume_const`, and `ENNReal.toReal` correctly; if `stdGaussian` isn't normalized to total mass 1 in the inherited library, this simplification is wrong.

### 5. Zero-Dimension / Zero-Rank Edge Case in Limit
When `m = 0` or `p = 0` or `n = 0`, `min m (...) = 0`. The theorem asserts convergence to `0`. However, `actualCorrelatedMatrixLogDet` divided by `log r` as `r → ∞`: if the logdet is identically zero (empty matrix), the ratio is `0/∞ → 0`, which is fine. But if the inherited `actualCorrelatedMatrixLogDet_prelog_expected_rank` was proven only for positive dimensions or excludes the zero-rank case via a side condition, instantiating it here at zero is an **unsupported specialization**. The file header says "zero dimensions are intentional," but the imported theorem may not share that intent.

### 6. `simpa only [Nat.cast_add]` Insufficient for Stacked Variant
**`actualCorrelatedMatrixLogDet_prelog_stacked_rank`**: After `rw [matrix_fromRows_rank_eq]`, the goal becomes syntactically equal to `actualCorrelatedMatrixLogDet_prelog_generic_rank` only up to `Nat.cast_add`. But `generic_rank`'s conclusion wraps the entire `min m (B.rank + ...)` in `(: ℝ)`, while `stacked_rank` wraps `min m (fromRows.rank)` in `(: ℝ)`. The `simpa only [Nat.cast_add]` must also resolve `Nat.cast_min` or similar lemmas if `min` interacts with the cast. If `min` is taken in `ℕ` before casting vs. in `ℝ` after casting, these are different expressions. This is a potential **coherence error**.

### 7. Mean Subtraction / Witness Construction Not Visible
The review preamble states: *"For witness construction the term (psi-a|C) explicitly subtracts mean; transversality alone without that subtraction is invalid."* None of the three theorems displayed perform or reference mean subtraction. If `actualCorrelatedMatrixLogDet` internally relies on a centered Gaussian model where the mean-subtraction is elided at this layer but was required for the rank identity `actualCorrelatedRank_eq_generic_ae`, then the dependency is **hidden** and the correctness of the generic rank formula inherits that unverified precondition.

### 8. Complex vs. Real Measure Space Coherence
`ComplexSample (m := m) (n := p)` with `stdGaussian _`: the preamble notes CN1 source uses two standard real coordinates divided by √2. If `actualCorrelatedRank_eq_generic_ae` was proven under the real-coordinate representation but integration here is over `ComplexSample` with `stdGaussian`, the measure-theoretic identification (pushforward equivalence) is part of the inherited [需人工审查] block. A mismatch in normalization (√2 factor absorbed or not) would scale the logdet by a constant, breaking the prelog coefficient.

---

**Summary**: Primary risks are (1) hidden integrability/measurability preconditions in the `rwa` substitution, (2) cast/coherence gaps between `ℕ`-rank arithmetic and `ℝ`-valued limits, (3) zero-shape validity of the inherited expected-rank theorem, and (4) the mean-subtraction requirement being invisible at this interface layer. All polynomial null-set/Fubini/model-correspondence issues are acknowledged as inherited [需人工审查].
