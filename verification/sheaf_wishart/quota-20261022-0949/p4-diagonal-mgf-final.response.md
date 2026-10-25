## P4 Adversarial Review

### GaussianWeightedSquareMGF.lean

**1. Missing nonnegativity constraint on `t` (Mathematical Gap)**

The hypothesis `ht : ∀ i, t i < 1` permits negative values of `t i`. The standard Gaussian integral identity `∫ exp(t·x²/2) dγ = (1-t)^{-1/2}` requires `t < 1` but the convergence and the formula's validity for **negative** `t` depends on the specific definition of `gaussianReal_integral_exp_shifted_square`. If that imported lemma assumes `0 ≤ t i` or proves convergence only for `t i ∈ [0,1)`, then applying it here with potentially negative `t i` is unsound. The statement does not restrict `t i ≥ 0`, so either the dependency must handle all `t < 1` (including negative), or this theorem has a gap.

**2. Empty index type `ι` edge case (Minor Gap)**

When `ι` is empty, both sides reduce to trivial values (empty product = 1, empty sum = 0, integral over singleton = 1). This works, but `integral_fintype_prod_eq_prod` must be valid for empty types. Not a serious issue unless that lemma has a hidden nonemptiness assumption.

**3. Integrability proof strategy (Logical Concern)**

`gaussianPi_integrable_exp_weighted_shifted_squares` uses `Integrable.of_integral_ne_zero`. This principle states that if the integral exists and is nonzero, the function is integrable. However, this requires knowing **a priori** that the integral is well-defined (not `⊤` or undefined). The computation in `gaussianPi_integral_exp_weighted_shifted_squares` shows the integral equals a finite positive quantity, but Lean's `∫` notation returns `0` for non-integrable functions in some measure-theoretic setups. Circular reasoning risk: you need integrability to guarantee the integral computation is valid, but you're using the computed value to prove integrability.

---

### ActualDiagonalGramMGF.lean

**4. Division by 2 convention mismatch (Potential Mathematical Error)**

In `sample_gram_diagonal`, the identity `(complexGram ... j j).re = ∑ i, (z((i,j),0)² + z((i,j),1)²)/2` includes a factor of `1/2`. This propagates through `weighted_gram_coordinates` into the parameter `t a := v a.1.2` applied to `(x a + u a)²/2`. The imported theorem from GaussianWeightedSquareMGF expects the form `exp(∑ t_i · (x_i + u_i)² / 2)`, which matches. However, verify that `complexSampleMatrix` normalization (with `√2` scaling) is consistent with this `1/2` factor throughout. A missing or double-counted `1/2` would corrupt the MGF formula.

**5. Pushforward measurability assumptions (API Question with Semantic Impact)**

`rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]` asserts that `complexSampleMatrix_add_mean` induces a measurable map pushing forward `stdGaussian` to the product Gaussian measure. The `fun_prop` calls are opaque; if `complexSampleMean` is not affine/measurable or the spaces don't align, this rewrite silently fails. This is not just API hygiene—it's a semantic requirement that the coordinate decomposition preserves the measure structure.

**6. Norm squared vs. real square in exponent (Mathematical Gap)**

The final answer contains `‖M a.1 a.2‖²` while the intermediate `he` proof uses `RCLike.norm_sq_eq_def` to convert `(u a)²` terms. But `u a = complexSampleMean M a` extracts real or imaginary parts separately (indexed by `Fin 2`). The sum over `Fin 2` should reconstruct `‖M_{ij}‖² = Re(M_{ij})² + Im(M_{ij})²`. The algebra in `he` claims this via `field_simp; ring` after expanding definitions—verify that no factor of 2 or `√2` is lost in this reconstruction given the `complexSampleMean` definition.

**7. Same integrability circularity as above**

`actualNoncentralDiagonalGram_integrable_exp` uses identical `of_integral_ne_zero` logic with the same concern from point 3.
