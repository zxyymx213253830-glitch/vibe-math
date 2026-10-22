# P4 Adversarial Review

## GaussianPolynomialSectionLogSquare

**1. Fubini direction mismatch (actual gap).** The final `rw [integral_prod g hi]` rewrites the product integral into an iterated integral over `a` then `z`. However, `hinner` establishes integrability of `a ↦ ∫ z, ‖g(a,z)‖`, which is the *other* iterated direction. Tonelli/Fubini requires the outer variable's integrability to be established first. The proof uses `integrable_prod_iff` correctly for `hi`, but the final rewrite direction may not match what `hinner` actually provides.

**2. Pointwise bound scope.** `hpoint` applies `stdGaussian_complex_polynomial_negativeLog_sq` for every `a`, but this imported theorem presumably requires the polynomial to have bounded degree and square-integrable leading coefficient. The hypothesis `hCoeff` is a global integrability condition on `α`, not a pointwise bound for each `a`. The step `filter_upwards [hDegree] with a ha` handles degree, but no corresponding filter handles pointwise leading-coefficient control—only its `μ`-integral.

## FiniteGaussianPolynomialLogSquare

**3. Induction: `natDegree_map_le` misuse.** The line `ae_of_all _ (fun _ => Polynomial.natDegree_map_le)` asserts `∀ a, (Polynomial.map (MvPolynomial.eval a) q).natDegree ≤ q.natDegree`. This is mathematically correct (evaluation can only lower or preserve degree), but `Polynomial.natDegree_map_le` as stated in Mathlib typically requires no hypotheses, so this should work. **No gap here**, but worth verifying the exact lemma name exists.

**4. Zero polynomial branch.** When `P = 0`, the proof does `simp [complexNegativeLog]`. This relies on `complexNegativeLog 0 = 0` by definition. If `Real.log 0 = 0` is the convention (as stated in the docstring), this is consistent, but the integrability claim becomes `Integrable (fun _ => 0)`, which is trivially true. **No gap**, provided the definition matches.

**5. `real_log_sq_le_nonnegative_square` is purely deterministic algebra.** No measure-theoretic content; the inequality itself is sound given `hu : 0 ≤ u`.

## ProperGaussianPolynomialLogSquare

**6. Scaling variance mismatch (potential semantic gap).** The docstring states "Both real coordinates scale by 1/sqrt2," but the code defines `s := (Real.sqrt 2)⁻¹` and applies it as `fun i => s • x i` where `x : ι → ℂ`. This scales the *complex* coordinate by `1/√2`, which scales *each real component* by `1/√2` only if scalar multiplication distributes over real/imaginary parts uniformly. This is correct for `ℂ` as a real vector space, but the phrase "physical variance" in the review tag suggests the author should verify that `standardComplexPiLaw` actually corresponds to variance-1 proper complex Gaussians after this rescaling.

**7. `integrable_map_measure` direction.** In `properComplex_pi_polynomial_log_sq_integrable`, the proof uses `.mpr` on `integrable_map_measure`, going from integrability under the pushforward to integrability under the source. But `hscale.measurable.aemeasurable` must exactly match the map used in `standardComplexPiLaw_eq_planarMap`. If that equivalence involves additional structure (e.g., a measurable embedding rather than just a measurable map), the `.aemeasurable` projection might lose information needed for the reverse direction.

## ActualComplexPolynomialLogSquare

**8. Matrix dimension independence.** The theorem `integrable_actualAffineCompressedDet_log_sq` takes arbitrary `m p n q` with matrices `B : p × n`, `M : m × n`, `L : q × m`, `H : n × q`. The product `L*(z*B + M)*H` yields a `q × q` matrix. No rank or dimensional compatibility assumption beyond type-checking is stated. The result holds even when `q > min(m,p,n)` (where the determinant is identically zero), because `Real.log 0 = 0` makes the integrand vanish. **No gap**, but the theorem is vacuously trivial in degenerate dimensions.

**9. `entryAffineCompressedDet_eval` dependency.** The entire compressed-determinant result reduces to the holomorphic polynomial case via this single rewrite. If that lemma has side conditions (e.g., requiring the affine map to be expressible as a polynomial evaluation without remainder), they are invisible here. This is an imported dependency—treat as separately checked per instructions—but the semantic alignment between "affine compressed determinant" and "polynomial evaluation" should be confirmed at the signature level.
