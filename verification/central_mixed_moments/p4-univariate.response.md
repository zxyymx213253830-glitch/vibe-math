# P4 Issues-Only Review

## ComplexGaussianMomentFunctional.lean

**1. Linearity vs multiplicativity (no issue).** Correctly declared as `→ₗ[ℂ] ℂ` and explicitly documented as not a ring homomorphism. The `map_add'` and `map_smul'` proofs properly use pointwise evaluation properties and integral linearity. No multiplicative structure is claimed or needed.

**2. Coefficientwise integration / polynomial evaluation commutation (no issue).** `complexGaussianIntegratedPolynomial_eval` correctly applies `map_sum`, then uses `map_smul` to commute the linear functional past scalar multiplication by `x^k`. The `mul_comm` + `ring` close is valid since `ℂ` is commutative. This establishes that coefficientwise application of the moment functional commutes with `eval₂` at scalars, which is exactly what's needed.

**3. Axiom surface.** Depends on whatever axioms underlie `integral_complexGaussian_polynomial`, `integrable_complexGaussian_polynomial`, and the imported moment infrastructure. The `#print axioms` calls are appropriate; no new axioms are introduced locally.

## CentralMinimumUnivariatePolynomial.lean

**4. Nested polynomial / Gram determinant (no issue).** `shiftedGramPolynomialInX` builds a univariate `Polynomial (ComplexMatrixPolynomial n n)` via `.det^d`. The `_eval` proof correctly uses `map_pow`, `e.map_det`, and entrywise `congr 2; ext i j` to reduce to the known `shiftedGramDeterminantPolynomial` definition. The `split_ifs <;> simp` handles diagonal/off-diagonal cases. This is a fixed univariate representation — no degree bound or original paper determinant identity is claimed.

**5. Real argument evaluation (no issue).** `x : ℝ` is coerced to `ℂ` via `(x : ℂ)` consistently in both `_eval` theorems. The final equality `centralRectangularMinimumPolynomial_eq_univariate` extracts `.re` after evaluation, which is type-correct.

**6. Composition chain (no issue).** The three theorems compose cleanly: `shiftedGramPolynomialInX_eval` feeds into `complexGaussianIntegratedPolynomial_eval` to yield `centralMinimumUnivariatePolynomial_eval`, which then rewrites the rectangular minimum polynomial. All definitional unfoldings align.

## Standing items (require human review)

**7. Measure/model interpretation.** Both files carry `[需人工审查]` markers. The formal chain from `centralMinimumUnivariatePolynomial` back to the actual probabilistic minimum law relies on imported correspondence theorems (`centralDeterminantPowerMoment`, `centralRectangularMinimumPolynomial`). This review confirms internal consistency of the two files but cannot validate the semantic adequacy of the underlying measure-theoretic model.

**8. No independent compilation.** Per instructions, no build was attempted. Axiom prints should be inspected against the project's trusted base.

**Summary:** No formal defects detected. Linearity is correctly scoped, coefficientwise integration commutes with evaluation as proven, nested determinant polynomial evaluation reduces properly, and real-to-complex coercion is consistent. The only open items are the flagged human-interpretation reviews of the imported probability infrastructure.
