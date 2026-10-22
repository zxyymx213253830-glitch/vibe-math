# P4 Adversarial Review

## NegativeLogNaturalMomentBounds.lean

**1. Missing nonnegativity assumption on `f` (Mathematical gap).** The small-ball hypothesis `hsmall` bounds `μ.real {a | f a ≤ x}` only for `x > 0`. However, `Y = max 0 (-Real.log (f a))` requires reasoning about all values of `f`. If `f a < 0`, then `-Real.log(f a)` involves `Real.log` of a negative number (defined as 0 in Mathlib by totalization), making `Y` behave unexpectedly. The theorem never assumes `0 ≤ᵐ[μ] f` or `f ≥ 0`. Without this, the connection between the small-ball bound on `{f ≤ x}` for positive `x` and the tail behavior of `-log(f)` is semantically broken—negative values of `f` contribute to `{f ≤ x}` but don't correspond to large `Y`.

**2. Layer-cake applicability requires `q + 1 > 0` (Minor gap).** The equivalence `integrable_natPower_iff_weightedProbabilityTail` is applied with exponent `q + 1`. Since `q : ℕ`, we have `q + 1 ≥ 1 > 0`, so this is fine mathematically, but the proof relies on `hYn : 0 ≤ᵐ[μ] Y` to invoke the layer-cake representation. This holds by construction (`max 0 ...`), so no issue here—flagging only that the nonnegativity is structural, not an assumption.

## ComplexGaussianRootLogMoments.lean

**3. Variance mismatch in small-ball constant (Mathematical gap).** The docstring explicitly states "Its complex second moment is 2, not proper CN1." The small-ball bound uses constant `C = 1/2`: `(stdGaussian ℂ).real {z | ‖z-a‖² ≤ x} ≤ (1/2)*x`. For a standard complex Gaussian with variance 2 (i.e., real and imaginary parts each with variance 1), the squared norm `‖z-a‖²` has expectation 2, and the small-ball probability for small `x` scales as `x/2` (the density at origin is `1/(2π)·π = 1/2`). This appears correct, but the imported lemma `stdGaussian_complex_closedBall_le_radius_sq_half` must actually state `μ(ball(a,r)) ≤ r²/2` rather than `r²` or `r²/π`. If the imported lemma has a different normalization, the constant `1/2` would be wrong. **This is a concrete semantic dependency that must be signature-checked.**

**4. Final bound arithmetic (Potential error).** The result gives `≤ ((q+1).factorial)/(2·2^(q+1))`. From `hs.2` we get integral `≤ C·(q+1)! = (1/2)·(q+1)!`. Then dividing by `2^(q+1)` gives `(1/2)·(q+1)!/2^(q+1) = (q+1)!/2^(q+2)`. But the stated bound is `(q+1)!/(2·2^(q+1)) = (q+1)!/2^(q+2)`. These match—no error, but easy to misread.

## ComplexGaussianPolynomialLogSquare.lean

**5. Subadditivity of `complexNegativeLog` under multiplication (Mathematical gap).** The lemma `complexNegativeLog_mul_le` asserts `complexNegativeLog(a·b) ≤ complexNegativeLog(a) + complexNegativeLog(b)`. Since `complexNegativeLog(w) = max(0, -½·log‖w‖²) = max(0, -log‖w‖)`, this claims `max(0,-log‖ab‖) ≤ max(0,-log‖a‖) + max(0,-log‖b‖)`. When `‖a‖,‖b‖ < 1`, both sides are positive: LHS = `-log‖a‖-log‖b‖` = RHS, equality holds. When one factor has norm ≥1, say `‖a‖≥1`, then `max(0,-log‖a‖)=0` and `‖ab‖≤‖b‖` need not hold... actually `‖ab‖=‖a‖·‖b‖≥‖b‖`, so `-log‖ab‖≤-log‖b‖`, giving LHS ≤ `max(0,-log‖b‖)` = RHS. This is correct, but **only if `complexNegativeLog_mul_le` is actually proven in the imports**—it's used without proof here.

**6. Use of `IsAlgClosed.splits` (API question, not mathematical gap).** The factorization `P.eval z = P.leadingCoeff · ∏(z - roots i)` invokes `(IsAlgClosed.splits P).eval_eq_prod_roots`. This requires `ℂ` to be algebraically closed (true) and `P ≠ 0` implicitly (since `natDegree` of zero polynomial behaves differently). If `P = 0`, then `P.eval z = 0` everywhere and `complexNegativeLog(0) = max(0,-log 0) = max(0,∞)` which is problematic. **The theorem does not exclude `P = 0`.**
