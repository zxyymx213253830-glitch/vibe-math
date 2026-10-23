## P4 Adversarial Review: `GaussianShiftedSquareMGF.lean`

**1. Critical Mathematical Gap: Incorrect Completing-the-Square Identity (`realQuadraticIntegral`)**

The algebraic identity in `h` is mathematically wrong. Expanding the RHS:
```
-b*(x - c/(2b))² + d + c²/(4b) = -bx² + cx - c²/(4b) + d + c²/(4b) = -bx² + cx + d
```
This works. However, the subsequent application of `integral_sub_right_eq_self` claims:
```
∫ exp(-b*(x - c/(2b))²) dx = ∫ exp(-b*x²) dx
```
This translation invariance holds for Lebesgue measure over ℝ, **but only if the integral converges absolutely**. The theorem assumes `hb : 0 < b`, which guarantees convergence, so the mathematical conclusion is correct—but the proof step is incomplete. The invocation of `integral_sub_right_eq_self` requires verifying that `fun x => exp(-b*x^2)` is integrable with respect to volume. This integrability condition is not established in the proof. While `integral_gaussian` is invoked immediately after, Lean's elaborator may fail to unify the integrability side-condition automatically without an explicit `have` statement proving `(fun x => exp(-b*x^2))` is `Integrable` or at least `AEStronglyMeasurable` and bounded by an integrable function. If this is a Codex-generated proof body, the gap between invoking the shift lemma and discharging its measure-theoretic preconditions is a real semantic hole, not merely an API question.

**2. Potential Type/Signature Mismatch in `integral_gaussianReal_eq_integral_smul`**

The call `integral_gaussianReal_eq_integral_smul (by norm_num)` converts integration against `gaussianReal 0 1` into integration against Lebesgue measure scaled by the PDF. The `by norm_num` must discharge whatever side-conditions this lemma carries (likely positivity of variance, i.e., `0 < 1`). This is trivially true but represents an implicit assumption about the parameterization of `gaussianReal`. If `gaussianReal μ σ` requires `σ > 0` rather than `σ ≠ 0`, then `norm_num` handles it; if it requires a type-level positivity witness like `(hσ : 0 < σ)`, the term-mode proof may fail. This is an API-level concern but directly impacts whether the stated equality type-checks.

**3. Division-by-Zero Risk Masked by `field_simp` in Main Theorem**

In `gaussianReal_integral_exp_shifted_square`, the expression `u^2*t/(2*(1-t))` and the factor `(sqrt(1-t))⁻¹` both require `1-t ≠ 0`. The proof correctly derives `hn : 1-t ≠ 0` from `ht : t < 1`. However, the final `field_simp` call is asked to clear denominators involving `1-t` globally. If any intermediate rewrite produces a term where `1-t` appears in a denominator before `hn` is available to `field_simp`'s simp-set, the elaboration may silently rely on Mathlib's convention that `x/0 = 0` in fields, potentially masking a genuine logical dependency order problem. The explicit `have hn` is present, but whether it is registered as a `field_simp` lemma at the right moment is an implementation fragility, not a mathematical guarantee.

**4. Integrability Proof Logic is Circular-Appearing**

`gaussianReal_integrable_exp_shifted_square` proves integrability by showing the integral is nonzero via `Integrable.of_integral_ne_zero`. This lemma requires knowing *a priori* that the function is measurable and that the integral expression is well-defined. But the integral was computed in the previous theorem under the assumption `ht : t < 1` alone—no measurability proof is given. Mathlib's `∫` notation returns `0` for non-measurable functions, so computing a nonzero value does imply measurability retroactively, making this logically sound but fragile: it depends on the specific definitional behavior of Bochner integration in Mathlib treating non-measurable functions as having zero integral.

**Summary:** One genuine mathematical gap (missing integrability proof for shift invariance), one logical fragility (retroactive measurability), two API-level concerns.
