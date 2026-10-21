# Finite-N Induction Route Review

## Current Position

You have:
- Univariate complex polynomial absolute-log integrability under `stdGaussian ℂ` (including zero poly via `Real.log 0 = 0`)
- Bivariate nested case completed
- Section helper (`integrable_polynomial_section_negativeLog`) giving parameterized univariate bound with explicit coefficient L1 assumption
- Real null-set induction for multivariate polynomials (volume-zero, not integrability)

Target: `∀ n, ∀ P : MvPolynomial (Fin n) ℂ`, integrability of `max 0 (-log ‖eval x P‖)` under `Measure.pi (fun _ => stdGaussian ℂ)`.

---

## Induction Structure on `n`

**Base `n = 0`:** `MvPolynomial (Fin 0) ℂ ≃ ℂ`. Constant polynomial. Requires `Integrable (fun _ : Unit => max 0 (-log ‖c‖))` which is trivial since the space is a point. This works but needs the identification `Measure.pi (fun _ : Fin 0 => stdGaussian ℂ) = pure ()`. **[需人工审查]** Measure normalization on empty product.

**Base `n = 1`:** Your univariate theorem. Done.

**Inductive step `n → n+1`:** Use `MvPolynomial.finSuccEquiv ℂ n P` to view `P` as `Polynomial (MvPolynomial (Fin n) ℂ)`. Split into leading coefficient `r : MvPolynomial (Fin n) ℂ` and fiber polynomials.

---

## Missing Lemmas (Precisely Identified)

### 1. Degree-Dropping Fiber Integrability

When you write `P = Σ i, c_i * X_n^i` with `c_i : MvPolynomial (Fin n) ℂ`, the inductive hypothesis applies to each `c_i` **only if** you know `c_i ≠ 0` implies integrability for fewer variables. But:

- The section helper requires `Integrable (fun a => complexNegativeLog (P a).leadingCoeff) μ` as an **assumption**. In the induction, this becomes: you need the `n`-variable integrability of the leading coefficient `r` to feed the `(n+1)`-variable section theorem.
- **Missing lemma:** If `P : MvPolynomial (Fin (n+1)) ℂ` and `r = leadingCoeff (finSuccEquiv P)`, then `Integrable (complexNegativeLog ∘ eval r) (pi^n)` must follow from the inductive hypothesis applied to `r : MvPolynomial (Fin n) ℂ`. This is fine **unless** `r = 0`, but `r ≠ 0` when `P ≠ 0` by `finSuccEquiv` injectivity and `leadingCoeff_ne_zero`.
- **Degree drop problem:** `natDegree (finSuccEquiv P)` might be less than expected if cancellation occurs after evaluation at `y : Fin n → ℂ`. You need `∀ᵐ y, natDegree (map (eval y) q) ≤ D` for some uniform `D`. The real null-set proof uses `hqEval_ne` outside the exceptional set — but "exceptional set is null" gives you **ae**, not a uniform degree bound.

**Gap:** No lemma providing a **uniform almost-everywhere degree bound** for the fiber polynomial `map (eval y) q` in terms of data from `q` alone. The section helper takes `D` and `hDegree : ∀ᵐ a, natDegree ≤ D` as inputs; constructing this `D` for the inductive step is missing.

### 2. The `P = 0` / `n = 0` Edge Cases

- `P = 0`: Under `Real.log 0 = 0` totalization, `complexNegativeLog 0 = 0`, so integrand is identically 0. Trivially integrable. But your section helper uses `(P a).leadingCoeff` — for `P = 0` this is `0`, and `complexNegativeLog 0 = 0` by convention, so it works **only if** your univariate theorem actually covers `P = 0` with that convention. Verify this explicitly.
- `n = 0` with `P ≠ 0`: constant nonzero, integrand is constant, probability space, done.

### 3. Product-Measure Equivalence and Circularity

The section helper concludes integrability under `μ.prod (stdGaussian ℂ)`. The inductive target is `Measure.pi (fun _ : Fin (n+1) => stdGaussian ℂ)`.

- **Required equivalence:** `Measure.pi (fun _ : Fin (n+1) => stdGaussian ℂ) = (Measure.pi (fun _ : Fin n => stdGaussian ℂ)).prod (stdGaussian ℂ)` up to the measurable equivalence `MeasurableEquiv.piFinSuccAbove`.
- Your real null-set proof uses `Measure.volume_eq_prod` and `volume_preserving_piFinSuccAbove`. The Gaussian analogue would be `Measure.pi_eq_prod` for finite products plus measure-preservation of `piFinSuccAbove` under Gaussian measures.
- **Potential circularity:** If you prove the `(n+1)`-variable integrability by invoking the section helper (which itself uses Fubini/Tonelli for `μ.prod ν`), and the section helper's own proof uses `integrable_prod_iff` which depends on the product σ-algebra structure matching `pi (Fin (n+1))`, you need the measurable equivalence to transport between these **before** applying the helper. No circularity if done in order: (a) establish measure equivalence, (b) apply section helper, (c) transport back. But if the section helper's internal Fubini call implicitly assumes the same structural fact you're trying to prove for `n+1`, that's circular.

**[需人工审查]** Verify that `Mathlib.MeasureTheory.Integral.Prod`'s `integrable_prod_iff` and `integral_prod` are stated for abstract `μ.prod ν` and don't require re-proving product structure for `pi (Fin (n+1))` each time.

### 4. From `max 0 (-log ‖·‖)` to Absolute Log

Your section helper bounds `complexNegativeLog` which is `max 0 (-log ‖·‖)`. The target is `|log ‖eval P‖|` integrability. You need both:
- Upper tail: `max 0 (-log ‖P‖)` integrable (what you have)
- Lower tail: `max 0 (log ‖P‖)` integrable

For the lower tail, `log ‖P(x)‖ ≤ ‖P(x)‖` for large values, and polynomial growth under Gaussian is always integrable. **Missing lemma:** `Integrable (fun x => max 0 (log ‖eval x P‖)) (pi^n)` for any multivariate polynomial. This should follow from moment bounds but isn't stated yet.

---

## Smallest Next Target

**Prove the uniform-degree-bound lemma for fibers:**

Given `q : Polynomial (MvPolynomial (Fin n) ℂ)` with `q ≠ 0`, produce `D : ℕ` and show `∀ᵐ y ∂(pi^n), natDegree (Polynomial.map (eval y) q) ≤ D`. Take `D = q.natDegree`. The failure set is `{y | leadingCoeff q evaluates to 0 at y}`, which is null by the inductive hypothesis (applied to the leading coefficient as an `n`-variable polynomial, using that it's nonzero). This closes the gap between the section helper's interface and what induction provides.

Immediately after that, **prove `P = 0` case separately** (one line under log0=0) to avoid polluting the generic argument with zero-polynomial edge conditions.

Then assemble: `n → n+1` by (a) handle `P=0`, (b) get `D` and ae-degree-bound from above, (c) get leading-coefficient integrability from IH, (d) apply section helper, (e) transport via `piFinSuccAbove` measure-preservation, (f) add lower-tail lemma for absolute value.

---

## Summary of Human-Review Flags

- **[需人工审查]** Empty product measure normalization (`n=0`).
- **[需人工审查]** Product-measure transport `pi (Fin (n+1)) ↔ pi (Fin n) .prod stdGaussian` via `piFinSuccAbove` — confirm Mathlib has `MeasurePreserving` instance for Gaussian, not just Lebesgue volume.
- **[需人工审查]** Fubini/Tonelli application inside section helper doesn't create induction circularity when the base measure `μ` is itself a Gaussian product.
- **[需人工审查]** `Real.log 0 = 0` convention propagation through `complexNegativeLog` and all existing univariate proofs — confirm no hidden `≠ 0` side conditions.
