## P4 Adversarial Review: `SeparableInverseMomentTransport.lean`

### 1. Critical Mathematical Gap: Backward Direction Bound is Reversed

The theorem claims integrability of `(f z)⁻¹^p` is **equivalent** to integrability of `(g x)⁻¹^p`. The backward direction (· intro hgi) attempts to bound `(f z)⁻¹^p` using the hypothesis `f z ≤ K z.2 * g z.1` (from `hz.2.2.1`).

**This is mathematically backwards.** From `f ≤ K * g`, we get `f⁻¹ ≥ (K * g)⁻¹ = K⁻¹ * g⁻¹`, hence `f⁻¹^p ≥ K⁻¹^p * g⁻¹^p`. This provides a **lower** bound on `f⁻¹^p`, not an upper bound. You cannot deduce integrability of a larger function from integrability of a smaller one.

To obtain an **upper** bound on `f⁻¹^p`, you need a **lower** bound on `f`. The hypothesis `g z.1 ≤ K z.2 * f z` (i.e., `f ≥ g / K`, from `hz.2.2.1`'s companion `hz.2.2.2`... wait, let me re-read the conjunction structure):

The bound hypothesis is: `g z.1 ≤ K z.2 * f z ∧ f z ≤ K z.2 * g z.1`. So:
- `g ≤ K * f` gives `f⁻¹ ≤ K * g⁻¹` — this is what `inversePowerBound` needs and uses correctly with `hz.2.2.1`.
- `f ≤ K * g` gives `g⁻¹ ≤ K * f⁻¹` — used in the forward direction.

Actually, re-examining: `inversePowerBound (f z) (g z.1) (K z.2) p hz.1 hz.2.1 (hK z.2) hp hz.2.2.1` requires `hb : g z.1 ≤ K z.2 * f z` as its 5th argument. The arguments are `(F G D p hF hG hD hp hb)` where `hb : G ≤ D * F`. Here `F = f z`, `G = g z.1`, `D = K z.2`, so `hb` should be `g z.1 ≤ K z.2 * f z`, which is `hz.2.2.1`. **This is correct.**

I retract this objection — the bound direction is valid. My initial reading swapped the roles. **No gap here.**

### 2. Actual Gap: `prod_left_ae` Application Type Mismatch

In the forward direction, `hfi.prod_left_ae` asserts that for ν-a.e. y, the function `x ↦ (f(x,y))⁻¹^p` is μ-integrable. Then `.and hs` combines this with `hs`. The `.exists` extracts a single `y` satisfying both.

**Problem:** `hfi` has type `Integrable (fun z => (f z)⁻¹^p) (μ.prod ν)`. The method `prod_left_ae` yields `∀ᵐ y ∂ν, Integrable (fun x => (f x, y)⁻¹^p) μ`. But `hs` already has `∀ᵐ y ∂ν, ...`. The `.and` of two `∀ᵐ` statements is fine, and `.exists` on a probability space with a nonempty ae-set is valid. **However**, the conclusion then fixes this `y` and uses `(K y)^p` as a constant multiplier. The integrability of `g⁻¹^p` must not depend on the choice of `y`, but the bound obtained is `g(x)⁻¹^p ≤ (K y)^p * f(x,y)⁻¹^p` for this **specific** `y`. Since the right side is μ-integrable (for this fixed y), the left side is μ-integrable. **This is logically valid** — no gap.

### 3. Minor API Question (not a mathematical gap)

`Measure.ae_ae_of_ae_prod` combined with `measurePreserving_swap` is used to convert `∀ᵐ z ∂μ.prod ν` into `∀ᵐ y ∂ν, ∀ᵐ x ∂μ`. This requires the swap map to be quasi-measure-preserving, which holds for probability measures. The application appears correct given `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`.

### 4. No Issues Found

After careful re-reading, the proof logic is sound. Both directions use the correct inequality from the conjunction, `inversePowerBound` is applied with matching hypotheses, and the Fubini/sectioning argument is valid for probability measures.
