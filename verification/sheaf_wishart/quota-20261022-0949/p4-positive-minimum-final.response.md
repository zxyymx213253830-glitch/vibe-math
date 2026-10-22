## P4 Adversarial Review

### FinitePositiveMinimum.lean

**1. Missing `Nonempty` guard on `Fin n` (Mathematical Gap)**

Both theorems quantify over `{n : ℕ} (f : Fin n → ℝ)`. When `n = 0`, `Fin 0` is empty. The first theorem takes `(i : Fin n)`, making the statement vacuously true but Lean's type theory requires inhabitation to even state it. The second theorem has the same issue. Add `[NeZero n]` or `[Fact (0 < n)]`, or explicitly handle `n = 0`.

**2. Antitone direction ambiguity (Potential Semantic Mismatch)**

Mathlib's `Antitone f` means `a ≤ b → f b ≤ f a` (descending). The first theorem's forward direction uses `hi.trans_le (hf (Finset.mem_Iic.mp hj))` where `hj : j ≤ i`, so `hf` yields `f i ≤ f j`, giving `0 < f i ≤ f j`. This is correct for descending order. However, the second theorem's conclusion `f i ≤ f j` for all positive `j` claims `f i` is the **minimum** positive value. For a descending sequence, the minimum positive entry sits at the **largest** index among positive entries—this is consistent only if the eigenvalue ordering in the dependent file is also descending. Verify that `eigenvalues₀_antitone` matches this convention exactly; an ascending eigenvalue ordering would invert the result.

**3. `omega` fragility with `Fin` coercion (Minor)**

The proof `change j.val ≤ i.val; omega` relies on implicit `Fin.val` bounds. If `n = 0` slips through, `omega` may fail to close goals involving `Fin 0` arithmetic since no inhabitants exist. Related to point 1.

---

### FixedRankPositiveMinimum.lean

**4. Subtraction underflow in `Fin` construction (Mathematical Gap)**

```lean
let i : Fin (Fintype.card (Fin n)) := ⟨R-1, by dsimp [R] at *; omega⟩
```

`R` is defined as `min m (Matrix.fromRows B M).rank`. The hypothesis `hR : 0 < R` ensures `R ≥ 1`, so `R - 1` is well-defined in `ℕ`. However, the proof that `R - 1 < Fintype.card (Fin n)` (i.e., `R ≤ n`) uses `hRn : R ≤ Fintype.card (Fin n)`. The `omega` call must discharge `R - 1 < n` from `R ≤ n` and `0 < R`. This works for `R ≥ 1` but is fragile: if any upstream definition changes `R`'s type or the `min` expression, the `dsimp` may not reduce as expected. Make the inequality chain explicit.

**5. `gram_positive_modes_card_eq_rank` depends on unstated spectral theorem (Dependency Signature Question)**

The lemma equates the count of strictly positive eigenvalues of `complexGram_posSemidef X` to `X.rank`. This implicitly requires that the Gram matrix is diagonalizable with real nonneg eigenvalues and that algebraic multiplicity equals the rank. These are standard facts for positive semidefinite Hermitian matrices, but the proof calls `gram_positive_modes_eq_rank` as a black box. Confirm that `gram_positive_modes_eq_rank` does **not** assume full column rank or `m ≤ n`; otherwise `hR` alone doesn't prevent a dimension mismatch when `m > n` and rank saturates at `n`.

**6. AE transport without sample-space positivity constraint (Scope Clarification)**

The theorem concludes `∀ᵐ z, 0 < actualCorrelatedEigenvalue B M i z ∧ ...` using `actualCorrelatedRank_eq_generic_ae`. The `filter_upwards` correctly transports the AE equality. However, the minimum-positive-eigenvalue property is only established **on the AE set where rank equals R**. Off this set (measure zero), no claim is made—this is fine per the docstring ("no all-sample positive-minimum selector claimed"), but reviewers should note the conclusion is not a deterministic structural fact about `B, M`; it is purely stochastic.

**7. No uniformity over `B, M` (Explicit Non-Claim Confirmed)**

The existential `∃ i` depends on `B, M` through `R`. There is no claim of a single coordinate working uniformly across matrix pairs. This is correctly scoped.
