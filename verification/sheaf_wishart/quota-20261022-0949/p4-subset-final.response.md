## P4 Adversarial Review

### FiniteSubsetFunctionSum.lean

**1. Surjectivity gap in fiber equivalence construction.** In `permutation_injective_image_fiber_equiv`, the surjectivity proof of `F` constructs `E' : Fin q ≃ S.val` via `Equiv.ofBijective g ⟨hg, hg.surjective_of_finite e⟩`. The term `hg.surjective_of_finite e` appears to pass an equivalence `e` where a finiteness instance is expected. If this is not a valid coercion or instance resolution, the surjectivity claim for `g` (and hence bijectivity of `F`) is incomplete. This is a concrete proof gap, not merely an API question—the logical step from "injective function between finite sets" to "bijection" requires explicit cardinality equality or a valid finiteness witness.

**2. Empty type edge case (q = 0).** When `q = 0`, `Fin 0` is empty. The definition `cardinalSubsetEnumeration` produces `Fintype.equivOfCardEq` on an empty subtype. The permutation group `Equiv.Perm (Fin 0)` has exactly one element. The fiber over the unique empty subset should be a singleton, and `0.factorial = 1`, so the theorem statements remain true. However, the proof's construction of `g` and invocation of `surjective_of_finite` on an empty domain may require degenerate-case reasoning that is not explicitly discharged. This is a minor verification gap, not a mathematical error, but it could cause the proof to fail at `q = 0` without additional simp lemmas.

### SubsetCauchyBinet.lean

**3. Missing dependency: `det_mul_rectangular_factorial_sum_functions`.** The theorem `det_mul_rectangular_sum_cardinal_subsets` invokes `det_mul_rectangular_factorial_sum_functions` via `rw [← det_mul_rectangular_factorial_sum_functions] at hg`. This lemma is not defined in the supplied sources. It is listed as an imported dependency from `AveragedCauchyBinet`. Per instructions, imported results are treated as separately checked, but note: if that lemma carries side conditions (e.g., `q ≤ m` or positivity), they must be satisfied here. The current source does not make such assumptions explicit, so any hidden precondition in the imported lemma would constitute a semantic mismatch.

**4. Cancellation at q = 0.** The step `mul_left_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero q)) hg` is valid for all `q : ℕ` since `0! = 1 ≠ 0`. No gap.

**5. `complexGram` undefined in supplied sources.** The term `complexGram B` in `gram_det_sum_squared_cardinal_minors` is not defined here. Treated as an imported dependency. No intrinsic issue, but the correctness of the statement depends on `complexGram B` being definitionally `B.conjTranspose * B` (or equivalent) for the `simpa` step to close.

### GramAllMinorCoefficient.lean

**6. Polynomial coefficient extraction assumes standard identity.** The rewrite `Matrix.coeff_det_one_add_X_smul_eq_sum_minors` is imported. This is the characteristic-polynomial/minor expansion identity. No gap if the import is correct, but this is the sole point where polynomial algebra enters; all other files are purely finite-combinatorial.

**7. Double sum indexing—no overcounting.** The final expression sums over both `T` (column subsets) and `S` (row subsets). Each pair `(S, T)` contributes `|det X_{S,T}|²`. This is mathematically correct for the coefficient of `t^q` in `det(I + t X^H X)`. No combinatorial factor is missing because each submatrix is enumerated exactly once per subset pair.

**8. Real-part extraction is sound.** The simplification `Complex.mul_re, Complex.star_def, Complex.normSq_apply` correctly reduces `Re(z̄ · z)` to `|z|²`. No gap.

### Summary

- **Actual gaps:** (1) suspicious surjectivity argument syntax/semantics; (3) unverified imported lemma preconditions.
- **Edge cases needing attention:** (2) `q = 0` degeneracy in equivalence construction.
- **No stochastic/analytic assumptions detected or required.** All claims are finite algebraic identities.
