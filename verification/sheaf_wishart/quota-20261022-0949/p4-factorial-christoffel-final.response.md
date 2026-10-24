# P4 Adversarial Review

## FactorialLaguerreOrthogonality.lean

**1. Missing `factorialMomentFunctional` definition and linearity.** The entire file depends on an imported functional that is never shown. If it lacks ℂ-linearity, the expansion in `factorialLaguerre_moment_orthogonal` (using `map_sum`, `map_smul`) is unsound. This is not a mere API question—it is a hard semantic dependency: the proof bodies here are valid only if the functional is linear over ℂ.

**2. Coercion gap in `alternatingPolynomialSum`.** The hypothesis `hp : p.natDegree < n` is passed to `fwdDiff_iter_eq_zero_of_degree_lt`, which expects the iteration count to strictly exceed the degree. The `simpa` discharge of `(ascPochhammer ℂ j).natDegree < n` from `j < n` requires that `ascPochhammer ℂ j` has degree exactly `j`. This fact is not stated or proved here; it is silently assumed from the import. If the Pochhammer polynomial is defined differently (e.g., shifted or zero in edge cases), this step breaks.

**3. `hr` rewrite direction.** In `factorial_alternating_moment_sum`, the identity `((j+k).factorial : ℂ)/(k.factorial : ℂ) = (ascPochhammer ℂ j).eval ((k : ℂ)+1)` relies on `factorial_mul_ascPochhammer ℂ k j`. The `.symm` usage and `div_eq_iff` application assume the factorial quotient simplifies exactly to the rising factorial evaluation. This is mathematically correct for standard definitions but represents a fragile coupling: any nonstandard normalization in the imported Pochhammer definition would invert the identity.

**4. `mul_div_assoc` in sum congruence.** The rewrite `rw [mul_div_assoc, hr]` inside the sum implicitly reassociates `(-1)^(n-k) * C(n,k) * ((j+k)! / k!)` into a form where `hr` applies directly. Lean's ring solver handles this, but the step assumes no division-by-zero subtlety—already discharged by `Nat.factorial_ne_zero k`, so this is sound.

**5. Leading coefficient calculation.** `factorialLaguerre_coeff_top` uses `Finset.sum_eq_single n` and discards all `k ≠ n` terms. This is correct because `X^k` contributes to coefficient `n` only when `k = n`. No gap.

**6. Evaluation identity sign tracking.** In `factorialLaguerre_eval_neg`, the claim `(-1)^n * (-1)^(n-k) * (-1)^k = 1` via `pow_add` and `Nat.sub_add_cancel hkn` is arithmetically correct. The `neg_pow` application and subsequent ring closure are sound.

**No mathematical gaps found in the explicit proof bodies**, contingent on the imported functional being ℂ-linear and the Pochhammer polynomial having degree `j` with the standard rising-factorial semantics.

---

## ChristoffelMomentDeterminant.lean

**1. Critical index mismatch in `G` definition.** The functional array `G : Fin (n+1) → ...` is defined by `Fin.cases (Polynomial.leval z) (fun i => F.comp ...)`. Here `i : Fin n` (the tail), so `G 0 = leval z` and `G (succ i) = F ∘ mulLeft(X^i)`. But the matrix entries use `G i (Q j)` where both indices range over `Fin (n+1)`. The determinant expansion then mixes one evaluation row with `n` functional rows. This is **mathematically intentional** for Christoffel-type formulas, but the proof that the submatrix extraction works (`hminor`) must correctly identify which row/column carries the `leval z` term. The `det_succ_row_zero` and `det_succ_column` applications do handle this, but only because `Q 0 = 1` and `P last = p` are positioned to kill cross-terms. This is sound but extremely brittle—any shift in the `Fin.cases`/`Fin.lastCases` convention breaks it.

**2. `hdQ` degree proof incomplete in source.** The `simp [Q, Polynomial.natDegree_mul, (monic_X_sub_C z).ne_zero]` call assumes `natDegree (X^j * (X - C z)) = j + 1` reduces automatically. This requires `natDegree_mul` to fire, which demands both factors nonzero. `monic_X_sub_C z` gives `(X - C z) ≠ 0`, and `X^j ≠ 0` is trivial, but the `simp` set must contain these facts. If the imported library lacks the exact lemma form, this `simp` will stall. Not a logical error, but a real fragility.

**3. Orthogonality hypothesis scope.** `ho : ∀ i : Fin n, F (X^i * p) = 0` provides exactly `n` vanishing conditions. The determinant `det(F((X-Cz)*X^(i+j)))` expands into moments up to order `2n-1`. The proof uses `ho` only in `hP` via `simp [G, P, Polynomial.leval_apply, ho]` to kill terms involving `F(X^i * p)`. This is correct: the column expansion along `P` isolates `p` in the last slot, and `ho` zeroes out the appropriate cofactors. **No gap.**

**4. Sign factor `(-1)^n`.** Arises from `det_succ_column` expansion along the last column with `Fin.last n`. The parity is `(-1)^(n + n)` from row+column position, simplified. This is standard and correct.

**5. No measure-theoretic assumptions.** Correctly absent. The theorem is pure bilinear algebra over ℂ.

**No actual mathematical gaps.** The proofs are logically complete given the explicit hypotheses. The primary risk is definitional brittleness in the `Fin` indexing conventions, not a reasoning error.
