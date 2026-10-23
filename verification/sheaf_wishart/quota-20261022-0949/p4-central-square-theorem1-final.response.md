# P4 Adversarial Review

## FactorialHankelDeterminant.lean

**Mathematical gap in `binomial_overlap_sum_fin`:** The identity $\sum_k \binom{i}{k}\binom{j}{k} = \binom{i+j}{j}$ is false as stated. The correct Vandermonde convolution is $\sum_k \binom{i}{k}\binom{j}{m-k} = \binom{i+j}{m}$. The proof attempts to bridge this via `Nat.add_choose_eq i.val j.val j.val` and antidiagonal reindexing, but the symmetry rewrite `Nat.choose_symm` at the end requires `k ≤ i.val`, which is not guaranteed for all `k : Fin n`. When `i.val < k`, the binomial coefficient $\binom{i}{k}$ is already zero, but the symmetry lemma application is invalid. This needs a case split or an explicit support restriction.

**API question:** `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` — confirm the exact statement matches the required index transformation.

## PolynomialMomentTranslation.lean

**Mathematical gap in `monic_polynomial_moment_det`:** The expansion `hp` writes `p i` as a sum over `Fin n`, which requires `natDegree p i < n`. The hypothesis `hd : ∀ i, (p i).natDegree = i.val` combined with `i : Fin n` gives `i.val < n`, so this is valid. However, the matrix multiplication `T * H * T.transpose` implicitly assumes the bilinear form structure. The linearity of `F` is used via `map_sum`, but `F` is only assumed to be a `ℂ`-linear map, not a ring homomorphism. The step `F(p i * p j) = ∑ ... F(X^(k+l)) ...` requires expanding the product of polynomials inside `F`, which is valid by linearity but the double-sum rearrangement needs `F` applied to each monomial term individually. This is correct but the `conv_lhs` block obscures where polynomial multiplication becomes scalar multiplication inside `F`.

**Not a gap but worth noting:** No conjugate transpose is used, consistent with the header comment.

## GammaFactorialMoment.lean

**Mathematical gap in `factorialMoment_shift_succ`:** The derivative formula `derivative ((X + C x)^(k+1)) = (k+1) • (X + C x)^k` is applied, then `factorialMoment_eval_derivative` yields the recurrence. The simplification relies on `eval 0` of `(X + C x)^(k+1)` being `x^(k+1)`. This is correct. However, the cast `(k+1 : ℕ) : ℂ` versus the factorial recursion `Nat.factorial_succ` needs careful tracking — the proof uses `ring` after pushing casts, which should close this, but the intermediate expression mixes `ℕ`-arithmetic with `ℂ`-arithmetic in a way that could hide a coercion mismatch if `ring` doesn't normalize both sides identically.

**Dependency question:** `upperGammaNat_succ` and `upperGammaNat_zero` are imported from `IncompleteGamma`. Their exact signatures matter: does `upperGammaNat_succ k hx` require `0 ≤ x` or `0 < x`? If the latter, the induction in `upperGammaNat_eq_factorialMoment` would fail at the boundary.

## Theorem1CentralSquare.lean

**Mathematical gap in `theorem1CentralSquare_candidate_eq_expCDF`:** The term `theorem1CentralSquare_PsiDet n 0 (by norm_num)` evaluates the determinant at `n = 0`. The matrix type becomes `Matrix (Fin 0) (Fin 0) ℂ`, whose determinant is `1` by convention. However, the right-hand side `(Real.exp 0 : ℂ) * ∏ i : Fin 0, ...` also equals `1`. The subtraction `1 - 1` in the candidate formula then gives `0`, but the goal states the result is `1 - Real.exp(-(n:ℝ)*x)`. At `n = 0` this is `1 - 1 = 0`, which is consistent. **But** the theorem is stated for general `n : ℕ` without the `0 < n` hypothesis, and the final division `mul_div_cancel_right₀ _ hDN` requires the denominator nonzero. When `n = 0`, the product over `Fin 0` is `1 ≠ 0`, so `hD` holds. This is actually fine.

**Actual gap:** In `theorem1CentralSquare_candidate_eq_actualCDF`, the right-hand side invokes `actualCentralSquare_minimum_CDF n hn x hx`, which is imported. The left-hand side has no probability measure, no integrability condition, and no assertion that the CDF formula applies to this specific parameter regime. The equality is purely algebraic on the left and probabilistic on the right; the semantic bridge is entirely in the imported lemma. If `actualCentralSquare_minimum_CDF` requires additional hypotheses (e.g., that the underlying measure is the standard complex Gaussian, that `n` matches the matrix dimension in the probability space), these must be verified to discharge correctly. The proof provides `hn : 0 < n` only here, not in the candidate-equals-exp version, suggesting the probabilistic interpretation genuinely requires positive dimension.

**API/signature question:** Confirm that `stdGaussian (ComplexSample (m := n) (n := n))` produces a measure on the same space where `centralSquareSampleMinimum n hn` is defined, and that `.toReal` is well-defined (i.e., the measure of the sublevel set is finite).
