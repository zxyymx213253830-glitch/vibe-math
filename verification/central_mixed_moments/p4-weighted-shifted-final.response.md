# P4 Mathematical Issues Review

## Issue 1: Incorrect scalar action in polynomial expansion lemmas

In all eight theorems, the `have he` expansion steps use `MvPolynomial.smul_eq_C_mul` to rewrite expressions like `(a i) • (MvPolynomial.X _)`. However, the left-hand side of `he` is a product of polynomials (e.g., `complexDirectLinearPolynomial a * complexConjugateLinearPolynomial c`), which lives in `MvPolynomial (ι ⊕ ι) ℂ`. The `simp only` calls also list `map_mul`, but `complexGaussianMomentLinear` is a **linear map**, not a ring homomorphism — `map_mul` should not apply to it. If `map_mul` refers instead to the internal definition of `complexDirectLinearPolynomial`/`complexConjugateLinearPolynomial` as linear maps, then listing it alongside `smul_eq_C_mul` in the same `simp` call conflates two different algebraic structures. Each `he` proof should be checked to confirm that `ring` alone (without `map_mul` in the simp set) closes the goal after proper expansion.

## Issue 2: Degree-3 moment references lack explicit odd-degree justification

The theorems `complexGaussianPolynomialMoment_weighted_direct_direct_conjugate` and `complexGaussianPolynomialMoment_weighted_direct_conjugate_conjugate` invoke `complexGaussianPolynomialMoment_direct_direct_conjugate` and `complexGaussianPolynomialMoment_direct_conjugate_conjugate` respectively. Per the dependency statement, "all odd degree 3 listed coordinate patterns have moment 0." These two lemmas are specific mixed-type instances. There is no issue if those imported lemmas are already proved for arbitrary finite `ι` (including empty), but the current file does not show whether they cover the case where `ι` is empty. For empty `ι`, the sums `∑ i, ...` are zero, and the polynomial products reduce to `0`, so L(0) = 0 by linearity — this is fine, but only if the referenced lemmas themselves handle empty types or if the `simp` chain reduces to `Finset.sum_const_zero` before invoking them. The `simp` calls do include `Finset.sum_const_zero`, but the `he` expansion produces a triple sum over `ι × ι × ι` which for empty `ι` is trivially empty, so the reference to the degree-3 lemmas is actually never reached. No bug, but the proof structure is slightly misleading: the `simp only [..., complexGaussianPolynomialMoment_direct_direct_conjugate, ...]` call lists lemmas that are dead code when `ι` is empty.

## Issue 3: `complexGaussianPolynomialMoment_weighted_pair` final simplification

After applying `complexGaussianPolynomialMoment_X_conj_X` (which gives `L(X_{inl i} * X_{inr j}) = if i = j then 1 else 0`), the expression becomes `∑ j, ∑ i, (a i * c j) * (if i = j then 1 else 0)`. The trailing `simp` must collapse the double sum to `∑ i, a i * c i`. This requires `Finset.sum_ite_eq` or equivalent. The dependency statement confirms "ac = ∑ aᵢcᵢ, no extra star," which matches. No mathematical error, but the bare `simp` at the end is doing nontrivial work — if `simp` fails to close this in some Lean configurations, an explicit `simp only [Finset.sum_ite_eq', Finset.sum_const_zero, add_zero]` would be more robust.

## Issue 4: Fourth-moment theorem (`weighted_shifted_fourth`) — coefficient matching

The RHS is `αβγδ + βδ(∑ aᵢcᵢ) + βγ(∑ aᵢdᵢ) + αδ(∑ bᵢcᵢ) + αγ(∑ bᵢdᵢ) + (∑ aᵢcᵢ)(∑ bᵢdᵢ) + (∑ aᵢdᵢ)(∑ bᵢcᵢ)`.

Per the dependency statement, the centered weighted fourth moment is `L(DₐD_bK_cK_d) = ac·bd + ad·bc` where `ac = ∑ aᵢcᵢ` (no conjugation). The expansion in `he` produces 16 terms. After applying linearity and the lower-degree lemmas:

- Constant term: `L(C(αβγδ)) = αβγδ` ✓
- Linear terms (U, V, W, Y): all vanish by `weighted_direct`/`weighted_conjugate` ✓
- Pure-direct pair `U*V` and pure-conjugate pair `W*Y`: vanish by `weighted_direct_pair`/`weighted_conjugate_pair` ✓
- Mixed pairs: `βδ · L(U*W) = βδ(∑ aᵢcᵢ)`, etc. ✓
- Fourth-order: `L(U*V*W*Y) = (∑ aᵢcᵢ)(∑ bᵢdᵢ) + (∑ aᵢdᵢ)(∑ bᵢcᵢ)` per `weighted_fourth` ✓

**No mathematical discrepancy.** The formula correctly implements `ac·bd + ad·bc` without any spurious conjugation on the coefficients.

## Issue 5: `hL` is definitionally `rfl` but used as a `simp` lemma

Every theorem includes `have hL (P) : complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl` and then `simp only [hL, ...]`. Since `hL` is `rfl`, this is just unfolding a definition. Not a bug, but `change complexGaussianMomentLinear _ = _` followed by `simp only [hL, ...]` is redundant — the `change` already replaces the goal. The `simp only [hL]` then immediately rewrites it back. This is harmless but indicates the proof was generated mechanically rather than minimally.

## Summary

**No substantive mathematical errors found.** The coefficient conventions match the stated dependencies (no extra stars, linear not multiplicative, ac = ∑aᵢcᵢ). Empty `ι` is handled correctly because all sums vanish and L(0)=0 by linearity. The only concerns are proof-engineering issues (redundant `hL`/`change` pattern, bare `simp` doing heavy lifting in the pair theorem, dead-code lemma references for empty types). These are not correctness blockers.
