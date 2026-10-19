# P4 Concrete Mathematical Issues Report

## 1. Factorial Multiplicity 2 Correct but Potentially Misleading

In `complexGaussianPolynomialMoment_fourth`, when all four indices coincide (a=b=c=d), the formula yields:
```
(if a=a ∧ a=a then 1 else 0) + (if a=a ∧ a=a then 1 else 0) = 2
```
This correctly matches `hm` which computes `∏ i, factorial(...) = if a=b then 2 else 1`. The factorial(2)=2 for the coincident case is properly captured. **No error here**, but the proof structure obscures that this "2" arises from two pairings of identical indices, not from an arbitrary coefficient.

## 2. Unmatched Index Argument in `monomial_unbalanced` is Sound

The theorem `complexGaussianPolynomialMoment_monomial_unbalanced` proves that total charge imbalance (sum of direct exponents ≠ sum of conjugate exponents) forces the moment to zero. The contrapositive argument (`by_contra hp`) correctly shows: if the product is nonzero, every index must have matching direct/conjugate exponents, forcing equal sums. **Mathematically correct.**

## 3. Shifted Fourth Moment Expansion: Missing Cross-Pairing Terms

**Critical issue.** The `complexGaussianPolynomialMoment_shifted_fourth` expansion lists 16 terms from `(U+α)(V+β)(W+γ)(Y+δ)`. After applying linearity and vanishing odd-moment theorems, the surviving terms are claimed to be:

- `α*β*γ*δ` (constant term)
- Four second-order terms: `(if a=c then 1)*β*δ`, etc.
- Two fourth-order pairing terms: `(if a=c ∧ b=d then 1)+(if a=d ∧ b=c then 1)`

**Problem:** The second-order terms are incomplete. When expanding the 16-term polynomial, terms like `U*W` (coefficient `β*δ`) give `E[Z_a * Z̄_c] = δ_{ac}`, which is captured. However, the expansion as written in `he` uses scalar multiplication `•` inconsistently with ring multiplication. The expression `δ • (U*V*W)` denotes `MvPolynomial.C δ * U * V * W`, which is a degree-3 monomial—correctly vanishing by the unbalanced/odd theorem. But the grouping of terms like `(γ*δ) • (U*V)` represents `C(γ*δ) * X(inl a) * X(inl b)`, which is a pure-direct pair and also vanishes. **The algebraic expansion itself is correct; no mathematical error in the 16 terms.**

## 4. Scalar Linearity Application is Valid

The proof uses `map_add` and `map_smul` on `complexGaussianMomentLinear`, then substitutes `hL : complexGaussianMomentLinear = complexGaussianPolynomialMoment` by `rfl`. This is valid **only if** `complexGaussianPolynomialMoment` is definitionally the linear functional. If it's merely provably equal, `change ... rw [hL]` would fail. The `rfl` suggests definitional equality. **No issue if compilation succeeds.**

## 5. Finite Index Type ι May Be Empty

When `ι` is empty (`Fintype.card ι = 0`), all products over `ι` equal 1, all sums equal 0. The monomial formula gives `c * ∏ i : ι, ... = c * 1 = c` for the zero polynomial, consistent with `complexGaussianPolynomialMoment_C`. The fourth moment theorem becomes vacuous (no elements `a,b,c,d : ι` exist). **Mathematically consistent, no error.**

## 6. No Novel Probability Claimed

Correct. These are algebraic consequences of the defined functional `L(P) = Σ coeff(d) * Π factorial(...)`, applied to multilinear polynomials. The Wick/fourth-moment formula `δ_{ac}δ_{bd} + δ_{ad}δ_{bc}` is classical Isserlis' theorem for complex Gaussians. **The formalization derives it from the functional definition, not from measure theory—appropriate for the stated scope.**

## Summary

**Zero concrete mathematical errors identified.** The factorial multiplicity 2, unmatched-index vanishing, shifted 16-term expansion, scalar linearity, and empty-index edge cases are all handled correctly within the algebraic framework. The caveat remains: this verifies identities about the *defined functional* `complexGaussianPolynomialMoment`; connection to actual Gaussian integration requires the previously-proved equivalence (referenced but not re-established here). Human review should confirm that `complexGaussianMomentLinear` and `complexGaussianPolynomialMoment` are indeed definitionally equal as used in `hL`.
