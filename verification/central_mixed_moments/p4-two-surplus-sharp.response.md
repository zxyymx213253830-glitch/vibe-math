I've reviewed all six files in scope. No genuine semantic, dimensional, or logical gaps were found. Specific confirmations:

**(a) Dimensions/normalization/variance:**
- The `(N+2) × N` complex sample (variance-one, central) is consistently maintained. The final interface correctly uses `N = n+1`, yielding shape `(n+3) × (n+1)`.
- The normalization by `centralDeterminantPowerMoment 0 N 2 = ((N)!·(N+1)!)` in `CentralWishartMomentFactorials.lean` is algebraically consistent and correctly propagated through the complement reindexing.
- `N=1` scalar case: coefficients `1, 1, 1/2` match `Q(x) = 1 + x + x²/2` (Gamma shape-3 truncation), confirmed by `coeff_zero/one/two`.

**(b) Unsupported steps:** None detected.
- The degree-`|R|+|T|` monomial indexing (not union-cardinality) is explicitly defined in `centralComplementMinorPolynomial` and consistently used.
- Grouped parameters `r=|R|, h=|R∩T|, t=|T\R|` with degree `r+h+t` are correctly implemented in `complementCoefficientTerm`; the combinatorial reindexing via `sum_finsets_pair_cardinalities` (imported law) is properly instantiated.
- Finite truncation in `FiniteChooseTruncation.lean` uses exact binomial-zero support (`Nat.choose_eq_zero_of_lt`), not asymptotic cutoff.
- The cubic coefficient `N(N-1)(5N+2)/36` is derived deterministically in `CentralComplementCubic.lean` for all `N` including small cases (exhaustive `cases` on `N`).

**(c) Statement-proof mismatch:** None.
- `centralMinimumRealPolynomial_two_surplus_normalized` correctly identifies the normalized CDF polynomial with the complement polynomial via infinite evaluation agreement on `[0,∞)` — no circularity since the RHS is purely combinatorial.
- Coefficient extraction (`_coeff`) uses `Polynomial.coeff_C_mul` correctly.
- The hard-edge convolution yielding `CDF/x³ → N(N+1)(N+2)/36` and `density-core/x² → N(N+1)(N+2)/12` (factor-of-3 ratio) follows from the imported limit laws applied to the proved coefficient identity; the `linear_combination` arithmetic is consistent.

**Out of scope (correctly flagged as human-required):** inherited measure-theoretic interpretation, Fubini justification, variance-one model soundness, and the general-CDF-to-polynomial identification's probabilistic meaning. Within the formalized algebraic/combinatorial scope, the chain is gap-free.
