# P1 Route Criticism

## Normalization/Index/Sign Gaps

**Index shift is the primary gap.** Your candidate uses `upperGammaNat(2*n-(i+1)-(j+1), x)` with `Fin n` indices (0-based). The Hankel reversal gives moments `H_x(i+j)` where the natural index sum runs over `{0,...,2n-2}`. But `upperGammaNat(k,x)` as defined equals `k! * exp(-x) * Σ(a=0..k) x^a/a!`, which is the *complementary* incomplete gamma only when `k` is a non-negative integer. You need to verify that `2*n-(i+1)-(j+1) ≥ 0` for all `i,j ∈ Fin n`. At `i=j=n-1` this gives `2n - 2n = 0`, so it barely closes—but the map from reversed-index Hankel `(i+j)` to your argument `2n-2-i-j` must be made explicit as an anti-diagonal reflection, not just asserted.

**Sign of the determinant ratio.** `det H_x = exp(-n*x) * det H_0` is correct algebraically. Since `T(x)` is lower unit triangular, `det T = 1`, and the factorization `H_x = exp(-x)·T·H_0·T^T` gives `det H_x = exp(-n*x)·(det T)^2·det H_0 = exp(-n*x)·det H_0`. No sign issue here because `det H_0 = ∏(i!)^2 > 0`. However, your candidate formula is `1 - ||det Ψ(x)||/||det Ψ(0)||`. If `Ψ` is exactly the Hankel matrix after reversal, then `det Ψ(x)/det Ψ(0) = exp(-n*x)`, giving CDF `1 - exp(-n*x)`. **The gap is confirming that `Ψ` after row-and-column reversal is literally `H_x`, not a signed permutation away from it.** A double reversal is a conjugation by the exchange matrix `J` with `det J = (-1)^{⌊n/2⌋}`, which cancels in the ratio—so this is fine, but must be stated.

**Normalization at x=0.** `upperGammaNat(k, 0) = k!` matches `H_0(i+j) = (i+j)!` only under the correct index identification. Pin this down explicitly.

## Smallest Reusable Finite Identity

For the translation step `H_x = exp(-x)·T·H_0·T^T`, the core obligation is:

```
Σ_{a=0}^{i} Σ_{b=0}^{j} choose(i,a)·choose(j,b)·x^{i+j-a-b}·(a+b)! = exp(x)·(something yielding H_x structure)
```

But since you already have `upperGammaNat_eq_finite` and the factorization is purely algebraic, the smallest missing identity is simply the **binomial convolution for factorial moments**: `(i+j)! = Σ_k choose(i,k)·choose(j,k)·k!·(i+j-k)!` or equivalently the statement that `P·P^T` with `P_{ik} = choose(i,k)` satisfies `H_0 = D·P·P^T·D`. This is Vandermonde-type and likely follows from `Nat.add_choose_eq` / antidiagonal splitting already pinned. Verify that this single convolution closes the `H_0 = D·P·P^T·D` factorization without needing a named Pascal-matrix API.

## Two Alternative Deterministic Routes

1. **Direct cofactor expansion.** Skip the Hankel factorization entirely. Show `det Ψ(x)` satisfies the ODE `f'(x) = -n·f(x)` by differentiating under the determinant using `upperGammaNat`'s recurrence `d/dx upperGammaNat(k,x) = -upperGammaNat(k-1,x)·exp(-x)·...` and Jacobi's formula. With `f(0) = det Ψ(0)`, conclude `f(x) = f(0)·exp(-n*x)`. Fewer matrix-factorization obligations.

2. **Smith normal form / elementary divisors.** Treat `Ψ(x)` as a polynomial-in-`x` matrix over `ℚ[x]`. Compute its invariant factors directly (feasible for small `n`, then generalize by pattern). The determinant ratio becomes a product of scalar ratios. Avoids the `T·H_0·T^T` decomposition entirely; replaces it with divisibility arguments in a PID.
