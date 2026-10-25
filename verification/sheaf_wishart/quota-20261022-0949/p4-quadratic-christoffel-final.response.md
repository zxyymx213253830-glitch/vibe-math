## P4 Adversarial Review: QuadraticChristoffelMomentDeterminant

**Scope**: Purely algebraic determinant identities over `ℂ[X]` with linear functionals. No measure, probability, positivity, or rank assumptions are stated or needed. All claims are exact polynomial identities.

---

### Actual Mathematical Gaps

**1. Missing dependency verification for `monic_functional_columns_det`**

The entire proof of the main theorem rests on `hb`, which equates two `(n+2)×(n+2)` determinants via `monic_functional_columns_det`. This imported result is applied to the column families `Q` and `P` constructed by interleaving basis-like polynomials with specific evaluation/derivative rows. The proof verifies `hdQ`, `hmQ`, `hdP`, `hmP` (degree and monicity conditions), but **no check is performed that `monic_functional_columns_det` actually requires only these hypotheses**. If the imported theorem has hidden preconditions (e.g., linear independence of the functional family `G`, non-degeneracy of the moment matrix, or a requirement that the column polynomials form a complete basis up to degree `n+1`), the application is unsound. The construction of `G` mixes evaluation (`E`), derivative-evaluation (`D`), and moment functionals (`F ∘ mulLeft`), which is an unusual hybrid; the imported theorem must genuinely handle arbitrary monic column families with matching degrees, not just standard monomial bases.

**2. Degree computation gap in `hdQ`**

The claim `((X - C z)^2 * X^j.val).natDegree = j.val + 1 + 1` uses `Polynomial.natDegree_mul` and `(monic_X_sub_C z).ne_zero`. However, `natDegree_mul` requires **both** factors to be nonzero. The proof shows `(X - C z)^2 ≠ 0` via monicity, but **does not explicitly verify `X^j.val ≠ 0`**. For `j.val = 0`, `X^0 = 1 ≠ 0`, so this holds, but the case analysis is elided under `simp`. This is technically dischargeable but represents an incomplete explicit argument in the proof body as written.

**3. Derivative evaluation in `hd` assumes characteristic zero behavior**

The step `change Polynomial.eval z (Polynomial.derivative ((X-C z)^2*X^j.val))=0` followed by `simp [Polynomial.derivative_mul, Polynomial.derivative_pow]` implicitly relies on the product rule and power rule behaving classically. Over `ℂ` this is fine, but the simplification chain is doing nontrivial work: it must expand the derivative, evaluate at `z`, and cancel all terms. The `simp` call is trusted to close a computational goal that involves `j.val`-dependent expressions. If `simp` fails to normalize the `X^j.val` derivative term correctly (which produces `j.val • X^(j.val-1)` with a natural number coefficient coerced to `ℂ`), the proof silently breaks. No `ring_nf` or explicit normalization is shown.

**4. Sign arithmetic opacity in `hs` and `ht`**

The identities `(-1)^(n+1) * (-1)^n = -1` and `(-1)^(1+(n+1)) * (-1)^n = 1` are proved by `omega` for the exponent arithmetic. This is correct but **conflates `ℕ`-exponent reasoning with `ℂ`-multiplication**. The `pow_add` and `pow_mul` rewrites require the base to be in a monoid (satisfied), but the step `show n+1+n = 2*n+1 by omega` is a natural number identity fed into integer exponentiation of a complex unit. No gap exists, but the proof trusts `norm_num` to handle the final `(-1 : ℂ)^k` evaluation without showing the parity reduction explicitly.

---

### Non-Issues (Explicitly Noted)

- No positivity, full-rank, finite-measure, or dimension-uniformity assumptions are claimed or required.
- `F`, `E`, `D` are arbitrary linear functionals; no probability model is asserted.
- The use of `classical` is for `Fin` elimination, not logical strength.
- Imported results (`monic_functional_columns_det`, `functional_border_det`) are treated as dependencies; their internal proofs are out of scope per instructions.

---

**Summary**: The core risk is **(1)**—the entire argument collapses if `monic_functional_columns_det` has unstated hypotheses not verified here. Items **(2)** and **(3)** are minor incompletenesses dischargeable by elaboration. Item **(4)** is cosmetic.
