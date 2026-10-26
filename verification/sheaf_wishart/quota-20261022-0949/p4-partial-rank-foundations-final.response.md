# P4 Adversarial Review

## NoncentralFullRankNormalizer.lean

**1. `moment_coeff_top` omits the binomial coefficient.**
The proof states `simp [Nat.factorial_ne_zero]`, but the coefficient of $X^k$ in the sum is $\frac{k! \cdot \binom{q+k}{0}}{k!} = 1$. The simplifier must also resolve `Nat.choose_self (k+q)` or equivalent. If `simp` alone closes this goal, it relies on a lemma not shown; otherwise this is an incomplete proof body for the stated claim.

**2. `noncentralMoment_eval_det` matrix orientation mismatch.**
The theorem equates `Matrix.of (fun i j => poissonFactorialMomentPolynomial q i.val (lambda j))` with a Vandermonde determinant. However, `h` invokes `det_eval_matrixOfPolynomials_eq_det_vandermonde` which expects polynomials indexed by rows evaluated at column points. The transpose relation `he` corrects this, but `h` as written applies the polynomial family `(fun i => noncentralMomentPolynomial q i.val)` to produce a matrix whose $(i,j)$ entry is the $i$-th polynomial at $\lambda_j$. After `he` and `det_transpose`, the indices align, but the intermediate `have h` asserts an equality about `Matrix.of (fun i j => (noncentralMomentPolynomial q i.val).eval (lambda j))`—this is the **transpose** of what `det_eval_matrixOfPolynomials_eq_det_vandermonde` standardly produces. The proof works only if that imported lemma's convention matches this transposed form. Without seeing the import, this is a concrete semantic dependency that must be verified signature-by-signature.

**3. `theorem1PsiMatrix_zero_det_ne_zero_full_rank`: `Matrix.det_mul_row` scope.**
The step `rw [Matrix.det_mul_row]` treats `B` as obtained from `D` by multiplying each row $j$ by $w_j$. But `B i j = w j * D i j` multiplies **columns**, not rows. Either the lemma name is misleading (some libraries state it for columns) or this rewrite is dimensionally incorrect. This is a potential mathematical error unless `Matrix.det_mul_row` in this codebase actually refers to column scaling or `D` has been implicitly transposed earlier.

**4. `Complex.ofRealHom.mapMatrix` injectivity.**
The final coercion step `exact_mod_cast hB` requires that embedding a real matrix into $\mathbb{C}$ preserves determinant nonzeroness. This holds because `Complex.ofRealHom` is injective, but the proof does not cite this fact explicitly—it relies on `mod_cast` resolving the coercion. This is acceptable if the tactic succeeds, but fragile.

## NoncentralGammaMomentColumns.lean

**5. `gammaMoment_column_eq_coefficient_sum`: missing `factorial_ratio_vandermonde` hypothesis check.**
The identity `rw [factorial_ratio_vandermonde q h k]` is invoked without argument verification. The left side sums over `range (h+1)` with terms involving $\binom{q+h}{h-j}\binom{k}{j}$. The Vandermonde convolution $\sum_j \binom{a}{j}\binom{b}{h-j} = \binom{a+b}{h}$ requires matching parameters. Here the first binomial has upper index $q+h$ and lower $h-j$, while the second has upper $k$ and lower $j$. This yields $\binom{q+h+k}{h}$, so the factorial ratio should be $\frac{(q+k+h)!}{(q+k)!}$. The proof writes `((k+q+h).factorial : ℝ)/((k+q).factorial : ℝ)`, which matches—but only if `factorial_ratio_vandermonde` accepts these exact arguments in this order. A parameter-order mismatch would silently produce a wrong constant.

**6. `gammaMomentColumnTransform_det_ne_zero` with `p = 0`.**
If `p = 0`, then `Fin p` is empty, the product is empty (= 1), and the claim holds trivially. No gap, but worth noting the edge case is correctly handled.

## ZeroConfluentVandermonde.lean

**7. `zeroConfluentVandermonde_det` block structure assumes square diagonal blocks.**
`Matrix.fromBlocks 1 ... 0 ...` requires the top-left block to be square of size $p \times p$ and bottom-right $L \times L$. The definition uses `Matrix.of (fun i j => lambda j ^ i.val)` for the top-right $p \times L$ block and `Matrix.of (fun i j => lambda j ^ (p+i.val))` for the bottom-right $L \times L$ block. The determinant formula `det_fromBlocks_zero₂₁` applies when the (2,1) block is zero, giving $\det(A_{11})\det(A_{22})$. Here $A_{11} = I_p$, so $\det = 1$. This is correct.

**8. `zeroConfluentVandermonde_eq_zero_of_conditions`: vector-matrix multiplication convention.**
The proof uses `Matrix.eq_zero_of_vecMul_eq_zero`, which requires the **row vector** $c$ times the matrix to equal zero. The hypothesis `he` provides exactly the components of this product for `inr` indices, and `hc` zeros out the `inl` components. Correct.
