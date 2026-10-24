# General one-surplus central T1 (OPEN)

After 810/1809c98 closes arbitrary-row noncentral single-column T1/T2,
next target is the ORIGINAL central T1 for (s,t,L)=(n,n+1,0), all n>0.
ActualOneExtraRow_minimum_CDF is already proved and must be reused.
Do not rebuild its Gaussian/Bartlett law.

Algebraic target: det[(i+j+1)!+x*(i+j)!] equals
prod_i(i!*(i+1)!)*sum_{k=0}^n choose(n,k)*x^k/k!.
Shifted-polynomial moment determinant and upperGammaNat factorial functional
then identify the literal original Gamma determinant, using double Fin.rev.
Controls seed2026102403:55 exact checks n0..8, not a general proof.

Real bounded Qoder P1 returned three routes but misread the tridiagonal
Jacobi J as diagonal. Reject its product-of-diagonal determinant claim:
n2 gives (x+1)(x+3)-1, not (x+1)(x+3). The raw response is preserved.
Its Christoffel quotient also omitted n!: the monic polynomial produces
n!*sum choose(n,k)x^k/k!, not the unscaled sum. Its n2 factorial-of-x
expression was a self-corrected misstatement, not a proposed source.

Chosen Codex route: explicit signed monic factorial Laguerre polynomial,
orthogonality from pinned Polynomial.fwdDiff_iter_eq_zero_of_degree_lt and
fwdDiff_iter_eq_sum_shift, then a finite augmented-determinant Christoffel
identity. Avoid assuming a non-existent Laguerre or tridiagonal-det API.
Seed2026102404's129 exact pre-source checks include orthogonality n<=10,
arbitrary complex moment functionals n<=5, and diagonal-misreading control.
No positivity or multiplicativity is imposed on the complex-linear functional.

First useful source: factorial-weighted alternating sum vanishes for j<n,
then monic degree n/orthogonality/evaluation of the explicit polynomial.
For the determinant bridge use a matrix whose row0 is evaluation at -x and
remaining rows are F(X^i*P). Changing monic column basis preserves its det.
Basis [1,(X+x),X*(X+x),...] gives det(H1+xH0). Replacing final monomial
by monic orthogonal P_n gives (-1)^n*P_n(-x)*det(H0).

[需人工审查] Original formula indexing and normalization, later actual-model
mapping. Current controls/P1 are not proofs. Multi-column noncentral G2,
general rectangular T1/T2/T3/full mapping remain OPEN.
