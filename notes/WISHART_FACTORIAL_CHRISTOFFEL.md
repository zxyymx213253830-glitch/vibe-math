# Factorial orthogonality and finite Christoffel determinant

Seven Codex declarations / two modules. These are pure complex polynomial
and matrix algebra, not probability-law breakthroughs. They provide the
structural all-n step needed for original central one-surplus T1.

The monic polynomial is
P_n(X)=sum_{k=0}^n (-1)^(n-k)*n!*choose(n,k)*X^k/k!.
FactorialLaguerreOrthogonality proves a factorial-weighted alternating sum,
monicity, exact degree, F(X^j P_n)=0 for j<n with F(X^k)=k!, and
(-1)^n P_n(-x)=n!*sum choose(n,k)x^k/k! for all complex x.
It reuses pinned forward-difference vanishing for polynomial degree<n,
applied to the rising factorial of degree j, rather than assuming a Laguerre API.

ChristoffelMomentDeterminant proves that monic degree-indexed column bases
preserve determinants for arbitrary arrays of complex-linear functionals.
It then proves det F((X-z)*X^(i+j))=(-1)^n*p(z)*det F(X^(i+j))
for every monic degree-n p orthogonal to X^i, i<n. No determinant nonzero,
positive functional, multiplicativity, measure, or n>0 assumption is required.
An augmented matrix uses row0=evaluation at z and n moment rows. The
monic bases [1,X-z,X*(X-z),...] and [1,X,...,X^(n-1),p] yield the two sides.

Seed2026102404's129 exact controls preceded both sources. Generic complex
moment controls do not assume positivity. Finite experiments are not proof.
The n2 diagonal-versus-tridiagonal negative control also rejects the earlier
P1 misreading, retained verbatim in its raw response.

One failed orthogonality source and three failed Christoffel sources/logs
are retained unaccepted. Errors concerned protected namespaces/nonzero casts,
accidentally rewriting coefficients on the RHS, explicit Matrix.of wrappers,
and reducing Fin minors; the final sources pass with standard three axioms.
Seven independent literal target types and immutable final gates are bound.

## Real bounded Qoder P4 adjudication

Qwen3.8-Max reviewed both complete final sources, tools disabled, exit0.
It reports no actual mathematical gaps conditional on imported definitions.
The requested exact dependencies are: factorialMomentFunctional is explicitly
typed Complex[X] ->_linear[Complex] Complex and takes X^k to k!; pinned
ascPochhammer_natDegree Complex j=j, with standard product semantics, and
factorial_mul_ascPochhammer states k!*ascPochhammer_j(k+1)=(k+j)!.
Complex factorial denominators are explicitly nonzero by cast of factorial_ne_zero.

The Fin indexing concern is resolved by explicit hminor equalities, checked
pointwise for row-successor/column-successor and row-successor/column-castSucc.
The Q basis has evaluation row [1,0,...]; the P basis has last column
[p(z),0,...]. The sign is row0 + lastcolumn n, hence (-1)^n; the response's
phrase n+n is incorrect and must not be adopted. Exactly n orthogonality
conditions suffice; higher moment entries elsewhere are unconstrained.
The degree product simplifier's nonzero conditions follow from monicity
and nonzero X powers, discharged in the checked source.

[需人工审查] Subsequent paper normalization/indexing and original actual-model
mapping. Qoder P4 is not human review or independent compilation. Original
all-n one-surplus T1 is still OPEN until the Gamma/paper bridge is accepted.
Frozen publications unchanged; fullLake/Linux independent kernel NOT_RUN.
