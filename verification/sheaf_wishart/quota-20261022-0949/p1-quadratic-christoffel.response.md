## P1 Route Review

### 1. Hidden Assumptions & Edge Cases

- **n=0**: p monic degree 0 means p=1, q monic degree 1 means q=X-a. Conditions F(X^i p)=F(X^i q)=0 for i<0 are vacuous. The Wronskian p(z)q'(z)-q(z)p'(z) = 1·1 - (z-a)·0 = 1. The identity reduces to F((X-Cz)^2) = F(1)·1, forcing F(1)=F((X-Cz)^2). This over-constrains arbitrary linear F unless the functional is specifically tied to p,q. The seed should handle n=0 as a degenerate base case separately or verify the identity holds trivially.
- **Confluent evaluation rows require differentiability**: eval_z and eval'_z acting on polynomials is well-defined algebraically, but if F is a general linear functional (not necessarily integration against a measure), "derivative of evaluation" must be defined purely formally as a row operation, not analytically.
- **Column monicity in Q**: Q=[1, X-z, (X-z)^2 X^j] for j=0,...,n-1 gives degrees 0,1,2,...,n+1. The last two columns have degrees n and n+1 but leading coefficients from (X-z)^2 X^{n-2} expand to monic only if tracked carefully. The accepted `monic_functional_columns_det` applies when columns are monic of exact degree j—verify Q's columns satisfy this after expansion.

### 2. Three Conceptual Routes

**Route A (Proposed Confluent)**: Build (n+2)×(n+2) matrix with top two rows [eval_z; eval'_z] and bottom n rows [F(X^i ·)]. Use columns P=[1,X,...,X^{n-1},p,q]. Expand determinant along last two columns to extract Wronskian factor. Bottleneck: proving the squared-shift moment determinant equals the confluent determinant requires a non-trivial column transformation identity linking Q-basis to P-basis while preserving the confluent structure.

**Route B (Direct Factorization)**: Work entirely in the moment basis. Express F((X-Cz)^2 X^{i+j}) = F(X^{i+j+2}) - 2CzF(X^{i+j+1}) + C^2z^2F(X^{i+j}). Factor the resulting Hankel-like matrix as a product involving the original moment matrix and a rank-2 update encoding p,q interpolation conditions. Bottleneck: the rank-2 update factorization yielding exactly the Wronskian is algebraically opaque without Christoffel-Darboux machinery.

**Route C (Single Christoffel + Derivative Limit)**: Apply the known single-evaluation Christoffel identity det[F(X^{i+j}(X-z))] = det[F(X^{i+j})]·p(z)/leading... then differentiate with respect to z to produce the confluent/squared version. Bottleneck: justifying differentiation under the determinant and tracking how q emerges from the derivative of p-related quantities.

**Simplest**: Route A, because `monic_functional_columns_det` directly gives the P-determinant as H_n·Wronskian, and the Q-to-P change-of-basis is upper-triangular (monic degree condition), making the determinants equal by the accepted lemma.

### 3. Math-Check Type

Core steps should be checked at type level via:
- `Matrix.det_of_upper_triangular` for change-of-basis between Q and P columns.
- `LinearMap.ext` to verify F(X^i p)=0 constraints propagate through row operations.
- Polynomial degree/coefficient extraction (`Polynomial.coeff`, `Polynomial.natDegree`) to confirm monicity is preserved in confluent columns.

### 4. Mathematical Obstruction

The primary obstruction: **the confluent determinant with Q-columns does not automatically equal the squared-shift moment determinant**. Q=[1, X-z, (X-z)^2 X^j] introduces z-dependent column transformations. When you apply F to these columns, the bottom n rows become F((X-z)^2 X^{i+j}), but the top two evaluation rows act on (X-z)^2 X^j giving 0 and derivatives that may not match the target identity's structure. You need to verify that after row reduction eliminating the eval/eval' contributions, the remaining n×n minor is exactly [F((X-Cz)^2 X^{i+j})]. If C≠z, there is a mismatch between the shift in the functional argument and the shift in the evaluation rows that breaks the confluent interpretation.
