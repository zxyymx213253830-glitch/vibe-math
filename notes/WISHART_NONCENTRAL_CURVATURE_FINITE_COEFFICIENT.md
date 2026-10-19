# Exact finite coefficient for noncentral low-scale logdet curvature

For ANY fixed complex mean M and finite shape m,n, let G_M be the existing
matrix of multivariate Gram entry polynomials: entry ij is

    SUM_k (X_conj(ki)+conj Mki)*(X(kj)+Mkj).

Define P_M=trace(G_M^2), an explicit finite polynomial. The actual limit from
WISHART_LOGDET_LOW_SCALE_CURVATURE.md now has coefficient

    Re L(P_M)/2,
    L(P)=SUM_{d in support(P)} coeff_P(d) *
         PROD_i [if d(inl i)=d(inr i) then d(inl i)! else0].

This removes every probability integral and derivative from the coefficient.
It is a finite algebraic algorithm, not an assumed target moment, a closed
noncentral minimum law or a joint spectral density theorem. No rank assumption
or positive dimension is added. Natural logarithms and the existing variance-one
complex source remain fixed. All proof bodies Codex, Qoder review only.

`HermitianSquaredTrace.lean` proves trace(A^2).re=SUM orderedlambda^2 for ANY
Hermitian A, including indefinite and empty matrices, by the existing spectral
theorem, ring homomorphism of unitary conjugation, cyclic trace and real casts.
It does not assert that the ordering of eigenvalues of A^2 equals that of A.

`NoncentralLogDetCurvatureCoefficient.lean` proves polynomial evaluation equals
the actual trace-square, transports the preexisting exact Gaussian polynomial
moment identity with its supplied complex L1 evidence, exchanges the real part
with the integral, and replaces the finite sum of actual eigenvalue-square
moments in the previously checked curvature limit. Evaluation is a ring
homomorphism; L is only a linear functional. Neither multiplying expectations
nor independence of eigenvalues occurs.

## Validation and limits

Final Hermitian leaf hermitian-squared-trace-5 and actual coefficient leaf
finite-curvature-coefficient-2 realexit0, five printed standard-three-axiom
declarations. Failures1..4/1 preserve real-cast and polynomial real-part transport
repairs; no source edited during compilation. Main facade37 realexit0.
Fixedseed actual sample curvature controls preceded this coefficient work;
supplemental exact rational SymPy factorial controls cover seven shapes including
zero dimensions, central/noncentral scalar fourth moment and deliberate omission
of the factorial2. Finite tests do not prove the general simplified constant.

First P4 request timed out without response and is not counted as review. The
shorter final-source real P4 response is retained. Its conditional integral_re
signature worry is resolved against the pinned mathlib declaration: complex
Integrable f is exactly the input. Its empty-shape concern is vacuous finite-sum
elimination; for m=0,n>0 the Gram is n by n ZERO, not0 by0 as the response says.
Its final comment about only factorial1 surviving is incorrect: P_M has total
degree4 and per-coordinate matched exponents can be2, contributing factorial2.
The actual functional definition and negative control preserve that factor.
No blocking mathematical issue established by the response; not blanket approval
or independent compilation. [需人工审查] Actual Gaussian measure/variance,
Fubini, proof bodies and paper correspondence still require human review.

The classical simplified expression

    Re L(P_M)=mn(m+n)+2(m+n)||M||F^2+trace((M^H M)^2)

is matched by exact finite examples but remains a SEPARATE open formalization.
The next useful algebra card is a complex Gaussian Wick contraction, using the
existing factorial functional, then finite row/column summation. Two foundational
monomial/second-coordinate moment helper candidates have passed locally; they
are not yet in this completed bundle or independently reviewed.

Frozen manuscript/PDF/upload/code archives remain old and unchanged. Full
Lake/mathlib build NOT_RUN. No upstream novelty claim for classical Wick facts.
