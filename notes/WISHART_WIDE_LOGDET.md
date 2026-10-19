# Full Gaussian log-det: both orientations and min(m,N) prelog

2026-10-19. Codex proofs. [需人工审查] Gaussian transport, variance and small-side
spectral/model interpretation. Positive row and column dimensions only.

For any m,N>0 and any FIXED complex mean M, actual iid variance-one CN X=Z+M:

    E log(Re det(I_N+rho X^H X))/log rho -> min(m,N).

For wide m<=N, the finite constant offset is

    E log(Re det(I_N+rho X^H X))-m log rho -> E log(Re det(XX^H)).

The small-side row-Gram logdet on the right is separately proved absolutely
integrable. When m<N, X^H X is singular, and its real log0 default value is
NOT substituted as a high-SNR offset. The earlier tall offset theorem remains
the counterpart for N<=m. This is a full matrix statistic, not weakest-mode
outage, but not a derivation of a channel coding/mutual-information theorem.
No zero-dimensional extension, SNR-dependent mean or singular covariance is
included in these statements.

## Exact route

1. complexGram X=X^H X. The exact identity is
   (complexGram(X^T))^T=XX^H. It is NOT complexGram(X^T)=XX^H.
2. Sylvester/Weinstein-Aronszajn, with A=X^H and B=rho X, gives equality of
   det(I_N+rho X^H X) and det(I_m+rho XX^H). Determinant transpose invariance
   identifies the latter with det(I_m+rho complexGram(X^T)). The proof works
   algebraically for all real rho; finite expectation interpretation here
   remains rho>=0.
3. Reuse GaussianMatrixBlockLaw.complexSampleTransposeReindex, an existing
   REAL linear isometry equivalence on the TWO-real-coordinate source, and
   its exact matrix-transpose identity. stdGaussian_map gives the source
   measure equality. Mean becomes M^T, NOT M^H. No new source-adjoint map law
   is invented from the older adjoint measurability fact.
4. A genuine measurable equivalence transports the expected full statistic
   to the tall transposed actual model. The source law is actual Gaussian,
   not an assumed density. Tall prelog and offset apply to arbitrary M^T.
5. Unshifted row-Gram determinant equals the transposed column-Gram
   determinant. Integrability is transferred through integrable_map_measure
   before interpreting the offset as a finite expectation.

Selected assets: Matrix.det_one_add_mul_comm, Matrix.det_transpose,
complexSampleTransposeReindex, complexSampleMatrix_transpose_reindex,
stdGaussian_map, integral_map_equiv, and the already proved arbitrary-mean
tall actual expected offset/prelog and absolute logdet integrability.
Rejected extra routes: constructing an adjoint Gaussian isometry when the
plain transpose already suffices; new spectral zero-padding/SVD infrastructure.

Fixedseed2026101924,200000 actual samples per wide shape (1,3),(2,4),(3,5)
check large/small/transposed logdet, noncentral trace and the known scalar
Gamma digamma offset. A wrong-N-prelog negative control passes. These finite
controls are not proofs. Existing sqrt2 source scaling is retained exactly.

New2 modules have9 printed declarations: GramLogDetTranspose3 and
WideGaussianLogDet6. Final leaf logs gram-logdet-transpose-2 and wide-logdet-3
realexit0, standard three axioms only. Main-entry facade-30 realexit0; full
Lake/mathlib build NOT_RUN. Failure logs retain the missing transpose
reduction and overbroad symmetric-simp loop; targeted rewrites resolved it
without increasing recursion limits or weakening statements.

## Real external review and resolutions

P1 selected the minimal transpose route. It briefly reversed tall/wide
dimensions then corrected itself, and misquoted the proposed exact transpose
identity as an untransposed matrix equality. None of those statements entered
the proofs. The first P4 response emitted only nonexecuted Read/Glob tags:
NOT a review. A new self-contained exact-final-source P4 response delivered
three objections, all preserved in full:

* It defines complexGram(X^T) as X^T*conjTranspose(X^T), reversing the actual
  Gram order, and says its size is N by N. In the supplied source it is
  conjTranspose(X^T)*X^T, size m by m. The hsmall rewrite has already replaced
  its determinant by det(I_m+rho XX^H) before the final Sylvester step.
  Thus the dimensional/algebraic objection is false; no stronger matrix
  equality is assumed. The exact original definition and checked hsmall
  proof, not an appeal to numerical evidence, settle this.
* It says integral_map_equiv needs integrability. The pinned exact signature
  takes a measurable equivalence and a function, with NO integrability
  premise; it handles the real integral's nonintegrable default consistently.
  Actual finite logdet expectations at rho>=0 and the small-side unshifted
  logdet integrability are separately established. No divergent expectation
  is being interpreted as finite via an unproved assumption.
* Its natural-to-real coercion concern is discharged by the actual theorem
  type and successful final kernel check: the limit is in REAL, and min(m,N)
  is coerced to REAL. The proof rewrites the natural min under that cast;
  no different limiting space or unsupported real-min identity occurs.

These are Codex resolutions of real model feedback, not an edited blanket
approval or independent compilation. Human measure/variance/model review
remains required. Frozen manuscript/PDF/upload archives are unchanged.
