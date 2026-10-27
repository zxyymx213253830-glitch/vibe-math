# Next: candidate kernel determinant positivity and normalization

2026-10-27 current checkpoint:969 accepted (971 normalizer norm-product final acceptance in progress). General original Psi(0) nonzero for all allowed ranks was accepted in4b827bf; the first3 and last2 exact-source disclosure permissions and their real P4 requests are complete. Historical950/quota-stop/unanswered wording has been superseded; do not repeat those source reviews. Norm-product is a separate authorized, already-returned P4 and is being adjudicated against locked source. See WISHART_ORIGINAL_PSI_NORMALIZER_NONZERO.md and WISHART_ORIGINAL_PSI_NORM_PRODUCT.md.

User fixed one-hour window2026-10-27 15:06:21--16:06:21UTC; no research after the deadline. Generic candidate positivity is still OPEN, distinct from denominator nonzero, norm formula and formal endpoint limits.

New seed2026102610 control: experiments/noncentral_candidate_total_positivity_control.py,530 exact finite-minor/Cauchy-Binet/Bessel-series calibration checks PASS before any new positivity proof source. This is NOT a total positivity proof, infinite limit interchange, normalized candidate law, or actual G2 law. There is currently NO new Lean positivity source.

For energy x>0 and lambda>0, omit positive row/column factors and consider
F_q(lambda,x)=sum(m>=0) (lambda*x)^m/[m!*(q+m)!].
Original noncentral columns include lambda^(q/2) exp(-lambda-x) x^q F_q; central columns include exp(-x) x^(q+h). With central columns h=0..p-1 first, lambda ascending, x ascending, finite truncations J>=s-1 factor as X*C with X_i,m=x_i^m, C_m,h=delta_m,h centrally and C_m,j=lambda_j^m/[m!*(q+m)!] noncentrally.

Every surviving Cauchy-Binet term contains all central exponents0..p-1, and higher exponents for noncentral columns. Needed GENERAL missing lemma: positive generalized monomial Vandermonde for positive strictly increasing points and strictly increasing natural exponents. Standard consecutive-degree Matrix.det_vandermonde is available; no generalized-positive API was located in the pinned file inventory. A possible route is coefficient/sign-variation root bounds plus continuity/sign identification, or a direct combinatorial alternant proof. Data.List.SignVariations exists, but a polynomial Descartes root bound was not located by filename scan; do not pretend it is already available. Review existing finite Gram/minor expansion proofs for the exact Cauchy-Binet API rather than guessing a theorem name.

After a genuine finite positivity proof: use convergence of each nonnegative entire series and finite determinant continuity to obtain nonnegativity; preserve a fixed strictly positive lowest-exponent minor to prove strict positivity rather than assuming strict positivity survives arbitrary limits. The control verifies insufficient J<s-1 gives rank0 determinant, repeated x/lambda vanish, and lambda0 conflicts with a positive-size central block. These edge cases must be explicit. p=0 can permit a zero lambda but the original paper parameter hypothesis is positive.

Only then combine the already-proved true L1 radial/Nuttall moments, Andreief, and the nonzero Psi0 denominator to construct/normalize a candidate ensemble. Nonzero denominator alone is not integrand positivity. A normalized candidate ensemble is still NOT the actual noncentral Wishart ordered joint law. Scalar trace Laplace does not identify a joint spectrum and eigenvalue density does not supply anisotropic angular matrix law. Actual-law identification remains separate.

All Lean through serial shared gate, no budgets/dependency upgrades. [需人工审查] Infinite determinant/series limit, positivity conventions, Andreief/Fubini and source/model mapping. Frozen publications unchanged; fullLake/Linux independent kernel NOT_RUN.
