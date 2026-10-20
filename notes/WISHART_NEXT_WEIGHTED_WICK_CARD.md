Update2026-10-20: weighted affine Wick and actual correlated secondmoments/tracevariance now CLOSED at469/facade42. See WISHART_CORRELATED_SECOND_MOMENTS.md. Below next/open card is historical; correlated logdet curvature remains undercheck.

# Next useful card: weighted complex fourth moment

Completed checkpoint431/facade40: all-shape iid trace first/second/variance and
closed low-scale logdet coefficients; arbitrary rectangular/singular B actual
Gram mean. No correlated fourth/trace-variance/low-scale extension is proved yet.

The next reusable algebra obligation is a weighted Wick theorem over ANY finite
index type I, allowing I empty. Let a,b,c,d:I->Complex, alpha,beta,gamma,delta
arbitrary complex constants, and define

    U=sum_i a_i X(inl i)+C(alpha),
    V=sum_i b_i X(inl i)+C(beta),
    S=sum_i c_i X(inr i)+C(gamma),
    T=sum_i d_i X(inr i)+C(delta).

Here c,d are ALREADY coefficients of conjugate source variables. Do NOT apply
an additional star to them. Put ac=sum a_i*c_i, ad=sum a_i*d_i,
bc=sum b_i*c_i, bd=sum b_i*d_i. Exact target:

    L(U*V*S*T)=alpha*beta*gamma*delta
       +beta*delta*ac+beta*gamma*ad+alpha*delta*bc+alpha*gamma*bd
       +ac*bd+ad*bc.

L is the existing complex Gaussian factorial functional, NOT a ring hom.
First prove its centered weighted fourth part by finite expansion and the
checked two-pair coordinate theorem; derive the shifted statement using zero
total-charge lower terms. This will contract physical ZB+M without inversion,
including singular covariance. No fresh Gaussian radial integral or target
Wishart density is needed. Empty I gives the constant product automatically.

Exact existing assets:

* ComplexGaussianMomentFunctional.complexGaussianMomentLinear: actual L as a
  COMPLEX linear map. Apply map_sum/map_smul before rewriting it back to L;
  rewriting outer L too soon blocks linearity simplification.
* ComplexGaussianWickMoments.complexGaussianPolynomialMoment_fourth and
  .complexGaussianPolynomialMoment_monomial_unbalanced: paired counts and
  charge mismatch, includes factorial2 on coincident coordinates.
* ComplexGaussianShiftedFourthMoment.complexGaussianPolynomialMoment_shifted_fourth:
  fully checked16-term coordinate expansion.
* CorrelatedGramMean.complexGaussianMoment_correlated_row_pair: weighted second
  moment; no inverse/rank premise, actual EGram entry and L1 already exported.
* GaussianMatrixPolynomialLaw.integrable_actualComplexMatrix_polynomial and
  .integral_actualComplexMatrix_polynomial: exact actual-source integration
  for ANY finite polynomial in mp source pairs.

Preflight complex_linear_wick_control.py uses exact rational-complex expansion
for I sizes0..4, with non-real coefficients and nonzero constants. The finite
factorial functional matches the candidate; wrong double-conjugation and
missing-pair controls are detected. No samples/seed needed for exact arithmetic.
This is NOT a general proof. The earlier physical fixedseed2026101926 controls
also cover rectangular/singular/zero B and independent Gamma/zero-factor cases.

After this lemma, instantiate Sigma=B^HB and the exact four-entry contraction
in WISHART_CORRELATED_GRAM_MEAN.md, then finite row/column sums. Keep Etrace(W^2)
and E[(trace W)^2] distinct. The P1 response that mislabeled them is archived
and rejected, not a route approval. Covariance of the REALsource is I; only
the complex sample is divided by sqrt2. [需人工审查] Actual Gaussian/Fubini/
variance/model mapping remains; all future Lean checks must use the same gate.
No next proof source has been started for the weighted fourth target.
