# Resolution of the first Bartlett-block model review

The real `p4-block.response.md` is preserved unchanged, including its claimed
critical issue. It is a model report, not a ruling or human review.

1. **Conjugation recommendation rejected by an exact counterexample.** Here
   z_j=<u,V_j>/||u|| is the first **row** of the rotated matrix, although stored
   as a finite-coordinate Euclidean vector. Its contribution to V^H V is
   z^H z, with (j,k) entry conjugate(z_j)*z_k. The existing new kernel identity
   `complexGram_firstRow_split` proves exactly this, independent of probability.
   The source retains the subtraction V^H V-z^H z; changing conjugation would
   not somehow turn subtraction into addition as the report asserts.

   Take u=(1,0) and V=[[1,i],[0,0]]. Then z=(1,i), V^H V=[[1,i],[-i,1]], and
   the correct residual is zero. The suggested swapped contribution gives
   [[0,2i],[-2i,0]], with eigenvalues -2 and 2, not a residual PSD Gram.
   `review_conjugation_control.py` verifies this exactly over rational complex
   numbers. This is a deterministic counterexample to the review suggestion,
   not a new Monte Carlo experiment or a replacement for the Lean theorem.

2. **Dimensions:** the report itself correctly retracts this concern. The
   first-row removal leaves m rows, precisely the parameter of the actual
   residual complexWishart(m,n), even if it is singular for m<n.

3. **Centrality:** the theorem and module explicitly say central and every
   matrix measure has mean0 in its type. No general noncentral block law is
   claimed. There is no need to discharge mean0 for an unclaimed noncentral
   result; arbitrary-mean full-rank results are separate.

4. **u=0 convention:** complex division is total in Lean. At zero u, z=0 and
   B=V^H V. This is only a globally measurable extension of the observable;
   the constant fiber law is proved for u!=0, and the actual CN(m+1) law
   assigns u=0 mass0, proved via its Gamma norm law. Thus no probability claim
   at that exceptional conditional value is used. This paragraph records the
   requested convention explicitly without changing the checked source.

The original scope and human-review limitations remain. A follow-up review
was requested with this exact counterexample and the same final sources.

## Follow-up disposition

The raw follow-up accepts the row convention but raises hypothetical changes
of imported definitions. These are checked against the actual locked code:

- Mathlib Probability/Distributions/Gamma.lean defines gammaPDFReal(a,r,x)
  as `r^a/Gamma(a) * x^(a-1) * exp(-(r*x))` on x>=0. Thus r is **rate**;
  the follow-up's shape-scale claim is false. In addition, rate1=scale1,
  so even that hypothetical parametrization would not change this theorem.
- The actual inner product is conjugate-linear in its first argument. The
  proved first-row Gram identity and exact phase-sensitive control fix this
  convention. No alternate inner instance or changed kernel is in use;
  switching conventions would not turn subtraction into addition either.
- WishartProbability.lean defines complexWishart as a Gram pushforward for
  all natural m,n, with a probability instance and no m>=n premise. Therefore
  residual row count m=0 is allowed. The conclusion is well typed and checked;
  it does not assert positive density for a singular residual.

These records are a transparent response to actual model feedback, not a
claim that it delivered an unqualified approval. Human semantic review,
especially inherited Fubini/variance/model interpretation, remains required.
