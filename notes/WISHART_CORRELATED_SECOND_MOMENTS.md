# Actual correlated Gaussian second moments

2026-10-20 checkpoint469, mainfacade42 actualexit0, auditPASS.
All new proof bodies Codex; bounded Qoder planning/P4 only, not independent compile.

Z is m-by-p iid CN(0,1) obtained from2mp REALstandardGaussian coordinates/sqrt2.
B is FIXED p-by-n, M FIXED m-by-n, X=ZB+M,W=X^H X. Sigma=B^H B,
A=M^H M,K=m Sigma+A. No inverse, rank or positive-dimension premise occurs.
p=0 or B=0 gives deterministicM; m=0 gives zeroGram; n=0 gives emptytraces.

The following are actual Gaussian expectations, with explicit true L1 proofs:

    E[W_ij W_uv]=K_ij K_uv+m Sigma_iv Sigma_uj+Sigma_iv A_uj+Sigma_uj A_iv.
    E trace W = Re trace K.
    E trace(W^2) = Re trace(K^2)+m(Re trace Sigma)^2
                   +2(Re trace Sigma)(Re trace A).
    E[(Re trace W)^2] = (Re trace K)^2+m Re trace(Sigma^2)
                        +2 Re trace(Sigma A).
    E[(Re trace W-Re trace K)^2] = m Re trace(Sigma^2)+2 Re trace(Sigma A).

The first formula is an ordinary product WITHOUT conjugating the second entry.
Do not swap indices to a Hermitian covariance convention. All scalar trace
quantities of Gram matrices are real; the PSD trace imaginary-zero facts are
explicitly discharged. The spectral second moment is different from square of
trace. The K-expression is already closed: K=mB^HB+M^HM, no probability integral.

Proof chain: centered weighted Wick -> affine weighted Wick (8 lower/affine
lemmas) -> arbitrary four source entries (10 row/eval/L1/moment lemmas) ->
Gram-entry product (5) -> finite trace algebra (3) -> actual trace moments (11).
The separate1 centered lemma was integrated at432. These are supporting
printed declarations, not38 independent new probability breakthroughs.

Controls BEFORE proofs: exact rational-complex generalfour-entry24 cases,
completeGram-product12 cases, trace/spectral identities on3 shapes inclzero
source and singular/rectangular factors. Earlier actual fixedseed2026101926,
200000samples/5shapes provided independent Gamma/zero-factor controls.
New fixedseed2026102001,200000/4shapes checks low-scale candidate curvature
against exact moments, including Gamma identity and singular/zero-source cases.
The latter is a preflight, not yet the low-scale theorem at this checkpoint.

Final-source real Qoder P4 responses are hash-bound. Resolutions:
* Centered missing-pair alarm retracted within the response; complex Wick has2
  surviving direct/conjugate pairings, with factorial2 on coincident indices.
* Affine first response only emitted unexecuted read tags: INVALID review,
  archived. Final self-contained request delivered substantive issues-only P4.
* Its map_mul objection confuses C (a ring hom) with L (a linear map).
  map_mul is used on C inside deterministic polynomial identities, never on L.
* Its hL/change objection misses the deliberate linear-map bridge: map_sum and
  map_smul must run BEFORE rewriting outerL. The first failed trace-algebra log
  preserves this exact ordering correction; no new analytic assumption added.
* Four-entry review's initial missing-delta heading is retracted; k=l indicators
  and Sigma indices are correct. ComplexMatrixPolynomial is MvPolynomial overC,
  hence commutative, as actual ring checks confirm. complexGram is B^H B.
* Entry-product P4 hL is NOT definitional equality between eval and integration:
  it is the definition of the finite linear functional. Actual law equality is
  separately proved for ANY polynomial, not merely single entries.
* Actual trace P4 'hb forward reference' claim is false. hi2.sub(...) constructs
  an Integrable proof; hb is the separate integral_sub EQUALITY, used after
  integral_add. Lean has no such forward reference and hb is used in rw.
* Its missing probability mass instance exists in pinned
  Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:71,
  isProbabilityMeasure_stdGaussian. Empty Euclidean spaces are included.
* No unnecessary classical premise is required by eval_trace_sq; its finite
  indices have decidable equality and the actual compiler accepts the theorem.
  Cast/simp style comments do not invalidate checked proof terms.

Failed attempts retained: row contraction congr elaboration timeout repaired
with an explicit polynomial equality; Kronecker finite-sum orientation fixed;
real projection RCLike.re/Complex.re aligned using exact pinned API; final
imaginary trace simplification uses both Gram imaginary-zero facts.

[需人工审查] Gaussian normalization, product/Fubini, real integral transport,
variance/model/paper correspondence remain REQUIRED. Model P4 is not human
approval. No general noncentral density/jointG2/high-SNR singular-factor claim.
Full Lake/mathlib build NOT_RUN; frozenpaper/PDF/upload/code archives OLD unchanged.
