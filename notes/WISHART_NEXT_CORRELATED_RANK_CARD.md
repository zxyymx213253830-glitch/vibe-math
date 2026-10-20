# Next card: deterministic generic rank for singular fixed factors — OPEN

2026-10-20. Current488 actual prelog equals expected numberpositiveGram modes.
The spectral/rank bridge is separately undercheck, not a deterministic rank law.
No new proof source for the candidate below has been started.

Actual X=ZB+M, Z m-by-p iidCN1, B FIXED p-by-n arbitrary, M FIXED m-by-n.
Put r=rank_C B, K=ker(B:C^n->C^p), s=rank_C(M restricted to K).
Candidate (UNPROVED): rank(X)=q=min(m,r+s) almost surely, hence prelog=q.
A basis for K suffices to define s: s=rank(M*kernelBasisMatrix), basis-independent.
Do NOT identify s with rankM, or count noise modes alone. Fixed B/M, no varying
SNR mean or degenerating-covariance uniformity is claimed.

Exact rationalcomplex controls64 finite structured instances passed before any
proof. Nontrivial invertible uppertriangular columnchanges, all feasible r/s
in selected shapes including0, mean-restored modes, B0 and rectangular cases.
Witness in adaptedcoordinates: choose Mbar with nullcolumns of rank s, choose V
in complementary outputrows with rank min(r,m-s), set Z0_first_r=V-Mbar_first_r.
Then (Z0B+M) reaches q. Wrong min(m,n) and min(m,rankB) controls detected.
These certify finite witnesses only, NOT an arbitrary B/M or Gaussian AE law.

Recommended proof obligations, still OPEN:
1. Deterministic upper bound for EVERY Z: decompose C^n=C complement K, dimC=r.
   im(ZB+M) is sum of image of restriction to C (dimension<=r) and M(K)
   (dimensions). Thus rank<=r+s and<=m. It is NOT generally bounded by
   rank(ZB)+s: Z=0,B fullcolumnrank,Mnonzero refutes that stronger shortcut.
2. Deterministic witness for arbitrary B/M: B|C is iso onto imB. Pick V:C->C^m
   whose image complements M(K) up to min(r,m-s). Prescribe Z0 on imB as
   (V-M|C) composed with inverse(B|C), extend to C^p by a complement. Then
   (Z0B+M)|C=V and restriction to K=M|K. Account for mean on C by SUBTRACTION;
   merely choosing col(Z0B) transverse can be cancelled by M|C.
3. Extract one q-by-q nonzero minor at Z0, encode it as polynomial in2mp REAL
   sourcecoordinates (the /sqrt2 encoding remains explicit). For q=0 handle
   separately, or use emptyminor determinant1. Full n-by-n Gramdet cannot be
   used when q<n; it vanishes identically.
4. Nonzero minor polynomial -> Gaussian-null exceptional set -> rank>=q AE.
   Combine with deterministic upper bound, then expected-mode/rank limit.

Exact pinned assets:
* ComplexGramSimpleSpectrum.complexMvPolynomial_realZeroSet_volume_eq_zero.
* ComplexGramSimpleSpectrum.sampleEval_ne_zero_ae (P nonzero), for ANYsource
  m-by-p. Encode physical B,M INSIDE the polynomial, and use ZERO SOURCE MEAN
  (m-by-p) in this theorem. Passing physical M(m-by-n) as its mean is wrong
  when p!=n. Evaluate at complexSampleMean Z0 to witness nonvanishing.
* GaussianGramFullRank.genericComplexGram_det_eval/.genericComplexGram_det_ne_zero
  and .complexSample_shiftedGram_det_ne_zero_ae are examples of that pattern,
  not already an arbitraryrank-minor proof.
* Mathlib Matrix.Rank.rank_submatrix_le; rank_of_isUnit; rank_conjTranspose_mul_self;
  rank_diagonal. Matrix.Pivot normalform API may help deterministic witness.
* New CorrelatedLogDetPrelog gives expectedpositivecount, no rank value premise.

Bounded real Qoder P1 selected polynomial/witness route. Corrections:
* Its 'rank2 always' example fails when the second noisy row iszero; the intended
  statement is AE, not pointwise. Do not adopt the stronger claim.
* Raw complex rowspace need not be the Hermitian orthogonal complement of kerB;
  use an algebraic complement or range(B^H) with explicit inner-product proof.
* Haar/Grassmannian route ignores mean on the noisy block and dimensions r>m;
  no automatic Haar-distribution argument is used.
* Its upperbound rank(ZB)+s and transversality-only witness are rejected as above.
No citation/novelty claim or general rank proof is supplied by that response.

[需人工审查] Polynomial zero-set/Fubini, Gaussian absolute continuity, variance,
rank/positive-mode/model correspondence. Do not refresh frozen publication or
claim this candidate proved based on controls or P1 response.
