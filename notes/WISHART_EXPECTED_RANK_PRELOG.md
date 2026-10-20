# Expected rank is the arbitrary-factor full-logdet prelog

2026-10-20 checkpoint491=489 theorem/instance+2 earlier constructions,
mainfacade45 actualexit0/auditPASS. Three printed declarations added to488:
Hermitian nonzero-eigenvalue rank cardinality, positive-Gram-mode rank identity,
and actual correlated expected-rank prelog. Codex proofs, finalsourceQoder P4
realresponse with exact source hashes, not human approval or independent compile.

For Z m-by-p iidCN1, ANYFIXED B p-by-n inclrectangular/singular/zero and
ANYFIXED M m-by-n, X=ZB+M, W=X^H X, natural logarithms:

    E log(Re det(I+rW))/log r -> E[(rank_C X : Real)], r->infinity.

All finite shapes allowed, no rank, positivityAE, inverse moment, spectral
density or absolute-log moment premise. This identifies the previously proved
expectedpositive-mode expression with the actual matrix rank expectation.
It does NOT evaluate this expectation as a deterministic formula in B,M.
The proposed a.s.rank min(m,rankB+rank(M restrictedkerB)) is STILL OPEN.

Deterministic proof: Hermitian A is unitary-conjugate to its real diagonal.
Both unitary determinants are units, so left/right rank invariance and existing
rank_diagonal give card(nonzero eigenvalues). For GramPSD, nonnegative makes
nonzero equivalent to strictlypositive. The explicit cardinality index equivalence
transports the sum. Finally rank(X^HX)=rankX by existing mathlib. Pointwise equality
rewrites the existing expectedpositivecount limit; the bounded globallymeasurable
finite indicator sum also supplies measurability/L1 of actual rank by equality.
No new analytic or Gaussian assumption is introduced by the rank bridge.

Controls beforeproof: exact ranks for empty, indefinite and PSD Hermitian examples
plus complex rectangular Gram; floating eigenvalues cross-check finite counts.
Indefinite diag(-2,0,1) has rank2 but positivecount1: PSD restriction is necessary.
These are implementation controls, not proof of the generic rank identity.

Final-source P4 'fatal' issues were checked against exact pinned code and rejected:
1. It assumes eigenvalues is an independently unsorted spectrum. Actual pinned
   Mathlib/Analysis/Matrix/Spectrum.lean:67-68 DEFINES eigenvalues i as
   eigenvalues0((equivOfCardEq(card_fin...)).symm i). The exact same cardinality
   equivalence is unfolded in hs. No extra sorting permutation theorem is needed.
2. actualCorrelatedEigenvalue is DEFINITIONALLY the PSD Gram eigenvalues0 at
   CorrelatedLogDetLowScale.lean:18-21. The alleged missing identification is rfl,
   not an unproved characteristic-root interface.
3. complexGram_eigenvalues0_nonneg uses precisely Fin(card(Fin n)); no wrongindex.
4. The final cast follows the exact Nat-rank equality rank_conjTranspose_mul_self;
   actual standard3 prints and exit0 retained, not merely a suggested norm_cast.
5. An integral is total, not ill-typed without measurability. Here pointwise
   equality with the already proved boundedmeasurable L1 mode-count suffices.
6. Zero-dim sample measures and empty-index sums are already included in the
   universally quantified proofs; no nonempty-type premise silently added.
Its PSD vs generalHermitian distinction is correct and retained.

Failedlogs1..3 retained: dependent spectral rewrite restricted to the rank LHS;
cardinality via exact Finset.sum_boole before predicate normalization;
ComplexOrder scope supplies pinned Gramrank instance; RCLike.ofReal_eq_zero
handles the real eigenvalue scalar extension explicitly. Final rank4 PASS.

[需人工审查] Spectral/rank/physical-model correspondence, inherited DCT/Fubini/
variance. Not channel coding or an original-new probability theorem. Fullbuild
NOT_RUN; frozen manuscript/PDF/upload/code archives OLD unchanged.
