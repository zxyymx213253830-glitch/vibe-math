# Closed noncentral second trace moment and low-scale curvature

For ALL finite m,n, any fixed complex mean M, iid variance-one complex CN noise
Z, X=Z+M, W=X^H X, A=M^H M and F=SUM_ij ||Mij||^2, the actual identities are

    E trace(W^2) = mn(m+n)+2(m+n)F+trace(A^2),
    (rho*(mn+F)-E log det(I+rho W))/rho^2
       -> [mn(m+n)+2(m+n)F+trace(A^2)]/2, rho->0right.

Real parts of traces are explicit in Lean. For Hermitian squares these traces
are real. The first expression is NOT E[(trace W)^2]; these are different
second moments. There is no full-rank, inverse-moment, spectral density, or
target-moment hypothesis. Zero shapes are included. All proof bodies Codex,
Qoder only route/review. Classical results, no new probability-law novelty claim
and no channel-coding/mutual-information derivation.

## From Gaussian coordinates to actual moments

`ComplexGaussianWickMoments.lean` derives10 algebraic declarations from the
existing exact factorial moment functional. Matching direct/conjugate
exponents gives factorials; unequal total charges force zero. Constants,
coordinate means, pure pairs, odd triples and mixed pairs are evaluated. The
fourth contraction is delta_ac*delta_bd+delta_ad*delta_bc. When all indices
coincide, both pairings contribute and the answer is2=2!, not1.

`ComplexGaussianShiftedFourthMoment.lean` expands16 polynomial terms BEFORE
applying the linear functional (never treats it as multiplicative). Four odd
triples, two pure pairs and four single-coordinate terms vanish. The constant,
four mixed second-moment terms and two fourth pairings remain.

`NoncentralGramEntryContraction.lean` instantiates four entries of an actual
Gram-square term. Column coincidence i=j and row coincidence k=l are kept
separate, including the simultaneous coincidence case. The final matrix moment
proof in `NoncentralGramSecondMomentClosed.lean` sums these terms. The column
delta contributes2*m*F, the row delta2*n*F. Central pairings contribute m^2*n
and m*n^2. The mean-only term is trace(A^2). The sum_mul/mul_sum expansion
reverses the two row sum binders; explicit Finset.sum_comm resolves this before
termwise comparison, rather than falsely equating the different summands.

The prior actual polynomial integration theorem identifies this finite
functional with E trace(W^2), with L1 already established. The prior L4/DCT
curvature theorem then gives the second limit. These probability assets are
reused, not reproved or replaced by target assumptions.

## Evidence and boundaries

Final leaves wick-moments-6(10), shifted-wick-2(1), gram-entry-contraction-1(1),
gram-second-moment-7(4) all realexit0 and standard three axioms. Earlier failed
logs preserve DecidableEq, casts, sum ordering and overly narrow simp repairs.
Final main facade38 realexit0.16 new printed items are algebraic/actual pieces
of this chain, NOT16 separate probability breakthroughs. Exact sources/olean/
logs/dependencies/controls and final-source real P4 snapshots are audit bound.

Before this proof: fixedseed2026101925,200000 actual samples per5shapes and
independent scalar Gamma controls passed. Seven exact rational shape checks
also match the closed formula, with wrong omission of factorial2 detected;
four-index exact finite contraction enumeration covers dimensions1..4. These
tests are evidence only; the Lean proofs quantify over ALL finite dimensions.
The same controlled experiment was subsequently extended to test the actual
trace variance candidate for a next card; that is not part of this theorem.

Both final-source Qoder P4 responses delivered. The Wick response labels a
"critical missing pairing" then explicitly retracts that concern and concludes
zero concrete errors; no terms are missing. Its empty-index "zero polynomial"
wording should read zero-EXPONENT monomial C(c), whose moment is c. The matrix
review finds no concrete issue, but swaps the descriptions of the individual
row/column factors; exact code yields2mF and2nF as above. For m=0,n>0, the
Gram is n by n zero, not0 by0. These metadata/description mistakes are retained
with the full responses; they do not override actual source and kernel evidence.

[需人工审查] Gaussian normalization, measure/Fubini, proof bodies and paper
parameter correspondence remain. Model P4 is neither human review nor
independent compilation. Full Lake/mathlib build NOT_RUN. Frozen manuscript,
PDF and upload/code archives unchanged and OLD. Original generalT1 determinant
identity, noncentral minimum G2/sharp coefficient, general-d simplified central
hard-edge coefficient, T3 journal constant and full originalT1-4 mapping open.
