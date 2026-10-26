# Mean-rank positive noncentrality parameters

Six printed declarations, one module. The positive parameter vector is indexed
by Fin rank(M) and extracts the first rank(M) descending column mean-Gram
eigenvalues. It is positive and Antitone. Every remaining mean-Gram coordinate
is exactly0. Reconstructing the full vector from these positive parameters and
zeros proves that equal deterministic mean rank and equal positive vectors
give equal actual paperJointSpectrum joint measures for the same arbitrary m,n.
The original same2mn real Gaussian source is retained.

These parameters belong to the deterministic mean M, not to a random sample.
They may repeat. The original OrderedPositiveNoncentralSpectrum package is
constructed only when StrictAnti is an explicit extra hypothesis. Rank0 and
empty shapes are allowed; StrictAnti on the empty index type is vacuous and
does NOT imply rank>=1. Existing matrix rank bounds supply rank(M)<=min(m,n).
No G2 density or determinant candidate equality is asserted.

## Controls and validation

Seed2026102602:166 pre-source controls PASS, including exact all-shape/rank
examples, repeated positive parameters, zero tail, squared-amplitude convention,
trace sum and rank-alone negative. The first scalar CAS control failed on raw
structural equality of (1-i)(1+i) and2. Its script is retained; exact simplification
repaired the implementation before any new Lean source. Controls are not proofs.

MeanPositiveNoncentralParameters v1 exited0, standard3 axioms, default budget;
six independent literal types and immutable final serial shared bundle PASS.
No failed Lean source iteration. The source and prompt were sent only after
the human explicitly answered "允许发送这份新模块". One bounded90s Qwen3.8-Max
P4, tools disabled, returned2026-10-26T07:28:37UTC. This was not human review or
independent compilation, and Qoder authored none of the proof bodies.

## P4 resolution against pinned interfaces

1. Matrix.IsHermitian.eigenvalues_0 is indexed by Fin(Fintype.card(Fin n)),
as defined in Mathlib/Analysis/Matrix/Spectrum.lean. The rank embedding first
maps Fin rank(M) into Fin n, then Fin.cast(card_fin n).symm maps it to exactly
that eigenvalues_0 index type. Both preserve val. The reviewer both describes
this correct direction and labels it inverted; the exact definition and six
literal types settle the question.
2. FinitePositiveMinimum.antitone_positive_iff_lt_count takes f, Antitone f,
and an index, and proves positive iff index.val<positive-count. It explicitly
allows negative tail entries and requires NO nonnegativity hypothesis. The
last underscore is the index, not a missing proof. The count equality is then
rewritten by gram_positive_modes_card_eq_rank, and i.isLt finishes.
3. The claim that positivity+StrictAnti implicitly forces rank>=1 is false:
both universal properties are vacuous on Fin0. The structure and existential
remain valid there. No downstream nonemptiness premise is supplied or inferred.
4. The final proof reconstructs both full mean spectra. Under equal ranks,
positive-coordinate casts have the same natural-number val; the checked
convert/congr proof discharges the equality. Kernel-checked terms cannot retain
the dangling subgoals suggested by the reviewer. The exact cast hRank is also
bound in the independent literal target.
5. The imported actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues
takes precisely fixed M,N and equality of their full descending mean-Gram
vectors. Measurability of the actual spectrum map and its pushforward transport
were proved in the accepted936 bundle, not silently requested as new hypotheses.
The inherited measure/model interpretation remains marked for human review.

[需人工审查] Noncentrality/covariance convention, Borel transport and original
paper mapping. Frozen publication products unchanged; fullLake/Linux independent
kernel NOT_RUN. General G2, original general T1/T2 and journal T3 remain OPEN.
