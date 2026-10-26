# Actual paper small-side spectrum: mean noncentrality eigenvalues

Seven printed exports, two modules. For every finite rectangular complex A,
the descending full column-Gram spectrum is exactly the paper's descending
min(m,n)-coordinate small-side spectrum followed by n-min(m,n) zeros.
This is deterministic and includes empty dimensions, repeated eigenvalues and
rank deficiency. Each small-side coordinate equals the same initial full-column
coordinate. It is not the last n-dimensional coordinate in a wide matrix.

Consequently, for the same m,n and arbitrary fixed means M,N, equality of the
descending column mean-Gram eigenvalues implies equality of the actual
paperJointSpectrum pushforward measures under the original 2mn real Gaussian
source. Equality of the descending SMALL-side mean-Gram eigenvalues also
suffices: appending the same structural zeros identifies the full mean spectra.
These are joint ordered-vector law equalities, not a joint-density formula or
eigenvalue independence claim. Positive rank-L extraction and the original
candidate's distinct-positive-parameter assumptions remain the next mapping.

## Evidence and boundaries

Seed2026102601:177 pre-source controls PASS, with exact rational-complex Gram
charpoly relations at all ranks, empty/repeated spectra and descending prefix
checks, independent dense SVD and negative last-wide-coordinate/signed-padding
controls. Not proofs. GramOrderedZeroPadding v1 default180s timeout empty log
is preserved; removing an unnecessary actual-Laplace dependency reduced import
load. v2/v3 failed and v4 exit0. Paper module v1 failed and v2 exit0. Failures
remain recorded and are not accepted. Final source/default budget standard3
axioms, seven independent literal types and immutable shared final bundle PASS.

The initial restricted-network Qoder request timed out empty. Automatic review
rejected network escalation for absent external disclosure authorization. The
safer installed local DeepSeek 7B attempt returned an unrelated theorem: exit0
did NOT constitute P4, and that response is rejected. The owned local server
was stopped. The human then explicitly answered "允许发送这两份锁定源码" for
GramOrderedZeroPadding.lean and PaperNoncentralSpectralOrbitLaw.lean plus their
review prompt. Only those two complete locked files were supplied to one
approved90s Qwen3.8-Max request, tools disabled, 2026-10-26T06:59:54--07:00:24UTC.
It returned a substantive P4. No reviewing model authored proof bodies, and
this is not human review or independent compilation.

## P4 resolution against exact sources

1. No extra dimension premise is missing from hermitian_ordered_zero_padding.
The assumed exact polynomial identity B.charpoly=X^d*A.charpoly gives equality
of the complete root multisets by roots_mul and roots_X_pow. Sorting that
equality proves equality of lists, so it already forces equal lengths b=a+d.
It is unnecessary to separately prove this consequence before deriving the
lists. d=0 is intentionally allowed, including empty matrices.
2. Nonnegative eigenvalues of A are an explicit sufficient hypothesis, not an
inconsistency. They put the extra zeros at the END of the descending list;
the signed negative control shows why the hypothesis matters. For A^H's Gram,
the existing lemma directly proves nonnegativity of (A^H)^H A^H=A A^H; no
unproved row/column spectral transfer is used for that sign assertion.
3. Fin.cast and Fin.castLE preserve the natural-number index. The proof takes
the same list getElem at i.val, under explicit bounds, then converts the
proof-only index transports. Tactics cannot fail silently in an accepted
kernel term. The literal targets bind these exact casts and dimensions.
4. The private PSD sign lemma reindexes an assertion valid at EVERY eigenvalue
index. It needs no order preservation of the chosen equivalence. Sorting is
separately supplied by eigenvalues_0_antitone.
5. PaperSmallSideGram explicitly chooses row Gram for m<=n and column Gram
otherwise. The existing charpoly_paperSmallSideGram_eq_charpoly_colGram A hnm
states exact equality under n<=m, not equality up to a factor. Thus the tall
branch has padding length0. In the wide branch the exact X^(n-m) relation is
used in the opposite orientation, including rank-deficient zero roots.
6. P is a fixed finite coordinate projection from a REAL vector space, not a
claim that this domain is discrete. Each selected coordinate is measurable;
the existing joint-vector measurability and explicit map_map hypotheses handle
the Gaussian source. There is no unstated measurability in M,N.
7. The accepted imported theorem in ActualNoncentralSpectralOrbitLaw identifies
the measures of the exact full ordered coordinate FUNCTIONS z -> (i ->
complexNoncentralSampleEigenvalue M i z). It is not equality only of multisets.
Projecting these vectors onto their initial min(m,n) coordinates is therefore
valid. The new literal targets independently bind both resulting paper laws.

[需人工审查] Borel maps, index casts, noncentrality conventions and source-paper
mapping. Frozen publication products unchanged; fullLake/Linux independent
kernel NOT_RUN. General noncentral G2, general original T1/T2/T3 mapping remain OPEN.
