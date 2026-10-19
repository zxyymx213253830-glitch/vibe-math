# Actual Gram mean with arbitrary rectangular or singular column factor

For any finite m,p,n, arbitrary FIXED complex B of shape p by n, arbitrary
FIXED M of shape m by n, actual iid variance-one CN matrix Z of shape m by p,
the entrywise actual identity and L1 theorem are now proved:

    E[(ZB+M)^H(ZB+M)]_ij = m*(B^H B)_ij+(M^H M)_ij.

No B inverse, whitening, rank, density or positive-dimension premise occurs.
Sigma=B^H B is n by n, not p by p. If p=0 or B=0 the model is deterministic M
and the expectation is M^H M, not generally zero. If m=0 the n by n Gram is
zero. Empty output index types give vacuous entry statements.

`CorrelatedGramMean.lean` defines an explicit polynomial in mp source pairs,
contracts a single row via E[Z_ka starZ_kb]=delta_ab and zero linear means,
then sums rows. Evaluation equals the actual Gram entry; polynomial L1 and
its exact actual integral come from the existing product-law bridge. Exported
entry integrability rules out nonintegrable Bochner default-zero issues. L is
only linear; eval is a ring homomorphism. All proof bodies Codex.

Final correlated-gram-mean-3 realexit0 with five standard-three-axiom prints;
earlier failed log preserves finite-sum grouping/conjugation repair. Main
facade40 realexit0. Fixedseed2026101926,200000 actual samples per5shapes,
identity Gamma(3,1), singular rank1, rectangular B and zero-factor controls
PASS before proof. Numerical correlated trace variance/second-spectral-moment
checks are preflight only, NOT proofs of those extensions.

P1 delivered a response but its numbered headings are not three independent
proof routes. It mislabels the second-spectral-moment formula as square of the
trace, says their difference is simply offdiagonal squared entries (false in
general), and misstates the REALsource covariance as I/2. Those suggestions
were rejected. The actual raw REAL source has covariance I, and division by
sqrt2 occurs in the complex sample map. Direct polynomial contraction was
selected; inverse/whitening is unsuitable for singular B.

Final-source real P4 found no mathematical issue, with metadata corrections:
it calls B^H B p by p; actual dimensions are n by n. Its empty-shape summary
incorrectly says all zero cases give zero, whereas p=0 leaves M^H M. Its axiom
list includes funext; actual prints are propext, Classical.choice, Quot.sound.
Full responses retained. [需人工审查] Gaussian normalization, covariance/model,
product-measure/Fubini and proof/paper mapping still require human review.
P4 is not human approval or independent compilation. Full build NOT_RUN.
Frozen manuscript/PDF/upload/code archives remain unchanged and OLD.

## Next precise correlated-moment card — unproved

Set Sigma=B^H B, A=M^H M, F=trace(A). Real parts are explicit when needed:

    T=m trace(Sigma)+F,
    Var(trace W)=m trace(Sigma^2)+2 Re trace(Sigma A),
    E trace(W^2)=m^2 trace(Sigma^2)+m trace(Sigma)^2
       +2m Re trace(Sigma A)+2 trace(Sigma) F+trace(A^2).

Do NOT label the last expression E[(trace W)^2]. The latter equals T^2+Var.
These candidate identities passed the controlled experiment, not Lean yet.
First derive a weighted four-coordinate Wick lemma by expanding only the
constant B coefficients in the checked shifted-fourth functional. For rows
k,l and output columns i,j the contraction of starXki*Xkj*starXlj*Xli is:

    starMki*Mkj*starMlj*Mli
    +Sigma_ij*starMlj*Mli+Sigma_ji*starMki*Mkj
    +delta_kl*(Sigma_ii*Mkj*starMlj+Sigma_jj*starMki*Mli)
    +Sigma_ij*Sigma_ji+delta_kl*Sigma_ii*Sigma_jj.

Then sum rows/columns and transport the actual polynomial integral. This
reuses the real-source factorial interface, never assumes a correlated target
density and never imports an invertible-B inverse-minimum theorem. Actual
correlated full-logdet curvature still needs its own finite-L4/spectral
instantiation (or polynomial differentiation); it is NOT established merely
by the current iid-B=I low-scale theorem. No next proof source is started yet.
