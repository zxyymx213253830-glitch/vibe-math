# Paper Psi tail bridge: review and scope

The three locked modules establish, for natural p, L, q, nonnegative lambda and x, entrywise transport from the original formula-side Psi matrix to central and noncentral positive-tail candidate moments, including the row and column equivalences and their factors. This does not yet establish a determinant ratio or an actual Wishart spectral law. Seed 2026103006 supplied 531 independent quadrature and index/scale controls; these are not proofs. The controls preceded all three bridge sources, and followed the earlier energy-substitution draft but preceded its first Lean check.

Qoder Qwen3.8-Max received the exact locked sources in two tool-disabled P4 calls. The second receipt reports exit 0; both reviews and source hashes are retained. The user authorized autonomous Qoder collaboration. P4 is neither human review nor independent compilation.

Review adjudication against the checked sources and pinned interfaces:

* The claimed missing `a >= 0` assumption is absent from the actual `integrableOn_nuttallQ_fullNaturalMoment q k a` signature: `a` is arbitrary real. The tail restriction uses the stated nonnegative lower endpoint.
* `quadraticEnergy_tail_substitution` explicitly has only `a >= 0` as a hypothesis and states an identity for totalized Bochner integrals. It does not assert finiteness for arbitrary functions. The source separately supplies the Nuttall integrability needed for `integral_re`; the scalar weighted moments are available from the established kernel results. `integral_const_mul` and `integral_complex_ofReal` are used at their actual unconditional totalized signatures.
* Pointwise congruence of the two integrands on `Ioi x` suffices for equality of the totalized integrals; it does not itself assert integrability. The central and noncentral definitions explicitly branch on `0 < y`, which follows from `0 <= x < y`. `scalarSeriesKernel` explicitly takes natural order then real lambda then real y, matching the call. Its series definition is exactly the noncentral branch.
* `Real.sqrt` is total in Lean and cannot produce NaN. The transport theorem explicitly assumes every lambda nonnegative; no assertion is made about positivity of its scaling factor without stronger assumptions. The paper matrix and the real-to-complex map both have codomain `Complex`; there is no alternate complex structure.
* The row arithmetic is checked against the imported `mixedMomentDegree` definition with `Fin.val_rev` and `omega`; the column identity is similarly checked against the actual equivalence. Any later dependency changes require rerunning the hash-locked checks. The natural cast arithmetic is proved in the stated natural domain.

[需人工审查] Improper integrals, Fubini inherited by kernel moments, exact paper parameter/index conventions, and the mapping from the candidate measure to the actual random-matrix model. Frozen publication artifacts unchanged; full Lake build and independent Linux kernel remain NOT_RUN.
