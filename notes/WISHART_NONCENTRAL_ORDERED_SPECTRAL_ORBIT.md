# Actual noncentral ordered-spectrum law: mean-Gram spectral orbit

Five printed declarations in two modules. Same arbitrary m,n on both sides;
fixed complex means M,N. If the complete descending eigenvalue vectors of
M^H M and N^H N agree, the complete n-coordinate descending column-Gram
eigenvalue vectors have equal laws under the original 2mn real Gaussian source.
Zero dimensions, repeated/zero noncentrality eigenvalues and wide structural
zeros are included. This is equality of joint vector measures, without any
Wishart eigenvalue independence or joint-density premise.

HermitianSpectralOrbit proves sorted eigenvalue equality from charpoly equality,
unitary conjugation invariance, and existence of a fixed unitary conjugacy from
equal sorted eigenvalues. The chosen U is U_A U_B^H. ActualNoncentralSpectralOrbitLaw
lifts the accepted matrix-law transport to the Hermitian subtype by injectivity
of its inclusion pushforward, then applies the measurable ordered spectrum map.
The closed Hermitian subtype avoids an arbitrary spectrum extension on other matrices.

The untransformed matrix laws need not be equal from only equal mean-Gram
eigenvalues. The same-Gram law theorem and its unitary transport remain separate.
This result retains all n column-Gram coordinates; the paper's small-side
Fin(min m n) and rank-L positive noncentrality convention still require mapping.
No general noncentral G2 density has been identified.

## Controls and verification

experiments/noncentral_spectral_orbit_control.py seed2026102511:140 PASS before
new Lean source. Exact rational-complex spectral-basis orbit/charpoly controls,
repeated/zero/signed spectra, rectangular physical Gram coupling, zero dimensions,
and an anisotropic Laplace negative separating matrix law from spectral law.
Controls calibrate conventions; they are not proofs.

HermitianSpectralOrbit v4 and ActualNoncentralSpectralOrbitLaw v3 exit0 at the
default budget, standard3 axioms. Earlier failed versions and logs are retained,
not accepted: coercion/star instance, dependent rewrite, a qualified unitary
lemma name, and a map-injectivity namespace/composition rewrite were repaired.
No budget upgrade or concurrency. Five independent literal types and the
immutable final shared bundle PASS. All Lean uses collaborative_check.py with
the same compute.lock serially.

## Full final-source Qoder P4 resolution

One actual bounded Qwen3.8-Max call, tools disabled, 2026-10-25T14:24:05--14:24:27UTC.
Both complete final source hashes were supplied. This is not human review or
independent compilation.

The response's sole potential issue asks whether eigenvalues in the spectral
diagonalization could be a different permutation of eigenvalues_0. Pinned
Mathlib/Analysis/Matrix/Spectrum.lean lines67--68 define eigenvalues i as
eigenvalues_0 ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i). This is the
SAME fixed reindexing for A and B. The new proof explicitly unfolds this
definition and rewrites the assumed equality to obtain he : hA.eigenvalues =
hB.eigenvalues. The spectral theorem at lines143--145 uses precisely these
eigenvalues in its diagonal. Thus he identifies the diagonals, not merely their
multisets; no simple-spectrum assumption or sample-dependent choice occurs.

The imported complexNoncentralWishart_meanGram_unitary_transport takes exactly
fixed M,N,U, U^H U=I and N^H N=U^H(M^H M)U, with no rank or positive-dimension
hypotheses. The new U has these properties by construction and unitary membership.
The reviewer found no other mathematical gaps. Measurability, inclusion
injectivity and all map compositions are explicit in the checked source.

[需人工审查] Borel subtype transport, spectral indexing and paper noncentrality
mapping. Frozen publication products unchanged; fullLake and Linux independent
kernel NOT_RUN. General surplus>2 original T1/general G2/general T2/journal T3
and full paper mapping remain OPEN.
