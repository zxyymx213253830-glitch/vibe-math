# Actual noncentral Wishart law: mean Gram and unitary transport

Three printed exports, one module, all m,n including0 and arbitrary fixed complex m-by-n means. The row count m is the same on both sides; it is not discarded as a distribution parameter.

- `complexNoncentralWishart_eq_of_meanGram_eq`: M^H M=N^H N gives equality of the actual matrix measures. Proof reuses the accepted actual Laplace characterization and support, and cycles the mean correction to Re trace((M^H M) T (I+T)^(-1)). No frame completion or density assumption.
- `complexNoncentralWishart_right_unitary_conjugation`: for fixed square U with U^H U=I, pushing actual(M) forward by W -> U^H W U gives actual(MU). Proof reuses actual Gaussian right-unitary mean law plus the pointwise Gram identity and explicit measurable map composition. No random unitary or independent Wishart eigenvalues.
- `complexNoncentralWishart_meanGram_unitary_transport`: if N^H N=U^H(M^H M)U for that fixed unitary, the same conjugate pushforward equals actual(N).

This is not equality of the untransformed matrix laws from equality of mean-Gram eigenvalues. The negative control demonstrates that distinction. Ordered-spectrum law dependence on only the sorted noncentrality eigenvalues remains a separate next target.

## Controls and checked evidence

experiments/noncentral_mean_gram_law_control.py seed2026102510:81 PASS before Lean source creation. Exact rational-complex trace cycling, row unitary matched-Gram means, right-unitary pointwise Gram conjugation, empty shapes, independent numerical sorted-eigenvalue comparison, and same Frobenius/mean-Gram-eigenvalues but different anisotropic transform negative. These are calibration, not law proofs. The first control implementation used raw structural SymPy matrix equality and failed at shape(1,3); retained failed script/failure JSON. It was repaired by exact entry simplification before comparison; the mathematical identity was not weakened. No Lean source existed before the repaired controls passed.

ActualNoncentralMeanGramLaw v1 exit0, default budget (cold elapsed147s), standard3 axioms. Immutable final shared bundle and three independent literal types PASS. No failed Lean source iterations for this module. All Lean uses collaborative_check.py/shared compute.lock serially.

## Full final-source Qoder P4 resolution

One actual Qwen3.8-Max call, tools disabled, 2026-10-25T14:01:33--14:02:04UTC; exact complete source/hash supplied. Not human review or independent compilation.

1. The response claims `(I+T)^-1` is ill-typed without invertibility in the private trace-cycling lemma. Pinned Matrix inverse is TOTAL, not a partial operation: NonsingularInverse.lean `nonsing_inv_apply_not_isUnit` explicitly makes the inverse zero for nonunit determinant. The private identity uses no inverse cancellation at all; it is trace cycling with an arbitrary n-by-n factor, so it is valid for every T, including singular I+T. When invoking the actual Laplace formula, T.PosSemidef is explicit and I+T invertibility is already proved in the accepted transform module. No missing helper hypothesis.
2. The imported `noncentralWishart_eq_of_PSD_matrixLaplace` takes a finite measure nu, AE PSD support, and equality with the explicit formula for EVERY matrix T satisfying T.PosSemidef. After `apply ... N hPSD`, `intro T hT` has exactly that typed PSD hypothesis, and it is passed directly to `noncentralWishart_PSD_matrixLaplace M T hT`. This determines the full matrix law by the accepted PSD uniqueness, not merely a few transform tests. Three literal targets independently bind the exact resulting public claims.
3. Trace cycling is applied by grouping M*T as the first factor, (I+T)^-1 as the second and M^H as the third, then associating. This is exactly the imported trace_mul_cycle signature and does not require commutativity of matrix multiplication.
4. The square condition U^H U=I is sufficient for the reused Gaussian isometric-projection law; pointwise Gram conjugation itself needs only associativity and adjoint-of-product. Right inverse completion is not silently assumed in the new proof.
5. Measurability is explicit from continuous fixed matrix multiplication and Gram, before map_map. The actual law is a pushforward of the same properCN1 raw Gaussian model; no target density premise enters.

[需人工审查] Pushforward/model/noncentrality parameter convention and eventual paper mapping. Frozen paper/PDF/upload products unchanged; fullLake/Linux independent kernel NOT_RUN. General noncentral G2 remains OPEN.
