# PSD matrix Laplace uniqueness and the actual noncentral characterization

Six printed exports in five modules. This closes the PSD specialization left OPEN at915; it does not verify an original G2 density candidate.

## Exact results

1. `psd_entry_norm_le_trace_re`: every entry of a finite complex PSD matrix has norm <= real trace.
2. `psd_entrySupNorm_le_trace_re`: the elementwise entry-sup matrix norm is <= real trace, including dimension0. All new geometry explicitly opens Matrix.Norms.Elementwise, not Frobenius/L2Operator.
3. `exists_hermitian_trace_dual_norm_le`: every continuous REAL linear functional L on the full complex matrix space has a fixed Hermitian H with L(W)=Re trace(H W) on ALL Hermitian W and entry-sup norm(H)<=2*operatorNorm(L). The construction expands real/imaginary elementary matrices into a kernel K, then symmetrizes (K+K^H)/2. No complex-linearity assumption.
4. `hermitian_scalar_shift_posSemidef`: for Hermitian H and real c>=n*entrySupNorm(H), cI-H is PSD. Pinned Gershgorin bounds the eigenvalues of cI-H using its off-diagonal row sums. Dimension0 is included without choosing an eigenvector.
5. `finite_PSD_measures_eq_of_matrixLaplace`: two finite nonnegative Borel measures on all complex n-by-n matrices, each AE supported on PSD, are equal if their real negative-exponential trace integrals agree for EVERY fixed PSD test T. No probability normalization, positive dimension, rank or absolute-continuity assumption. Proof uses c=2n+1, f(W)=c Re trace(W), the norm bound, the Hermitian representative of each dual of norm<1 and the already accepted norm-dominated local Laplace uniqueness.
6. `noncentralWishart_eq_of_PSD_matrixLaplace`: any finite PSD-supported measure with the explicit actual formula
   detNorm(I+T)^(-m) * exp(-Re trace(M T (I+T)^(-1) M^H))
   for ALL PSD T equals complexNoncentralWishart M. All m,n and fixed complex M are included, including zero shapes and singular Gram laws. This reuses the already proved actual properCN1 transform and existing PSD-support theorem. The inverse is only I+T. Candidate finite mass/support/transform remain explicit hypotheses, not proofs of a candidate G2 density.

## Reproducibility and kernel evidence

experiments/psd_dual_trace_geometry_control.py seed2026102509:168 PASS before new source creation. SymPy exact trace-dual and anchor identities with complex rational coefficients; independent PSD numerical checks for zero/rank-deficient shapes, trace domination and uniform perturbation; 2x2 imaginary-Hermitian eigenvalue calibration; wrong transpose and unsymmetrized-kernel negatives. Controls are not proofs.

Final leaf versions: PSDTraceNormGeometry v4, HermitianTraceDualGeometry v8, HermitianScalarShiftPSD v4, PSDMatrixLaplaceUniqueness v5 and ActualNoncentralLaplaceCharacterization v1 exit0, standard3 axioms. Six separately written literal types pass, and the immutable final shared bundle rechecks all five complete modules and those six types. Failed drafts/diagnostic files/logs remain outside accepted targets. No budget increase/direct or concurrent Lean.

The Matrix alias is semireducible in the pinned version. An explicit standard `ContinuousLinearMap.hasOpNorm` instance fixes matrix-dual instance indexing. `convert ...; rfl` discharges definitional instance/coercion differences, and explicit Pi Borel/second-countable/complete instances instantiate the generic uniqueness theorem. An attempted local reducibility annotation was rejected in a retained FAILED draft; the final sources contain neither unsafe reducibility overrides nor altered mathlib. These are elaboration repairs, not extra hypotheses or replacement norms.

## Full-source Qoder P4 resolution

One actual Qwen3.8-Max call, tools disabled, 2026-10-25T13:46:48--13:47:13UTC. All five final source bodies were supplied, hashes match the final bundle. This is bounded adversarial assistance, not human review or independent compilation.

- Norm ambiguity: final source explicitly opens `Matrix.Norms.Elementwise`. Pinned Analysis/Matrix/Normed.lean norm_def and norm_le_iff state the sup-of-entry norms characterization; no L2/Frobenius substitution occurs. All-dual operator norms use this domain norm. Independent literal type targets use the same explicit scope/standard instance.
- Eigenvector normalization: pinned Spectrum.eigenvectorBasis is an OrthonormalBasis in EuclideanSpace; eigenvectorUnitary_apply gives its coordinates. PiLp.norm_apply_le bounds a coordinate by the Euclidean norm1. This controls entries of U and is separate from the entry-sup norm used for A/H.
- Gershgorin: the standalone lemma assumes c>=n*norm(H), and explicitly constructs a nonzero eigenvector for each eigenvalue, bounds its closed-disc real part and row sum, then derives lambda>=0. The review's mention of the calling context is not a missing standalone hypothesis. The matrix-uniqueness proof separately proves the assumed bound from norm(H)<=2*norm(L), norm(L)<1 and c=2n+1.
- AE domination: the imported DominatedLocalLaplaceUniqueness export explicitly assumes `forall-ae x under mu, norm(x)<=f(x)` AND the corresponding condition under nu, not a global pointwise bound. hmu.mono and hnu.mono supply exactly these. Outside-PSD null sets require no pointwise bound. Positive exponential tilting respects AE equality.
- Parameter range: the exact imported hypothesis is ALL continuous linear L with norm(L)<1. Its proof considers t*L near t=0 in EACH arbitrary dual direction, applies scalar local-MGF uniqueness, and uses the full dual characteristic function. No arbitrary-large L equality or common MGF neighborhood is required. The stronger ALL PSD matrix-test hypothesis supplies every needed small perturbation, whose PSD status is proved.
- Actual model: existing complexNoncentralWishart_measure_posSemidef is a proved Gaussian-Gram pushforward support result, all shapes. Existing noncentralWishart_PSD_matrixLaplace is already accepted. The new export remains a conditional law characterization and makes no unproved candidate finite-mass/support/transform assertion.

[需人工审查] AE support, finite-dimensional Borel/dual structures, inherited scalar analytic continuation/tilting and original model/paper mapping. Frozen paper/PDF/upload products unchanged. FullLake and independent Linux kernel NOT_RUN.

## Next work

Do not redo PSD uniqueness, generic tilting or the actual matrix Laplace formula. A useful next model bridge is dependence of the actual law on mean Gram M^H M and right-unitary transport toward ordered noncentrality parameters. First search exact current assets and calibrate with a new seed, then prove. Original general noncentral G2 still needs a verified candidate transform/normalization; characterization alone cannot establish that density.
