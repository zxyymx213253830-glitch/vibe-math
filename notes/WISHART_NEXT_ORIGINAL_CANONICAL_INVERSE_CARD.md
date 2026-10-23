# Next original-model inverse transport card

Established by canonical product criterion732 (5fc8975): a,b,c>0, fixed invertible N, arbitrary fixed complex means, independent proper-CN1 blocks A and H, D=[[A,0],[H,N]], and fixed column index i+1=min(a+c,b+c). The inverse real p moment is finite iff p<max(a,b)-min(a,b)+1. CanonicalMatrixProductInverse734 (e008629) is accepted: auditPASS/facade97 realexit0,70 acceptance records validated; its matrix-product-law criterion and critical/higher nonnegative ENNReal TOP statement are closed. The source controls are reused, not new experiments.

This card replaces completed Fin/shear/rank work. Do NOT redo compression, fixed-normal-form existence, rectangular Gaussian projection, disjoint block product law, Fin column transport, canonical rank, Gaussian factor moments or the product-section lemma.

## Exact remaining assembly

1. The actual physical pair of 11/21 blocks has law complexGaussianMatrixLaw MA product complexGaussianMatrixLaw MH by canonical_physical_sample_block_law, on the original 2mp real source. The matrix-product criterion is deliberately expressed on that exact target law. Use integrable_map_measure with the measurable inverse spectral function. Reconstruct the full canonical Fin block from the pair, fixed zero block and fixed N using the pointwise physical identity. This is a measure pushforward, not an assumption of iid entries after the nonunitary column map T.

2. For compressed/common-kernel-zero B,M, actual_canonical_fin_positive_bounds_ae already gives original and canonical positive-coordinate AE positivity and two-sided FIXED finite C(F)/C(F inverse) comparison, under rank stacked[B;M]=n. The old integrable_inverse_rpow_iff_of_comparison uses all-sample bounds; do not incorrectly feed AE bounds to it. Prove the corresponding AE domination privately (or use an existing appropriate AE lemma) using Integrable.mono' and AE positivity. No new tail proof is needed.

3. The normal form supplies bijective N.toEuclideanLin. Derive IsUnit N.det by injectivity of mulVec after the explicit WithLp conversion, using the already checked pattern from canonical_reindexed_column_det_isUnit. T detunit/Fin representation are already done. Column reindex ec is a bijection of all columns, never arbitrary column deletion.

4. Before normalizing an original pair with a common kernel, use the SAME fixed isometric compression C and SAME original 2mp source. Its reconstructing identities and r=rank stacked[B;M] imply compressed full stacked column rank (the proof used in correlated_fixed_compression_joint_injective already has rank(A*C)=r). Reuse the accepted AE equality of fixed original/compressed minimum-positive coordinates. Do not declare ZBC iid. The normal form applies to BC/MC while Z remains m-by-p.

5. For b=rankB>0 and 0<c=rank(M restricted kerB)<m, a=m-c>0. The canonical threshold equals |a-b|+1=|m-b-c|+1 (natural max-minus-min form avoids subtraction underflow). Check this arithmetic explicitly. R=min(m,b+c)>0 selects a fixed original boundary index R-1. Stacked dimension b+c can exceed m; the wide boundary is m-1, never the final structural zero.

6. Remaining edge branches must be explicit. c=0 is not covered by the two-positive-block minimum theorem: use the rectangular fixed isometry projection law and the tall/wide IID criterion without inventing an N minimum. b=0 gives a deterministic matrix M and, when its positive rank R>0, all positive inverse moments are finite. c=m gives a surjective noiseless restricted block and can reuse CorrelatedNoiselessInverseMoments/row-Gram domination; no a>0 Gaussian minimum is available. R=0 has no minimum-positive variable. Existing noiseless and invertible-column results must be searched before any new proof.

7. Critical/higher divergence must be stated for a nonnegative ENNReal lower integral, with measurable integrand and nonnegativity, after transporting nonintegrability. Do not describe the totalized real Bochner integral as infinity. The canonical matrix-product critical theorem supplies this distinction on the canonical law; original-source transfer still needs the corresponding map/AE argument.

## Evidence and review requirements

The accepted identities and comparisons are kernel checked under the shared serial gate, with source/dependency hashes and real Qoder different-family P4. Current accepted baseline732:730 theorem/instance+2 older constructions; cumulative122 printed declarations/51 modules is not122 probability breakthroughs. Full Lake/mathlib and independent Linux kernel NOT_RUN. Frozen publication artifacts are unchanged and old. [需人工审查] Source normalization, fixed means, AE rank/index selection, measurability, Fubini/product sections, covariance and original theorem/paper interpretation. Canonical criterion is not yet the final arbitrary singular B theorem.
