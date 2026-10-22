# Finite holomorphic Gaussian polynomial log-square — 2026-10-22

Nine new Codex declarations in four modules complete the finite-dimensional extension of the earlier one-variable negative-log-square bound. For every finite index setI and every fixed complex holomorphic polynomialP,

    E[(Real.log ||P||)^2] < infinity

in the precise sense that the squared real logarithm is Bochner-integrable. The result holds under the independent planar stdGaussian(C) product (complex second moment2) AND, after explicit scaling of both real coordinates by1/sqrt2, the independent properCN1 product. It is transported to holomorphic polynomials in the actual matrix entries and to every fixed compressed determinant det(L(ZB+M)H), with arbitrary compatible finite shapes and fixed complex B,M,L,H. No rank, nonzero-polynomial or positive-dimension hypothesis is imposed on these literal totalized-log statements. Real.log0=0, including identically zero determinants; this is not a theorem about extended-real log0=-infinity.

This checkpoint does not yet prove square integrability of the SUM of positive-spectrum logarithms for arbitrary singular factors, nor its centered variance. A fixed compression log-square does not automatically give that result without a rank-sized nonzero minor and the correct domination argument. No fluctuation limit, CLT, inverse-moment threshold, channel coding or parameter-uniform bound is claimed.

## Proof mechanism

The parameterized section theorem assumes joint measurability of(a,z)↦P_a(z), square-L1 of the negative logarithm of its leading coefficient, and an AE deterministic degree boundD. It proves square-L1 jointly and the explicit estimate

    integral neglog(P_a(z))^2 <= 2 integral neglog(leadingCoeff P_a)^2 + D^2/2.

Root factorization is only used within each FIXED univariate section. No measurable root choice is made. The inner section integral and its norm are controlled by the displayed measurable/integrable coefficient expression; integrable_prod_iff and integral_prod use the SAME order: outera, innerz.

For n variables, finSuccEquiv treats a polynomial as univariate in one coordinate with(n-1)-variable polynomial coefficients. The induction hypothesis atn applies to EVERYn-variable polynomial, regardless of degree; it therefore applies to the leading coefficient without double induction or a lower-degree premise. The separately proved nonzero-polynomial evaluation AE theorem makes the evaluated leading coefficient nonzeroAE when mapping leading coefficients. Degree can only drop under evaluation, so the original univariate degree supplies a deterministic bound. The zero polynomial is handled explicitly.

Polynomial norm-square integrability follows from the already proved integrability ofP^2 and ||P^2||=||P||^2. The elementary bound(logu)^2<=2u^2+2max(0,-logu)^2 foru>=0 then gives full log-square integrability. This is not an inference thatL1 impliesL2.

Fintype reindexing, polynomial substitutionx_i↦x_i/sqrt2, and the checked physical entry pushforward law give the properCN1/actual-matrix results. Compressed determinant evaluation is an exact ring-hom/matrix identity, not a density ansatz. Fixed meanM is a polynomial constant and is retained even when the source dimensionp is0.

## Controls and verification

The earlier planar control has200000 samples/28 tests and remains audit-bound. New fixed-seed2026102208 properCN1 controls add200000 samples/10 tests: products ofn0..3 coordinates against meanlog=-EulerGamma/2 and variancepi^2/24; an actual fixed singular factorB=[1,0] with a noiseless columnc e2 has compressed minorc z1 and log-square meanpi^2/24+(logc-EulerGamma/2)^2; its Gram positive-log square is independently compared against pi^2/6+(2logc-EulerGamma)^2. The latter is a future spectral-bridge control, not a theorem asserted here. Physical entry secondmoment1, empty determinant and wrong-normalization controls are included. Numerical evidence is not a general proof.

All final leaves and nine independent literal expected types pass the existing serial Windows gate with only the standard three axioms. Full source/definition/project-olean, pinned toolchain/manifest and expected-type hashes are locked. Initial failed logs record a product-type token spacing issue and an evaluation-power rewrite under an integrability binder; final pointwise AE rewriting fixes the implementation. No final-source bytes changed after P4 snapshots. Complete Lake/mathlib and independentLinuxkernel builds remain NOT_RUN.

## Qoder P4 dispositions

Real Qoder Qwen3.8-Max final-source P4 used full exact source, disabled tools/MCP, zero retries and no independent compilation. All raw warnings are retained; these are author dispositions, not blanket approval:

1. Alleged Fubini direction mismatch: false. hinner is exactly Integrable(a↦integral_z ||g(a,z)||), and each a-section is integrable in z. These are the two hypotheses of the used integrable_prod_iff. integral_prod g hi produces the same outera/innerz expression. The later integral_mono_ae uses hi.integral_prod_left and the coefficient majorant in a. There is no swapped outerz integral in this proof.
2. Alleged pointwise coefficient control missing: the imported one-variable polynomial theorem takes ONLY a fixed polynomialP and outputs its estimate in terms of the ACTUAL leading-coefficient negative log and degree; it has no parameter-integrability premise. Each pointwise section estimate is valid for everya, retaining its coefficient value. The global coefficient-squareL1 hypothesis is used later to integrate that majorant. A coefficient bound at eacha by a fixed constant is unnecessary.
3. The reviewer recognizes degree cannot increase under coefficient evaluation. The exact pinned natDegree_map_le is used with no extra assumption. The independent type/proof check verifies the API application.
4. It correctly recognizes the zero polynomial branch and totalized-log convention.
5. It finds the scalar deterministic log-square domination sound.
6. The real scalar action onC multiplies BOTH real and imaginary components by the same1/sqrt2; the substitution equality explicitly uses Complex.real_smul. standardComplexPiLaw_eq_planarMap and complexMatrixEntries_law are separately checked exact definitions of the properCN1 physical law. The source Gaussian itself remains a REAL standardGaussian with covarianceI; only complex entries are scaled.
7. Its map-integrability direction concern is false: integrable_map_measure states integrability ofg underpushforward iff integrability ofg composed with the map under the source, with the given measurability conditions. After rewriting the proper law as that pushforward, `.mpr` reduces the goal to the composed planar polynomial. No measurable embedding or injectivity premise is required.
8. It notes dimensional degeneracy but incorrectly saysq>min(m,p,n) forces an identically zero determinant. The source dimensionp does NOT bound rank when fixedM is present. Counterexample:p=0,m=n=q=1,M=[2],L=H=[1] gives constant determinant2 and log-square(log2)^2, althoughq>p. Only the compatible actual matrix shapes enter the proved theorem, with no such false rank bound. Identically zero determinants that do occur are handled by totalizedlog0, not by this false dimensional rule.
9. The exact entryAffineCompressedDet_eval signature quantifies arbitrary fixed compatibleB,M,L,H and physical sourcez, with no hidden rank/remainder condition. Its polynomial is the determinant of the explicitly affine entry matrix; map_det/map_mul/map_add establish the exact equality. It is source/olean locked and is the sole rewrite used in the compressed-log-square specialization.

[需人工审查] Parameter measurability, AE leading-coefficient sets, product/Fubini transport, variance and physical/model/paper correspondence remain. The theorem concerns fixed holomorphic polynomials or fixed affine compositions, not arbitrary unspecified degenerate Gaussian laws. Frozen manuscript/PDF/upload/code archives unchanged; no new article or arXiv upload is produced.
