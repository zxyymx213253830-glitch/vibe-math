2026-10-22 此卡的通用奇异偏移目标已由平均Cauchy-Binet替代路线验收闭合：608/auditPASS/facade63。下面是保留的历史路线；完整子集恒等式仍未证明，不影响已验收目标。详见WISHART_SINGULAR_LOGDET_OFFSET.md。

# Next substantive obligation: fixed coordinate minor to positive-spectrum log

Checkpoint585, fixed hour2026-10-21. This is a research card, not a proved Lean theorem.

Let X(Z)=ZB+M, with arbitrary fixed complex rectangular B,M, and r the already proved deterministic AE generic rank. The current actual compressed determinant theorem supplies absolute-log L1 for every fixed square compression. It does not yet compare that determinant with the product of positive eigenvalues of X^H X.

Proposed route avoiding a new real-Gaussian polynomial-log theorem:

1. At a fixed maximal-rank witness Z0, select coordinate row/column sets I,J of size r with det X0[I,J] nonzero. This needs an actual coordinate-minor existence lemma. The existing matrix_rank_compression returns arbitrary L,H with LX0H=1; it does NOT establish coordinate selection. Do not silently treat that result as a coordinate minor. Alternative arbitrary-L/H route needs an explicit constant C(L,H), not coefficient1.
2. Set P(Z)=det X(Z)[I,J]. Use the new holomorphic physical-entry polynomial and a nonzero witness to prove P nonzero as a polynomial and P(Z) nonzero AE. The existing product properCN1 law plus polynomial AE-null result supplies this without changing the REAL two-coordinate source convention.
3. Prove rectangular Cauchy--Binet and the coefficient identity: e_r(X^H X)=sum_{|I'|=|J'|=r}|det X[I',J']|^2. Consequently e_r>=|P|^2. Exact pinned search did not locate a ready Cauchy--Binet theorem; this is a missing proof, not an available API. Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean contains coeff_det_one_add_X_smul_eq_sum_minors, but that gives Gram principal minors only and does not discharge rectangular Cauchy--Binet.
4. On the AE rank-r event, e_r equals the product of the positive eigenvalues, since exactly r eigenvalues are positive. This coefficient/spectrum identity is another explicit deterministic obligation. Finite real-parameter determinant spectral identities exist; no polynomial coefficient identity is currently claimed.
5. Off the P=0 null set, S=sum positiveSpectrumLog(lambda_i)=log e_r satisfies 2log|P|<=S<=trace(X^H X). Therefore |S|<=trace+2|log|P||. Actual trace is L1, and new compressed log is L1. Hence S is L1. Apply the accepted aggregate-to-individual bridge and existing generic-rank expected offset theorem.
6. r=0 is handled separately: all nonnegative eigenvalues are0, S=0 and e0=1. Empty coordinate determinant=1. No minimum for n=0 is introduced.

The fixed coordinate choice depends on fixed B,M,witness, not on random Z. There is no measurable minor selector or parameter-uniform bound. Real.log0=0 never substitutes for the AE nonzero step: X=diag(1/10,0) with a zero chosen minor makes log pseudoDet<2*totalizedLog0.

Exact controls: experiments/compression_pseudodet_bridge_control.py, seed2026102126,285 comparisons across rational-complex dimensions0..4, duplicated columns, rank0, conjugation and singular-determinant negative controls. Final result compression-bridge-control-2.json. The first result predates replacement of one documentary assertion with an actual exact negative control and is retained as historical only. These controls are not a proof or an accepted extension of585.

[需人工审查] Combining AE rank and AE nonzero events, integrability domination, totalized logarithms on null sets and model interpretation. No blanket unconditional singular offset claim is made. No frozen paper or upload change.

## Real Qoder route review and explicit disposition

The bounded final route review returned in25.22seconds (Qwen3.8-Max; tools disabled, no independent compilation). It calls the inequality direction fatal while writing exactly the same equivalent inequality: the supplied `2log|P|<=S` and its derived `S>=2log|P|` are identical. The domination follows from `-S<=-2log|P|<=2|log|P||` and `S<=trace`; it does not require S to remain bounded as P tends to0, because the proposed right-hand side also grows then. This warning is false; no route revision follows from it.

Its generic-rank-locus objection is already addressed by the stated AE event and the separate nonzero-polynomial AE event; domination is required AE, not on the rank-deficient null locus. The sum uses a fixed finite spectrum and positiveSpectrumLog0=0, not an undefined varying index set. Its non-totalized-integral objection is false for a chosen finite-valued version agreeing off a null set; absolute integrability is AE invariant. Human examination of that interpretation is still required.

The request to separate the coefficient principal-minor identity from rectangular Cauchy--Binet is valid as an implementation-scope reminder and is retained in steps3/4. For each fixed column subset J of size r, apply standard rectangular Cauchy--Binet to the m-by-r matrix X[:,J], then sum over J; no Newton--Girard premise is needed. These are still unproved deterministic Lean obligations, not dismissed as syntax work.

Further pinned asset audit: Matrix/Echelon/Pivot.lean `IsPivotedBy.rank_eq` constructs a nonzero square minor of an already echelon matrix, but does not directly select a minor of the original X. It must not be cited as the missing coordinate-minor theorem. Matrix/Rank.lean exposes rank_submatrix_le and general rank-normal forms, not a ready coordinate-witness result found by this search. A clean implementation route is to establish rectangular Cauchy--Binet first, then use positivity of the rank coefficient and the finite sum of squares to obtain a nonzero coordinate minor at Z0. That removes a separate coordinate-minor existence proof but requires steps3/4 before step1 in implementation order.

## Reuse actual-source null-set proof without conflating polynomial rings

The shortest next AE-nonzero implementation can reuse the exact recipe already checked inside CorrelatedGaussianGenericRank.lean `actualCorrelatedRank_ge_witness_ae`: construct genericAffineCompressedDet in the REAL-coordinate SampleIdx m p ring, evaluate at complexSampleMean Z0, derive nonzero from the chosen deterministic minor, then apply sampleEval_ne_zero_ae with zero mean and simplify complexSampleMean0=0. This handles actual source AE nonzero directly.

The L1 theorem from this hour instead uses entryAffineCompressedDet in the COMPLEX physical-entry ring Fin m times Fin p. Both polynomials evaluate to the same physical determinant, but their polynomial types differ. No equality between these rings is required: use the old ring for AE nonzero, the new holomorphic ring for log L1, and their separate checked evaluation identities to connect the functions. Do not feed an arbitrary SampleIdx polynomial into the new properCN1 holomorphic theorem. In particular generic raw-polynomial log integrability has not been proved this hour.

Two deterministic subgoals should precede any new probability work: (i) arbitrary rectangular Cauchy--Binet over complex matrices; (ii) spectral polynomial identity and coefficient-at-rank positivity. Once they are proved, coordinate minor selection follows by finite sum positivity at the already available maximal-rank witness. This route avoids trying to upgrade an arbitrary linear compression to coordinate selection.

## More precise finite-algebra implementation plan (not checked Lean)

For A:q-by-m and B:m-by-q, row multilinearity first gives

`det(A B) = SUM(f : Fin q -> Fin m) (PROD i A[i,f(i)]) * det(B.submatrix f id)`.

This has no factorial denominator. Terms with noninjective f vanish by equal rows in the second determinant. For each image subset I of size q, choose one equivalence Fin q to I; sum over permutations of this equivalence. The permutation sign from the B-row determinant turns the remaining sum into det(A[:,I]). Thus each subset contributes exactly det(A[:,I])*det(B[I,:]), not q! times that quantity. The individual choice of ordering cancels between the two determinants; use that to avoid proving an arbitrary ordered-enumeration convention canonical.

Apply this identity to A=(X[:,J])^H and B=X[:,J]. The selected first factor is the conjugate transpose of the selected second factor, so its determinant is the conjugate; the product is an absolute square. Sum the pinned principal-minor coefficient formula over column subsets J. This derives the full minor-square identity using ordinary rectangular Cauchy--Binet plus the already available coefficient theorem. For q>m there are no injective functions; for q=0 the empty function/product/determinant contributes1. These cases must be stated, not discarded by an assumed positive rank.

For the spectral polynomial identity, generalize the existing unitary conjugation determinant argument from real r to an arbitrary complex c, obtaining det(I+cG)=PROD_i(1+c*lambda_i). Then use evaluation compatibility of the determinant polynomial and Polynomial.funext over the infinite field C. This avoids an unjustified restriction of complex polynomial log integrability to real samples and avoids needing a separate infinite set of real evaluation points. At rank r, factors for zero eigenvalues are1 and exactly r remaining factors have positive lambda. The degree-r coefficient of their product is their product and is positive; the empty product is1. None of these polynomial identities is yet covered by the585 audit bundle.

Final preflight extension: compression-bridge-control-3.json now binds the final script hash and426 passing exact comparisons. It adds the all-function row-multilinear expansion for q<=3 and an extra-factorial negative control. Earlier285-comparison files are historical versions, not current-source bindings. No count is added to585 and no general algebraic proof is asserted.
