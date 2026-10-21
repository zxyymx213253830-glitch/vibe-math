# Fixed singular-factor logdet offset — proof and review packet

## Exact result

Let Z be m-by-p with independent proper complex CN(0,1) entries, obtained from2mp independent standard REAL Gaussian coordinates by division by sqrt2. Fix arbitrary complex B:p-by-n and M:m-by-n; rectangular, singular and zero factors are allowed. Put X=ZB+M and r=min(m,rank stacked[B;M]). All dimensions may be0. No parameter depends on rho or on the random realization.

The new ActualSingularPositiveLog.lean proves true absolute integrability of

`S(Z) = SUM_i (if lambda_i(X^H X)>0 then log(lambda_i(X^H X)) else0)`

and of each term. It then discharges the old log-moment premise and proves

`E log(Re det(I+rho X^H X)) - r log(rho) -> E S(Z)` as rho->positive infinity.

The right-hand constant is finite. It is the expected log of the product of positive eigenvalues (empty product1); the Lean conclusion uses the explicitly defined finite sum S, not a separately named pseudodeterminant object. It is not log of the singular full Gram determinant. No closed evaluation of the constant, uniformity in B,M, error rate, inverse-moment threshold or channel-coding derivation is asserted.

## Proof chain

1. Existing generic-rank assets give a deterministic maximal-rank witness Z0 and rank(X)=r AE. A rank-sized square compression of X0 has determinant1.
2. The new rectangular all-function determinant expansion and two row-extraction steps yield fixed injective coordinate maps f:Fin r->Fin m and g:Fin r->Fin n with minor nonzero at Z0. The choice is made for fixed parameters before integrating, not as a measurable random selector.
3. A physical coordinate minor equals det(LXH), with L=(I_m).submatrix f id of shape r-by-m and H=(I_n).submatrix id g of shape n-by-r. This hour's first two modules supply the coordinate witness; the prior hour's properCN1 holomorphic theorem gives absolute-log L1 of this fixed determinant.
4. Use the OLD REAL-coordinate genericAffineCompressedDet polynomial to prove actual AE nonvanishing, by evaluating it at complexSampleMean Z0. The NEW COMPLEX physical-entry polynomial supplies log L1. Their polynomial rings differ; their checked evaluations are the same determinant. No arbitrary real-source polynomial log theorem is smuggled in.
5. Permutation averaging proves `r! det(A B) = SUM_all_functions det(A[:,f])*det(B[f,:])`. For a Gram matrix this is a sum of nonnegative absolute squares. The explicit factorial multiplicity avoids the hard subset/permutation quotient. The full subset-grouped Cauchy--Binet theorem remains unproved here.
6. The pinned principal-minor coefficient identity and PSD principal-minor nonnegativity bound the selected-column Gram determinant by the degree-r coefficient c_r(X) of det(I+t X^H X). Thus `|minor|^2 <= r! c_r(X)`.
7. New unitary/polynomial spectral algebra proves c_rank is the product of nonzero eigenvalues and is strictly positive, including rank0. Its logarithm equals S after the exact checked eigenvalue reindexing.
8. On the joint AE rank/nonzero-minor event, `2log|minor| <= log(r!)+S <= log(r!)+trace` on the lower/upper comparisons separately. More explicitly S<=trace and S>=2log|minor|-log(r!). Hence

   `|S| <= trace + |log(r!)| + 2|log|minor||`.

   The actual finite sum of eigenvalues is L1; the minor log is L1; the fixed constant is integrable under the probability law. Measurability is obtained from the finite ordered eigenvalue APIs. This proves aggregate L1, then the earlier aggregate-to-mode and conditional offset results apply.

Rank0, empty source and empty Gram need no artificial fullrank or positive-dimension premise. Real.log0=0 is used only for a chosen finite-valued representative; the lower minor-log comparison is applied on the explicitly proved nonzero AE event.

## Validation and numerical controls

All six new source modules have real leaf compiler exits0 using the existing serial shared gate. Independent literal target types cover the10 spectral/minor declarations and13 further averaged-algebra/actual declarations. The sources, transitive definitions/oleans, literal checkers, final logs and exact-final review snapshots are bound in the acceptance manifests. No sorry/admit/newaxiom/native_decide/unsafe is accepted; only standard propext/Classical.choice/Quot.sound.

Prior426 exact rational-complex comparisons are reused, not recast as proofs. New permutation-average52 exact controls include empty and q>m shapes, factorial and conjugation negative controls. Its first run had an implementation-only SymPy relational expansion issue, fixed before passing. New fixed-seed2026102202/200000-sample27 controls compare rank1 singular-factor log moments with digamma(m), a rank2 singular-factor/fixed-noiseless-mean model with2log(c)-EulerGamma, known trace means, deterministic zero-factor and rank0 references. Sample error decreases are sanity checks, not a proof of expectation limits.

## Qoder review record and dispositions

All proofs are Codex. Qoder Qwen3.8-Max supplied bounded separate-family route/P4 reviews with tools disabled and no independent compilation. The raw requests, responses and receipts remain attached to this hour's evidence.

The averaged-algebra P4 mistakes the defined E.toFun(g)=g composed with sigma for E.invFun(g)=g composed with sigma inverse. The supplied source explicitly contains both fields. The product reindexing and determinant sign are therefore correct as stated. Its API/import doubts are discharged against the exact preceding rectangular expansion and real literal/leaf checks; determinant reindexing and PSD principal-submatrix APIs are present in the pinned sources. Its claimed logarithmic inequality is reversed: the actual hl is2log|minor|<=log(r!)+S. The final linarith uses all context including hl, not only the two explicitly added absolute-value inequalities. The eigenvalue reindexing unfolds the pinned definition; no unproved sorting invariance is assumed.

The first actual review request accidentally retained an algebra-only introductory scope sentence; that request is not used for final acceptance and is superseded. Its dimensional alarm also ignores submatrix selection: identity matrices before selection are m-by-m/n-by-n, but the selected L,H are r-by-m/n-by-r. The corrected-scope final response accepts the dimensions and AE/integrability chain, but speculates that positiveSpectrumLog means max(0,log x). Its actual definition is `if0<x then Real.log x else0`, and it CAN be negative. A further exact-definition follow-up is retained for final acceptance; no source change was made to accommodate the false warning.

The exact-definition follow-up returned in25.46seconds with three critical/major alarms, all false against the explicit assumptions and checked source. For q=0 it itself observes that hr forces rank0 and all eigenvalues0, then objects only to relaxing that premise; no such relaxation is in the theorem. Matrix.det0-by-0=1, the prior all-shape compressed-log theorem has no q>0 premise, and the nonzero-polynomial witness proof already treats that case without an extra split. The proposed sign objection again omits hl from the linarith context. Put L=log|minor|,C=log(q!),T=sum eigenvalues,A=|C|,B=|L|. The lower-bound target is S+T+A+2B. It is exactly

`(S+C-2L) + T + (A-C) + 2(B+L)`,

a nonnegative linear combination of the actual hl, trace nonnegativity and the two absolute-value bounds. The upper target is `(T-S)+A+2B`. This is the precise algebra the kernel checked. The final minor comment about complexSampleMean0 confuses the raw source shift with the fixed M already inside the polynomial; the shift passed to sampleEval_ne_zero_ae is exactly0, while the deterministic M remains in genericAffineCompressedDet. No mean term is deleted or duplicated. These raw false alarms are retained, not silently called approvals. No blanket model/human approval is claimed.

## Human and publication boundary

[需人工审查] Generic Gaussian null-set/Fubini assets, physical CN1 variance, deterministic witness interpretation, AE rank/nonzero-event combination, absolute-integrability domination and the inherited dominated-convergence offset theorem require human review. Model P4 is neither a human review nor an independent compiler run.

Frozen manuscript, PDF, arXiv upload and code archives are unchanged and describe an older checkpoint. Full Lake/mathlib build NOT_RUN. Linux may carry an exact source/DAG workcopy, but all kernel evidence in this packet is from the Windows serial gate. No remote push or credential migration.
