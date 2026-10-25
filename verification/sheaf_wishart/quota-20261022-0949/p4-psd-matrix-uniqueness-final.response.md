# P4 Adversarial Review

## PSDTraceNormGeometry.lean

**Mathematical gap (norm ambiguity):** The header declares "Entry-sup norm only," but the proof of `psd_entrySupNorm_le_trace_re` invokes `Matrix.norm_le_iff`. If this lemma refers to a different matrix norm (operator/Frobenius) in Mathlib, the conclusion `‖A‖ ≤ A.trace.re` does not establish entry-sup dominance. The semantic meaning of `‖A‖` must exactly match the elementwise sup-norm for the stated claim to hold. This is not an API question—it determines whether the theorem proves what it asserts.

**Minor:** `hU` uses `PiLp.norm_apply_le` on an orthonormal basis vector. This yields `‖U i k‖ ≤ 1`, which is correct but relies on the basis being normalized in the `PiLp 2` sense. No gap, but the coercion should be semantically verified against the actual eigenvector construction.

## HermitianTraceDualGeometry.lean

**No mathematical gaps identified.** The dual kernel construction, trace representation on Hermitian arguments, and norm bound `‖H‖ ≤ 2 * ‖L‖` follow from explicit real-linear expansion and triangle inequality. The symmetrization `(K + Kᴴ)/2` correctly produces a Hermitian representative. All claims are self-consistent with the entry-sup norm interpretation.

## HermitianScalarShiftPSD.lean

**Potential gap (Gershgorin application):** The proof obtains `k` from `eigenvalue_mem_ball` applied to an eigenvector `hv`, then unpacks the closed-ball condition at index `k`. Gershgorin's theorem places eigenvalues in the union of discs centered at diagonal entries with radii equal to off-diagonal row sums. The derivation `c - (H k k).re - lam ≤ ‖...‖` combined with the row-sum bound is arithmetically correct, **but** the step `have hsmall : ‖H‖ ≤ 2 := by linarith` depends critically on `hl : ‖L‖ < 1` from the calling context in `PSDMatrixLaplaceUniqueness`. Within this file alone, `hc : (n : ℝ) * ‖H‖ ≤ c` is assumed; the internal arithmetic `linarith` closing `0 ≤ lam` is valid given the explicit hypotheses. No standalone gap.

## PSDMatrixLaplaceUniqueness.lean

**Mathematical gap (measurability coercion):** The proof applies `hμ.mono fun W hW => hbound W hW` where `hbound` requires `W.PosSemidef`. However, `hμ : ∀ᵐ W ∂μ, W.PosSemidef` is an AE statement. The function `f W = c * W.trace.re` is measurable, but the domination condition `‖W‖ ≤ f W` is only established **on the PSD support**. For `W` outside the support, no bound is provided. The call to `eq_of_norm_dominated_localLaplace` requires a **global** dominating function or explicit restriction to the support set. If the imported theorem expects `∀ W, ‖W‖ ≤ f W` rather than AE-restricted dominance, this is a logical gap—not merely an API signature question—because exponential integrability over the full space is not established.

**Gap (tilt parameter range):** The proof shows `‖H‖ ≤ 2` via `hl : ‖L‖ < 1`, then derives `(n : ℝ) * ‖H‖ ≤ c = 2*n + 1`. This restricts the dual argument to `‖L‖ < 1`. The imported uniqueness theorem must actually guarantee that equality of Laplace transforms on PSD directions implies measure equality using **only** small-norm perturbations. If it requires arbitrary `L`, the specialization is incomplete.

## ActualNoncentralLaplaceCharacterization.lean

**No independent mathematical gap**, contingent on the above. The reduction to `finite_PSD_measures_eq_of_matrixLaplace` is structurally valid given the explicit hypotheses. The AE PSD support of `complexNoncentralWishart M` is asserted as an imported fact. If the domination gap in `PSDMatrixLaplaceUniqueness` is real, it propagates here.
