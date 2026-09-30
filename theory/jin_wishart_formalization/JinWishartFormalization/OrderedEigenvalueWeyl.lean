import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# A first step toward Weyl continuity for ordered Hermitian eigenvalues

The standard perturbation argument has two parts. First, the Rayleigh quotient changes by at most
the operator norm of the perturbation. Second, the Courant--Fischer characterization transfers
that estimate to each ordered eigenvalue. This file formalizes the first part. The pinned Mathlib
version provides Rayleigh characterizations of the extreme eigenvalues, but not the indexed
Courant--Fischer theorem required for the second part.

The remaining spectral target is, for `A B : Matrix (Fin n) (Fin n) ℂ` Hermitian and
`i : Fin (Fintype.card (Fin n))`,

```
|hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖(A - B).toEuclideanLin‖.
```

An indexed Courant--Fischer theorem (with the descending-list indexing convention above) plus the
Rayleigh perturbation lemma below suffices to prove this estimate.

More precisely, for a finite-dimensional complex inner-product space `E`, a symmetric continuous
linear map `T`, `hn : finrank ℂ E = n`, and `i : Fin n`, the missing min-max statement is

```
T.eigenvalues hn i =
  ⨅ U : {U : Submodule ℂ E // finrank ℂ U = n - i.val},
    ⨆ x : {x : U // x ≠ 0}, T.rayleighQuotient x
```

The easy direction comes from the span of the eigenvectors indexed `i, …, n-1`. The other
direction uses that any subspace of dimension `n-i` has a nonzero intersection with the span of
the first `i+1` eigenvectors; this dimension-intersection step is not present as an indexed
variational theorem in the pinned Mathlib API.
-/

open InnerProductSpace

namespace JinWishart

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Pointwise Rayleigh quotients are Lipschitz in the operator, with operator norm as a bound.
This lemma does not require symmetry; symmetry is needed later to identify ordered eigenvalues
through a min-max principle. -/
theorem abs_rayleighQuotient_sub_le_operatorNorm
    (T S : E →L[𝕜] E) (x : E) :
    |T.rayleighQuotient x - S.rayleighQuotient x| ≤ ‖T - S‖ := by
  have h := (T - S).rayleighQuotient_le_norm x
  have heq : (T - S).rayleighQuotient x =
      T.rayleighQuotient x - S.rayleighQuotient x := by
    rw [sub_eq_add_neg, ContinuousLinearMap.rayleighQuotient_add,
      ContinuousLinearMap.rayleighQuotient_neg_apply]
    ring
  rw [← heq]
  exact h

/-- The Rayleigh quotient of a symmetric operator at its `i`th ordered eigenvector is the
corresponding ordered eigenvalue. This is the eigenbasis endpoint of the future indexed
min-max argument. -/
theorem rayleighQuotient_eigenvectorBasis_eq_eigenvalue
    {n : ℕ} [FiniteDimensional 𝕜 E]
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T.rayleighQuotient (hT.eigenvectorBasis hn i) = hT.eigenvalues hn i := by
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  have hEigen : T (hT.eigenvectorBasis hn i) =
      (hT.eigenvalues hn i : 𝕜) • (hT.eigenvectorBasis hn i) :=
    hT.apply_eigenvectorBasis hn i
  rw [hEigen]
  have hi := (hT.eigenvectorBasis hn).orthonormal.1 i
  simp [hi, inner_smul_left]

end JinWishart
