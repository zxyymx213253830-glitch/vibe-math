import JinWishartFormalization.IncompleteGamma
import JinWishartFormalization.NuttallQ

/-!
# Formula side of Theorem 1

This file encodes equations (15)--(18) of Jin--McKay--Gao--Collings.  The
matrix entries and determinant ratio are definitions, not yet a proof that
the ratio equals the smallest-eigenvalue CDF of the noncentral Wishart model.
The latter requires the missing Wishart/eigenvalue density argument.
-/

open Matrix

namespace JinWishart

/-- Nuttall-Q first index in the `i`th (one-based) row of Theorem 1. -/
def theorem1QOrder (s t : ℕ) (i : Fin s) : ℕ :=
  s + t - 2 * (i.val + 1) + 1

/-- Integer `k` such that the upper-Gamma entry in Theorem 1 has shape `k+1`. -/
def theorem1GammaIndex (s t : ℕ) (i j : Fin s) : ℕ :=
  t + s - (i.val + 1) - (j.val + 1)

/-- The `(i,j)` entry of the determinant matrix `Ψ(x)` in equation (16).
`lambda : Fin L → ℝ` lists the positive noncentrality eigenvalues. The hypotheses
`s ≤ t` and `L ≤ s` encode the paper's dimension and rank restrictions. -/
noncomputable def theorem1PsiEntry (s t L : ℕ) (_hst : s ≤ t) (_hLs : L ≤ s)
    (lambda : Fin L → ℝ) (i j : Fin s) (x : ℝ) : ℂ :=
  if hj : j.val < L then
    (Real.rpow 2
      ((((2 * (i.val + 1) : ℕ) : ℝ) - s - t) / 2) : ℂ) *
      nuttallQ (theorem1QOrder s t i) (t - s)
        (Real.sqrt (2 * lambda ⟨j.val, hj⟩)) (Real.sqrt (2 * x))
  else
    upperGammaNat (theorem1GammaIndex s t i j) x

/-- The matrix `Ψ(x)` in equation (16). -/
noncomputable def theorem1PsiMatrix (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (x : ℝ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => theorem1PsiEntry s t L hst hLs lambda i j x

/-- The determinant-ratio expression on the right-hand side of equation (15).
The nonzero-denominator and equality-to-CDF claims are intentionally not axiomatized. -/
noncomputable def theorem1CdfCandidate (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (x : ℝ) : ℝ :=
  1 - ‖(theorem1PsiMatrix s t L hst hLs lambda x).det‖ /
    ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖

end JinWishart
