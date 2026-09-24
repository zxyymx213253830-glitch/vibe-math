import JinWishartFormalization.IncompleteGamma
import JinWishartFormalization.NuttallQ

/-!
# Formula side of Theorem 1

This file encodes equations (15)--(18) of Jin--McKay--Gao--Collings.  The
matrix entries and determinant ratio are definitions, not yet a proof that
the ratio equals the smallest-eigenvalue CDF of the noncentral Wishart model.
The latter requires the missing Wishart/eigenvalue density argument.
-/

open Matrix MeasureTheory Set

namespace JinWishart

/-- Nuttall-Q first index in the `i`th (one-based) row of Theorem 1. -/
def theorem1QOrder (s t : ℕ) (i : Fin s) : ℕ :=
  s + t - 2 * (i.val + 1) + 1

/-- Integer `k` such that the upper-Gamma entry in Theorem 1 has shape `k+1`. -/
def theorem1GammaIndex (s t : ℕ) (i j : Fin s) : ℕ :=
  t + s - (i.val + 1) - (j.val + 1)

/-- The `(i,j)` entry of the determinant matrix `Ψ(x)` in equation (16).
`lambda : Fin L → ℝ` is intended to list the positive noncentrality eigenvalues. The current
definition does not enforce positivity or strict ordering of this list; these paper hypotheses
remain an obligation when using the candidate. `s ≤ t` and `L ≤ s` encode the dimension/rank
restrictions. -/
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

/-- The `(i,j)` entry of the matrix `Ξ(x)` in equation (20), using the lower
incomplete Gamma integral from mathlib for the zero-noncentrality columns. -/
noncomputable def theorem2XiEntry (s t L : ℕ) (_hst : s ≤ t) (_hLs : L ≤ s)
    (lambda : Fin L → ℝ) (i j : Fin s) (x : ℝ) : ℂ :=
  if hj : j.val < L then
    (Real.rpow 2
      ((((2 * (i.val + 1) : ℕ) : ℝ) - s - t) / 2) : ℂ) *
      (nuttallQ (theorem1QOrder s t i) (t - s)
          (Real.sqrt (2 * lambda ⟨j.val, hj⟩)) 0 -
        nuttallQ (theorem1QOrder s t i) (t - s)
          (Real.sqrt (2 * lambda ⟨j.val, hj⟩)) (Real.sqrt (2 * x)))
  else
    Complex.partialGamma
      ((theorem1GammaIndex s t i j + 1 : ℕ) : ℂ) x

/-- The matrix `Ξ(x)` in equation (20). -/
noncomputable def theorem2XiMatrix (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (x : ℝ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => theorem2XiEntry s t L hst hLs lambda i j x

/-- Formula side of equation (19), the largest-eigenvalue CDF determinant ratio.
As with `theorem1CdfCandidate`, no equality to the Wishart probability is asserted here. -/
noncomputable def theorem2CdfCandidate (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (x : ℝ) : ℝ :=
  ‖(theorem2XiMatrix s t L hst hLs lambda x).det‖ /
    ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖

/-- Entrywise relation behind the passage from the smallest-eigenvalue tail determinant
to the largest-eigenvalue CDF determinant: `Ξ(x) = Ψ(0) - Ψ(x)`. -/
theorem theorem2XiEntry_add_theorem1PsiEntry
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ)
    (i j : Fin s) (x : ℝ) :
    theorem2XiEntry s t L hst hLs lambda i j x +
        theorem1PsiEntry s t L hst hLs lambda i j x =
      theorem1PsiEntry s t L hst hLs lambda i j 0 := by
  by_cases hj : j.val < L
  · simp [theorem2XiEntry, theorem1PsiEntry, hj]
    ring
  · simp [theorem2XiEntry, theorem1PsiEntry, hj]
    rw [upperGammaNat_zero_eq_GammaIntegral]
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using
      upperGammaNat_add_partialGamma (theorem1GammaIndex s t i j) x

/-- Matrix form of the entrywise identity `Ξ(x) + Ψ(x) = Ψ(0)`. -/
theorem theorem2XiMatrix_add_theorem1PsiMatrix
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ) (x : ℝ) :
    theorem2XiMatrix s t L hst hLs lambda x +
        theorem1PsiMatrix s t L hst hLs lambda x =
      theorem1PsiMatrix s t L hst hLs lambda 0 := by
  ext i j
  exact theorem2XiEntry_add_theorem1PsiEntry s t L hst hLs lambda i j x

/-- On a positive-noncentrality column, the `Q(0)-Q(sqrt(2x))` term in `Ξ(x)` is
the corresponding finite-interval integral. The tail-integrability premise is explicit;
proving it for all paper parameters remains open. -/
theorem theorem2XiEntry_active_eq_intervalIntegral
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ)
    (i j : Fin s) (x : ℝ) (hj : j.val < L)
    (hint : IntegrableOn
      (nuttallQIntegrand (theorem1QOrder s t i) (t - s)
        (Real.sqrt (2 * lambda ⟨j.val, hj⟩))) (Ioi 0)) :
    theorem2XiEntry s t L hst hLs lambda i j x =
      (Real.rpow 2
        ((((2 * (i.val + 1) : ℕ) : ℝ) - s - t) / 2) : ℂ) *
        ∫ u in (0 : ℝ)..Real.sqrt (2 * x),
          nuttallQIntegrand (theorem1QOrder s t i) (t - s)
            (Real.sqrt (2 * lambda ⟨j.val, hj⟩)) u := by
  simp only [theorem2XiEntry, dite_eq_left hj]
  rw [nuttallQ_sub_eq_intervalIntegral _ _ _ 0 (Real.sqrt (2 * x))
    (Real.sqrt_nonneg _) hint]

@[simp]
theorem theorem2XiEntry_zero
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ)
    (i j : Fin s) :
    theorem2XiEntry s t L hst hLs lambda i j 0 = 0 := by
  by_cases hj : j.val < L <;> simp [theorem2XiEntry, hj]

@[simp]
theorem theorem2XiMatrix_zero
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ) :
    theorem2XiMatrix s t L hst hLs lambda 0 = 0 := by
  ext i j
  simp [theorem2XiMatrix]

/-- Theorem 2's candidate has the correct zero-threshold value whenever its
normalizing determinant is nonzero. The algebraic Lean candidate also reduces to zero
without this assumption because real division is totalized at a zero denominator; that
degenerate case is not an interpretation of the paper's ratio. -/
theorem theorem2CdfCandidate_zero
    (s t L : ℕ) [Nonempty (Fin s)] (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) :
    theorem2CdfCandidate s t L hst hLs lambda 0 = 0 := by
  simp [theorem2CdfCandidate, theorem2XiMatrix_zero]

/-- Theorem 1's determinant-ratio candidate is normalized to zero at threshold zero,
provided the normalizing determinant is nonzero. -/
theorem theorem1CdfCandidate_zero
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ)
    (hden : ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖ ≠ 0) :
    theorem1CdfCandidate s t L hst hLs lambda 0 = 0 := by
  simp [theorem1CdfCandidate, hden]

end JinWishart
