import JinWishartFormalization.NoncentralRadialFullMoments
import JinWishartFormalization.Theorem1Formula
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Codex. Seed2026102604 exact controls precede source. The ORIGINAL Psi(0)
matrix becomes a finite polynomial/Gamma-factorial matrix. This is not a
determinant evaluation, normalization nonvanishing, or actual joint-law theorem.
[需人工审查] Source formula and noncentrality/variance conventions. -/
open Matrix
namespace JinWishart
noncomputable section

def theorem1ZeroMomentMatrix (s t L : ℕ) (lambda : Fin L → ℝ) :
    Matrix (Fin s) (Fin s) ℂ :=
  fun i j => if hj : j.val < L then
    ((Real.rpow (lambda ⟨j.val,hj⟩) (((t-s : ℕ) : ℝ)/2) : ℝ) : ℂ)*
      (poissonFactorialMomentPolynomial (t-s) (s-(i.val+1)) (lambda ⟨j.val,hj⟩) : ℂ)
  else (Nat.factorial (theorem1GammaIndex s t i j) : ℂ)

private theorem zeroMoment_prefactor (s t : ℕ) (hst : s ≤ t) (i : Fin s)
    (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow 2 ((((2*(i.val+1) : ℕ) : ℝ)-s-t)/2)*
      (Real.sqrt (2*x))^(t-s)*(2 : ℝ)^(s-(i.val+1)) =
        Real.rpow x (((t-s : ℕ) : ℝ)/2) := by
  have hs : (Real.sqrt (2*x))^(t-s) =
      Real.rpow 2 (((t-s : ℕ) : ℝ)/2)*Real.rpow x (((t-s : ℕ) : ℝ)/2) := by
    calc
      _ = Real.rpow (2*x) (((t-s : ℕ) : ℝ)/2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = _ := Real.mul_rpow (by norm_num) hx
  have he : ((((2*(i.val+1) : ℕ) : ℝ)-s-t)/2)+
      (((t-s : ℕ) : ℝ)/2)+((s-(i.val+1) : ℕ) : ℝ) = 0 := by
    rw [Nat.cast_sub hst, Nat.cast_sub (show i.val+1 ≤ s by omega)]
    push_cast
    ring
  rw [hs, ← Real.rpow_natCast (2 : ℝ) (s-(i.val+1))]
  calc
    _ = (Real.rpow 2 ((((2*(i.val+1) : ℕ) : ℝ)-s-t)/2)*
        Real.rpow 2 (((t-s : ℕ) : ℝ)/2)*Real.rpow 2 ((s-(i.val+1) : ℕ) : ℝ))*
          Real.rpow x (((t-s : ℕ) : ℝ)/2) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num), he,
        Real.rpow_zero, one_mul]

theorem theorem1PsiMatrix_at_zero_eq_finiteMoments (s t L : ℕ)
    (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ)
    (hLambda : ∀ j, 0 ≤ lambda j) :
    theorem1PsiMatrix s t L hst hLs lambda 0 = theorem1ZeroMomentMatrix s t L lambda := by
  ext i j
  unfold theorem1PsiMatrix theorem1PsiEntry theorem1ZeroMomentMatrix
  by_cases hj : j.val < L
  · rw [dif_pos hj, dif_pos hj]
    have ho : theorem1QOrder s t i = (t-s)+2*(s-(i.val+1))+1 := by
      unfold theorem1QOrder
      omega
    have ha : (Real.sqrt (2*lambda ⟨j.val,hj⟩))^2/2 = lambda ⟨j.val,hj⟩ := by
      rw [Real.sq_sqrt (by positivity)]
      ring
    have hc := congrArg (fun y : ℝ => (y : ℂ))
      (zeroMoment_prefactor s t hst i (lambda ⟨j.val,hj⟩) (hLambda _))
    push_cast at hc
    rw [ho, nuttallQ_fullNaturalMoment, ha]
    calc
      _ = (((Real.rpow 2 ((((2*(i.val+1) : ℕ) : ℝ)-s-t)/2) : ℝ) : ℂ)*
          (Real.sqrt (2*lambda ⟨j.val,hj⟩) : ℂ)^(t-s)*(2 : ℂ)^(s-(i.val+1)))*
          (poissonFactorialMomentPolynomial (t-s) (s-(i.val+1)) (lambda ⟨j.val,hj⟩) : ℂ) := by ring
      _ = _ := by rw [hc]
  · rw [dif_neg hj, dif_neg hj, upperGammaNat_at_zero_eq_factorial]

end
end JinWishart
#print axioms JinWishart.theorem1PsiMatrix_at_zero_eq_finiteMoments
