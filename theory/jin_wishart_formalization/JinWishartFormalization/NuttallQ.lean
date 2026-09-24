import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Nuttall Q integral layer

The paper's Nuttall Q function uses the modified Bessel function `I_q` at
nonnegative integer order.  Mathlib provides complex `J_q`; for integer order
we define `I_q(z) = (-i)^q J_q(i z)`.  The tail integral is defined literally.
The parameter-dependent integrability estimates needed to discharge the
explicit hypotheses below remain separate work.
-/

open MeasureTheory Set

namespace JinWishart

/-- Modified Bessel function `I_q` at natural (hence nonnegative integer) order. -/
noncomputable def modifiedBesselI (q : ℕ) (z : ℂ) : ℂ :=
  (-Complex.I) ^ q * Complex.besselJ (q : ℂ) (Complex.I * z)

@[simp]
theorem modifiedBesselI_zero (q : ℕ) :
    modifiedBesselI q 0 = if q = 0 then 1 else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [modifiedBesselI, Complex.besselJ_zero]
  · simp [modifiedBesselI, Complex.besselJ_zero, hq]

/-- Integrand in the Nuttall Q function used by the complex noncentral Wishart formulas. -/
noncomputable def nuttallQIntegrand (p q : ℕ) (a t : ℝ) : ℂ :=
  (t : ℂ) ^ p * (Real.exp (-((t ^ 2 + a ^ 2) / 2)) : ℂ) *
    modifiedBesselI q ((a * t : ℝ) : ℂ)

/-- Nuttall Q as the improper integral of its defining kernel. -/
noncomputable def nuttallQ (p q : ℕ) (a b : ℝ) : ℂ :=
  ∫ t in Ioi b, nuttallQIntegrand p q a t

/-- Splitting the Nuttall Q tail at an intermediate point. This is the integral
identity used to rewrite the `Q(...,0)-Q(...,b)` entries in the largest-eigenvalue
formula as a finite-interval integral. -/
theorem nuttallQ_sub_eq_intervalIntegral
    (p q : ℕ) (a b₁ b₂ : ℝ) (hb : b₁ ≤ b₂)
    (hint : IntegrableOn (nuttallQIntegrand p q a) (Ioi b₁)) :
    nuttallQ p q a b₁ - nuttallQ p q a b₂ =
      ∫ t in b₁..b₂, nuttallQIntegrand p q a t := by
  have hint₂ : IntegrableOn (nuttallQIntegrand p q a) (Ioi b₂) :=
    hint.mono_set (Ioi_subset_Ioi hb)
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := nuttallQIntegrand p q a) hint hint₂
  simpa [nuttallQ] using (sub_eq_iff_eq_add.mpr hsplit.symm)

end JinWishart
