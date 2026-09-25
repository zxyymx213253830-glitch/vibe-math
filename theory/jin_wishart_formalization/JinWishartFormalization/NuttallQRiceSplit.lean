import JinWishartFormalization.NoncentralScalarCDF

/-!
# Finite-interval Rice representation of a Nuttall-Q tail difference

This module identifies the `(p,q) = (1,0)` Nuttall-Q kernel with its real
factorial-series Rice kernel, then applies the existing tail-splitting lemma.
The improper-tail integrability hypothesis is explicit; discharging it for
every noncentrality is a separate analytic estimate.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

/-- Real order-zero Rice radial kernel, using the factorial series for `I₀`. -/
def riceRadialKernel (a t : ℝ) : ℝ :=
  t * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
    (∑' n : ℕ, ((a * t) ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2))

private theorem nuttallQ_10_integrand_eq_riceRadialKernel (a t : ℝ) :
    nuttallQIntegrand 1 0 a t = (riceRadialKernel a t : ℂ) := by
  simp only [nuttallQIntegrand, riceRadialKernel, pow_one]
  rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
  push_cast
  ring

/-- Splitting the `(1,0)` Nuttall-Q tail at `b` gives the finite Rice radial
integral from zero to `b`.  This is the interval identity underlying
`1 - Q₁,₀(a,b)` once the total-mass normalization `Q₁,₀(a,0)=1` is supplied.

The only analytic side condition is integrability of the defining tail kernel
on `(0,∞)`, which is exactly what the general Nuttall-Q splitting theorem
requires. -/
theorem nuttallQ_10_zero_sub_eq_riceIntegral
    (a b : ℝ) (hb : 0 ≤ b)
    (hint : IntegrableOn (nuttallQIntegrand 1 0 a) (Ioi 0)) :
    nuttallQ 1 0 a 0 - nuttallQ 1 0 a b =
      ((∫ t in (0 : ℝ)..b, riceRadialKernel a t : ℝ) : ℂ) := by
  rw [nuttallQ_sub_eq_intervalIntegral 1 0 a 0 b hb hint]
  rw [intervalIntegral.integral_of_le hb]
  calc
    ∫ t in Ioc (0 : ℝ) b, nuttallQIntegrand 1 0 a t =
        ∫ t in Ioc (0 : ℝ) b, (riceRadialKernel a t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      exact nuttallQ_10_integrand_eq_riceRadialKernel a t
    _ = ((∫ t in Ioc (0 : ℝ) b, riceRadialKernel a t : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = ((∫ t in (0 : ℝ)..b, riceRadialKernel a t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_of_le hb]

end

end JinWishart
