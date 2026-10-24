import JinWishartFormalization.GaussianFiniteSquareMGF
import JinWishartFormalization.EvenRadialProbability
import JinWishartFormalization.LocalMGFLawUniqueness
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Codex. Seed2026102402 controls before source.
[需人工审查] Same-law identification via local MGFs, raw/Euclidean coordinates.
No sphere-chart integration or unproved noncentral mixture-law assumption. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem gaussianPi_energy_eq_evenRadialLaw {ι : Type*} [Fintype ι]
    (q : ℕ) (hdim : Fintype.card ι=2*(q+1)) (u : ι → ℝ) (a : ℝ)
    (ha : a^2=∑ i,(u i)^2) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun x : ι → ℝ => (∑ i,(x i+u i)^2)/2) =
    (evenRadialMeasure q a).map (fun r : ℝ => r^2/2) := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let X := fun x : ι → ℝ => (∑ i,(x i+u i)^2)/2
  let Y := fun r : ℝ => r^2/2
  have hIX (t : ℝ) (ht : t<1) : Integrable (fun x => Real.exp (t*X x)) μ := by
    simpa only [X, μ, mul_div_assoc] using gaussianPi_integrable_exp_shifted_square_sum u t ht
  have hIY (t : ℝ) (ht : t<1) : Integrable (fun r => Real.exp (t*Y r)) (evenRadialMeasure q a) :=
    evenRadialMeasure_integrable_exp_energy q a t ht
  apply map_eq_of_mgf_eventuallyEq_zero (X := X) (Y := Y) (by fun_prop) (by fun_prop)
  · apply mem_interior_iff_mem_nhds.2
    change ∀ᶠ t in 𝓝 (0 : ℝ), Integrable (fun x => Real.exp (t*X x)) μ
    filter_upwards [isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio 1)] with t ht
    exact hIX t ht
  · apply mem_interior_iff_mem_nhds.2
    change ∀ᶠ t in 𝓝 (0 : ℝ), Integrable (fun r => Real.exp (t*Y r)) (evenRadialMeasure q a)
    filter_upwards [isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio 1)] with t ht
    exact hIY t ht
  · filter_upwards [isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio 1)] with t ht
    have hp : 0≤1-t := le_of_lt (sub_pos.mpr ht)
    change (∫ x : ι → ℝ, Real.exp (t*X x) ∂μ) = _
    have hG := gaussianPi_integral_exp_shifted_square_sum u t ht
    have hR := evenRadialMeasure_mgf q a t ht
    change mgf Y (evenRadialMeasure q a) t = _ at hR
    rw [hR]
    change (∫ x : ι → ℝ, Real.exp (t*((∑ i,(x i+u i)^2)/2)) ∂μ) = _
    simp only [← mul_div_assoc]
    rw [show μ=Measure.pi (fun _ : ι => gaussianReal 0 1) from rfl, hG, ← ha]
    simp [hdim, pow_mul, inv_pow, Real.sq_sqrt hp, div_eq_mul_inv, mul_comm]

theorem stdGaussian_energy_eq_evenRadialLaw {ι : Type*} [Fintype ι]
    (q : ℕ) (hdim : Fintype.card ι=2*(q+1)) (u : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => ‖z+u‖^2/2) =
      (evenRadialMeasure q ‖u‖).map (fun r : ℝ => r^2/2) := by
  have h := gaussianPi_energy_eq_evenRadialLaw q hdim (fun i => u i) ‖u‖
    (by simpa only [EuclideanSpace.real_norm_sq_eq])
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  convert h using 1
  congr 1
  funext x
  simp [Function.comp_def, EuclideanSpace.real_norm_sq_eq]

end
end JinWishart
#print axioms JinWishart.gaussianPi_energy_eq_evenRadialLaw
#print axioms JinWishart.stdGaussian_energy_eq_evenRadialLaw
