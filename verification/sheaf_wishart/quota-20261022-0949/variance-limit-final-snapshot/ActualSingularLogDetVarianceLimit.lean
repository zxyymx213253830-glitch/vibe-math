import JinWishartFormalization.ActualSingularOffsetL2
import JinWishartFormalization.MeanSquareSecondMomentContinuity
import Mathlib.Probability.Moments.Variance

/-! Actual full-logdet variance converges to the finite positive-spectrum log variance.
Fixed arbitrary B,M, including singular/zero factors and all finite shapes.
Codex. [需人工审查] L2/moment transport, centering and physical model. -/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_offset_second_moment {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p)=>∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)
    (∀ r : ℝ,1≤r → MemLp (fun z=>actualCorrelatedMatrixLogDet B M r z-R*Real.log r) 2 (stdGaussian _)) ∧
    Tendsto (fun r : ℝ=>∫ z,(actualCorrelatedMatrixLogDet B M r z-R*Real.log r)^2 ∂stdGaussian _)
      atTop (𝓝 (∫ z,(S z)^2 ∂stdGaussian _)) := by
  classical
  intro R S
  have hS := integrable_actualCorrelated_positive_log_sum B M
  have hQ := integrable_actualCorrelated_positive_log_sum_sq B M
  change Integrable S (stdGaussian _) at hS
  change Integrable (fun z=>(S z)^2) (stdGaussian _) at hQ
  have hSM : MemLp S 2 (stdGaussian _) := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).2 hQ
  have hL := actualCorrelatedMatrixLogDet_offset_mean_square B M
  have hU (r : ℝ) (hr : 1≤r) : MemLp
      (fun z=>actualCorrelatedMatrixLogDet B M r z-R*Real.log r) 2 (stdGaussian _) := by
    have hC := (integrable_actualCorrelatedMatrixLogDet B M r (zero_le_one.trans hr)).sub (integrable_const (R*Real.log r))
    have hE : MemLp (fun z=>actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z) 2 (stdGaussian _) :=
      (memLp_two_iff_integrable_sq (hC.sub hS).aestronglyMeasurable).2 (hL.1 r hr)
    convert hE.add hSM using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  exact ⟨hU,integral_square_tendsto_of_mean_square (stdGaussian _)
    (fun r z=>actualCorrelatedMatrixLogDet B M r z-R*Real.log r) S hU hSM hL.2⟩

theorem actualCorrelatedMatrixLogDet_variance_tendsto {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    let S := fun z : ComplexSample (m := m) (n := p)=>∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)
    (∀ r : ℝ,1≤r → MemLp (actualCorrelatedMatrixLogDet B M r) 2 (stdGaussian _)) ∧
    Tendsto (fun r : ℝ=>ProbabilityTheory.variance (actualCorrelatedMatrixLogDet B M r) (stdGaussian _))
      atTop (𝓝 (ProbabilityTheory.variance S (stdGaussian _))) := by
  classical
  intro S
  let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
  let U := fun r z=>actualCorrelatedMatrixLogDet B M r z-R*Real.log r
  have hU := actualCorrelatedMatrixLogDet_offset_second_moment B M
  have hS := integrable_actualCorrelated_positive_log_sum B M
  have hQ := integrable_actualCorrelated_positive_log_sum_sq B M
  change Integrable S (stdGaussian _) at hS
  change Integrable (fun z=>(S z)^2) (stdGaussian _) at hQ
  have hSM : MemLp S 2 (stdGaussian _) := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).2 hQ
  have hC (r : ℝ) (hr : 1≤r) : MemLp (actualCorrelatedMatrixLogDet B M r) 2 (stdGaussian _) := by
    have h := (hU.1 r hr).add (memLp_const (R*Real.log r))
    convert h using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  refine ⟨hC,?_⟩
  have hmean : Tendsto (fun r : ℝ=>∫ z,U r z ∂stdGaussian _) atTop (𝓝 (∫ z,S z ∂stdGaussian _)) := by
    apply (actualCorrelatedMatrixLogDet_offset_generic_rank B M).congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    dsimp only [U]
    rw [integral_sub (integrable_actualCorrelatedMatrixLogDet B M r (zero_le_one.trans hr)) (integrable_const _)]
    simp [R]
  have ht := hU.2.sub (hmean.pow 2)
  have hVS : ProbabilityTheory.variance S (stdGaussian _) =
      (∫ z,(S z)^2 ∂stdGaussian _)-(∫ z,S z ∂stdGaussian _)^2 := by
    simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hSM
  rw [← hVS] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have hVU : ProbabilityTheory.variance (U r) (stdGaussian _) =
      (∫ z,(U r z)^2 ∂stdGaussian _)-(∫ z,U r z ∂stdGaussian _)^2 := by
    simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub (hU.1 r hr)
  calc
    _ = ProbabilityTheory.variance (U r) (stdGaussian _) := hVU.symm
    _ = _ := ProbabilityTheory.variance_sub_const
      (integrable_actualCorrelatedMatrixLogDet B M r (zero_le_one.trans hr)).aestronglyMeasurable (R*Real.log r)

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_second_moment
#print axioms JinWishart.actualCorrelatedMatrixLogDet_variance_tendsto
