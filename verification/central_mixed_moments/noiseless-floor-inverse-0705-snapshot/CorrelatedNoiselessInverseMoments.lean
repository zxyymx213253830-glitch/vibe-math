import JinWishartFormalization.CorrelatedNoiselessSpectralFloor
import JinWishartFormalization.CorrelatedColumnMinimum

/-! All nonnegative real inverse orders for the ROW minimum in the noiseless-floor regime.
Codex. This is NOT the inverse minimum criterion for every singular factor.
[需人工审查] Measurability/integral domination and row/column model correspondence.
-/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem measurable_actualCorrelatedRowMinimum {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m) :
    Measurable (fun z : ComplexSample (m := m) (n := p) =>
      gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm) := by
  apply (measurable_gramSmallestValue hm).comp
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.conjTranspose_apply,Matrix.add_apply,Matrix.mul_apply,complexSampleMatrix]
  fun_prop

theorem actualCorrelatedRow_inverseMoment_integrable_of_noiseless_surjective {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m)
    (pwr : ℝ) (hpwr : 0≤pwr) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      (gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm)⁻¹^pwr) (stdGaussian _) := by
  obtain ⟨δ,hδ,hδf⟩ := correlated_rowGram_uniform_floor B M hm hs
  have hf := measurable_actualCorrelatedRowMinimum B M hm
  apply (integrable_const (δ⁻¹^pwr)).mono' (hf.inv.pow_const pwr).aestronglyMeasurable
  apply ae_of_all
  intro z
  have hz := hδf (complexSampleMatrix z)
  have hpos : 0<gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm := hδ.trans_le hz
  have hinv : (gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm)⁻¹≤δ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hδ hz
  change |(gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm)⁻¹^pwr|≤δ⁻¹^pwr
  rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hpos.le) pwr)]
  exact Real.rpow_le_rpow (inv_nonneg.mpr hpos.le) hinv hpwr

end
end JinWishart
#print axioms JinWishart.measurable_actualCorrelatedRowMinimum
#print axioms JinWishart.actualCorrelatedRow_inverseMoment_integrable_of_noiseless_surjective
