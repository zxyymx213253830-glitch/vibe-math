import JinWishartFormalization.ActualComplexPolynomialLogSquare
import JinWishartFormalization.ActualSingularPositiveLog

/-! All-shape fixed-factor positive-spectrum logarithms have finite second moments.
positiveSpectrumLog is log(lambda) onlambda>0, and0 onzero modes; NOT log positive-part.
Codex. [需人工审查] AE minor/rank witness, L2 domination and physical model. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
namespace JinWishart
noncomputable section

theorem integrable_actualCorrelated_positive_log_sum_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z=>(∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))^2)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  classical
  let r := min m (Matrix.fromRows B M).rank
  obtain ⟨f,g,hf,hg,_hlog,hne⟩ := exists_actual_fixed_rank_minor_log_witness B M
  let L : Matrix (Fin r) (Fin m) ℂ := (1 : Matrix (Fin m) (Fin m) ℂ).submatrix f (Equiv.refl _)
  let H : Matrix (Fin n) (Fin r) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Equiv.refl _) g
  have he (X : Matrix (Fin m) (Fin n) ℂ) : L*X*H=X.submatrix f g :=
    coordinate_submatrix_as_compression X f g
  have hL := integrable_actualAffineCompressedDet_log_sq B M L H
  simp_rw [he] at hL
  let S := fun z : ComplexSample (m := m) (n := p)=>∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)
  let T := fun z : ComplexSample (m := m) (n := p)=>∑ i,actualCorrelatedEigenvalue B M i z
  let A := fun z : ComplexSample (m := m) (n := p)=>Real.log ‖((complexSampleMatrix z*B+M).submatrix f g).det‖
  let C : ℝ := |Real.log (r.factorial : ℝ)|
  have hT : Integrable (fun z=>(T z)^2) (stdGaussian _) := by
    apply (integrable_actualCorrelatedGram_trace_sq B M).congr
    exact ae_of_all _ (fun z=>by dsimp only [T]; rw [sum_actualCorrelatedEigenvalues_eq_trace])
  have hdom : Integrable (fun z=>3*(T z)^2+3*C^2+12*(A z)^2) (stdGaussian _) :=
    ((hT.const_mul 3).add (integrable_const _)).add (hL.const_mul 12)
  have hm : Measurable S := by
    apply Finset.measurable_sum
    intro i hi
    unfold positiveSpectrumLog
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i))
      (measurable_actualCorrelatedEigenvalue B M i).log measurable_const
  apply hdom.mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [hne,actualCorrelatedRank_eq_generic_ae B M] with z hz hr
  have hr' : (complexSampleMatrix z*B+M).rank=r := by
    dsimp only [r]
    rw [matrix_fromRows_rank_eq]
    exact hr
  have hb := abs_positive_log_sum_le_minor_log (complexSampleMatrix z*B+M) f g hg hr' hz
  change |S z|≤T z+C+2*|A z| at hb
  have hp := pow_le_pow_left₀ (abs_nonneg (S z)) hb 2
  rw [sq_abs] at hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change (S z)^2≤3*(T z)^2+3*C^2+12*(A z)^2
  nlinarith only [hp,sq_abs (A z),sq_nonneg (T z-C),sq_nonneg (T z-2*|A z|),sq_nonneg (C-2*|A z|)]

theorem integrable_actualCorrelated_positive_log_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    Integrable (fun z=>(positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))^2)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  classical
  let S := fun z : ComplexSample (m := m) (n := p)=>∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
  let T := fun z : ComplexSample (m := m) (n := p)=>∑ j,actualCorrelatedEigenvalue B M j z
  have hT : Integrable (fun z=>(T z)^2) (stdGaussian _) := by
    apply (integrable_actualCorrelatedGram_trace_sq B M).congr
    exact ae_of_all _ (fun z=>by dsimp only [T]; rw [sum_actualCorrelatedEigenvalues_eq_trace])
  have hS := integrable_actualCorrelated_positive_log_sum_sq B M
  have hm : Measurable (fun z : ComplexSample (m := m) (n := p)=>positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)) :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i))
      (measurable_actualCorrelatedEigenvalue B M i).log measurable_const
  apply ((hT.const_mul 2).add (hS.const_mul 2)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  have hb := abs_positiveSpectrumLog_le_trace_add_abs_sum (fun j=>actualCorrelatedEigenvalue B M j z)
    (fun j=>actualCorrelatedEigenvalue_nonneg B M j z) i
  change |positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)|≤T z+|S z| at hb
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change (positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))^2≤2*(T z)^2+2*(S z)^2
  nlinarith only [hp,sq_abs (S z),sq_nonneg (T z-|S z|)]

theorem actualCorrelated_positive_log_sum_centered_second_moment {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    let S := fun z : ComplexSample (m := m) (n := p)=>∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)
    Integrable (fun z=>(S z-(∫ w,S w ∂stdGaussian _))^2) (stdGaussian _) ∧
      (∫ z,(S z-(∫ w,S w ∂stdGaussian _))^2 ∂stdGaussian _) =
        (∫ z,(S z)^2 ∂stdGaussian _)-(∫ z,S z ∂stdGaussian _)^2 := by
  classical
  intro S
  let a := ∫ z,S z ∂stdGaussian _
  have hS := integrable_actualCorrelated_positive_log_sum B M
  have hQ := integrable_actualCorrelated_positive_log_sum_sq B M
  change Integrable S (stdGaussian _) at hS
  change Integrable (fun z=>(S z)^2) (stdGaussian _) at hQ
  have hlin : Integrable (fun z=>2*a*S z) (stdGaussian _) := hS.const_mul (2*a)
  have hsub : Integrable (fun z=>(S z)^2-2*a*S z) (stdGaussian _) := hQ.sub hlin
  have hdom := (hQ.sub (hS.const_mul (2*a))).add (integrable_const (a^2))
  have hi : Integrable (fun z=>(S z-a)^2) (stdGaussian _) := by
    apply hdom.congr
    exact ae_of_all _ (fun z=>by dsimp only [Pi.add_apply,Pi.sub_apply]; ring)
  refine ⟨hi,?_⟩
  have he : (fun z=>(S z-a)^2)=(fun z=>(S z)^2-2*a*S z+a^2) := by funext z; ring
  change (∫ z,(S z-a)^2 ∂stdGaussian _)=(∫ z,(S z)^2 ∂stdGaussian _)-a^2
  rw [he,integral_add hsub (integrable_const _),integral_sub hQ hlin,integral_const_mul]
  simp only [integral_const]
  simp
  change (∫ z,(S z)^2 ∂stdGaussian _)-2*a*a+a^2=(∫ z,(S z)^2 ∂stdGaussian _)-a^2
  ring

end
end JinWishart
#print axioms JinWishart.integrable_actualCorrelated_positive_log_sum_sq
#print axioms JinWishart.integrable_actualCorrelated_positive_log_sq
#print axioms JinWishart.actualCorrelated_positive_log_sum_centered_second_moment
