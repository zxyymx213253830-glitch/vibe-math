import JinWishartFormalization.ComplexGaussianPolynomialMoments
import Mathlib.Probability.ProductMeasure

/-!
# The exact polynomial functional on the actual complex matrix source

Codex proof bodies. Product law is derived from the existing real Gaussian
source, so independence is a conclusion, not a new premise.
[需人工审查] Finite coordinate transport, product measures and variance.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

def realPairToStandardComplex (x : Fin 2 → ℝ) : ℂ :=
  ((x 0 : ℂ) + x 1 * Complex.I) / (Real.sqrt 2 : ℂ)

theorem realPairToStandardComplex_law :
    (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map realPairToStandardComplex =
      standardComplexScalarLaw := by
  unfold standardComplexScalarLaw
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [realPairToStandardComplex,Function.comp_apply,Fin.sum_univ_two,
    Complex.coe_orthonormalBasisOneI,Complex.real_smul,Complex.ofReal_inv]
  simp
  ring

theorem realGaussian_complex_coordinates_law {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map
      (fun x i => realPairToStandardComplex (fun k => x (i,k))) =
        standardComplexPiLaw ι := by
  have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : Fin 2) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at h
  have hp := congrArg (fun μ => μ.map (fun x i => realPairToStandardComplex (x i))) h
  rw [Measure.map_map (by unfold realPairToStandardComplex; fun_prop) (by fun_prop),
    Measure.pi_map_pi (by intro i; unfold realPairToStandardComplex; fun_prop)] at hp
  simp_rw [realPairToStandardComplex_law] at hp
  exact hp

def complexMatrixEntries {m n : ℕ} (z : ComplexSample (m := m) (n := n)) :
    (Fin m × Fin n) → ℂ := fun ij => complexSampleMatrix z ij.1 ij.2

@[fun_prop]
theorem measurable_complexMatrixEntries (m n : ℕ) :
    Measurable (complexMatrixEntries (m := m) (n := n)) := by
  unfold complexMatrixEntries complexSampleMatrix
  fun_prop

theorem complexMatrixEntries_law (m n : ℕ) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map complexMatrixEntries =
      standardComplexPiLaw (Fin m × Fin n) := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (measurable_complexMatrixEntries m n) (by fun_prop)]
  have he : complexMatrixEntries ∘ WithLp.toLp 2 =
      fun x (ij : Fin m × Fin n) => realPairToStandardComplex (fun k => x (ij,k)) := by
    funext x ij
    simp only [complexMatrixEntries,complexSampleMatrix,Function.comp_apply,
      realPairToStandardComplex,PiLp.toLp_apply]
    ring
  rw [he]
  exact realGaussian_complex_coordinates_law

@[fun_prop]
theorem continuous_complexGaussianPolynomialEval {ι : Type*} [Fintype ι]
    (P : MvPolynomial (ι ⊕ ι) ℂ) : Continuous (complexGaussianPolynomialEval P) := by
  change Continuous (fun z => complexGaussianPolynomialEval P z)
  simp_rw [complexGaussianPolynomialEval_eq_sum]
  fun_prop

theorem integrable_actualComplexMatrix_polynomial (m n : ℕ)
    (P : MvPolynomial ((Fin m × Fin n) ⊕ (Fin m × Fin n)) ℂ) :
    Integrable (fun z => complexGaussianPolynomialEval P (complexMatrixEntries z))
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  have h := integrable_complexGaussian_polynomial P
  rw [← complexMatrixEntries_law m n] at h
  exact (integrable_map_measure
    (continuous_complexGaussianPolynomialEval P).aestronglyMeasurable
    (measurable_complexMatrixEntries m n).aemeasurable).mp h

theorem integral_actualComplexMatrix_polynomial (m n : ℕ)
    (P : MvPolynomial ((Fin m × Fin n) ⊕ (Fin m × Fin n)) ℂ) :
    (∫ z, complexGaussianPolynomialEval P (complexMatrixEntries z)
      ∂stdGaussian (ComplexSample (m := m) (n := n))) = complexGaussianPolynomialMoment P := by
  rw [← integral_complexGaussian_polynomial,← complexMatrixEntries_law m n,
    integral_map (measurable_complexMatrixEntries m n).aemeasurable
      (continuous_complexGaussianPolynomialEval P).aestronglyMeasurable]

end
end JinWishart
#print axioms JinWishart.realPairToStandardComplex_law
#print axioms JinWishart.realGaussian_complex_coordinates_law
#print axioms JinWishart.measurable_complexMatrixEntries
#print axioms JinWishart.complexMatrixEntries_law
#print axioms JinWishart.continuous_complexGaussianPolynomialEval
#print axioms JinWishart.integrable_actualComplexMatrix_polynomial
#print axioms JinWishart.integral_actualComplexMatrix_polynomial
