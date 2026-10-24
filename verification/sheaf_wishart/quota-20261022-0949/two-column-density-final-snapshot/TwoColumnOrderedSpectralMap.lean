import JinWishartFormalization.TwoByTwoOrderedEigenpair
import JinWishartFormalization.CentralWishartDeterminantBias

/-! Codex. Seed2026102414 precedes source. Deterministic two-column spectral map.
[需人工审查] Descending coordinates and raw properCN1 Gram conventions. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

def twoColumnMatrixEigenpair (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ × ℝ :=
  (((A 0 0).re+(A 1 1).re)/2+twoRowTracelessRadius A,
   ((A 0 0).re+(A 1 1).re)/2-twoRowTracelessRadius A)

def centralTwoColumnEigenpair {m : ℕ} (z : ComplexSample (m := m) (n := 2)) : ℝ × ℝ :=
  twoColumnMatrixEigenpair (complexSampleGram z)

theorem measurable_twoColumnMatrixEigenpair : Measurable twoColumnMatrixEigenpair := by
  unfold twoColumnMatrixEigenpair twoRowTracelessRadius
  fun_prop

theorem twoColumnMatrixEigenpair_det_product (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    ‖A.det‖=(twoColumnMatrixEigenpair A).1*(twoColumnMatrixEigenpair A).2 := by
  rw [complex_norm_eq_re_of_nonneg _ hA.det_nonneg,hermitian_twoRow_det_re A hA.1]
  have hr : (twoRowTracelessRadius A)^2=
      (((A 0 0).re-(A 1 1).re)/2)^2+(A 0 1).re^2+(A 0 1).im^2 := by
    simp [twoRowTracelessRadius,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,add_assoc]
  dsimp [twoColumnMatrixEigenpair]
  nlinarith [hr]

theorem centralTwoColumnEigenpair_eq_ordered {m : ℕ} (z : ComplexSample (m := m) (n := 2)) :
    centralTwoColumnEigenpair z=
      (complexNoncentralSampleEigenvalue (0 : Matrix (Fin m) (Fin 2) ℂ) 0 z,
       complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 2) ℂ) (by norm_num) z) := by
  have h := hermitian_twoRow_ordered_eigenpair (complexGram (complexSampleMatrix z))
    (complexGram_posSemidef (complexSampleMatrix z)).1
  have hi : smallestEigenvalue₀Index (n := 2) (by norm_num)=(1 : Fin (Fintype.card (Fin 2))) := by
    apply Fin.ext
    norm_num [smallestEigenvalue₀Index,Fin.last]
  apply Prod.ext
  · simpa [centralTwoColumnEigenpair,twoColumnMatrixEigenpair,complexSampleGram,
      complexNoncentralSampleEigenvalue] using h.1.symm
  · simpa [centralTwoColumnEigenpair,twoColumnMatrixEigenpair,complexSampleGram,
      complexNoncentralSampleSmallestEigenvalue,hi] using h.2.symm
end
end JinWishart
#print axioms JinWishart.measurable_twoColumnMatrixEigenpair
#print axioms JinWishart.twoColumnMatrixEigenpair_det_product
#print axioms JinWishart.centralTwoColumnEigenpair_eq_ordered
