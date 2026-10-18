import JinWishartFormalization.GaussianMatrixBlockLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual Gaussian column selections, not only ordered first-column splits

Codex proof bodies; route discussion assisted by Qoder.
[需人工审查] Finite coordinate marginalization and actual Gaussian variance.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem pi_gaussianReal_map_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => fun i => x (e i)) =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  classical
  letI : Fintype (Set.range e) := Subtype.fintype (fun i => i ∈ Set.range e)
  let eR : κ ≃ Set.range e := Equiv.ofInjective e he
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun _ : ι => gaussianReal 0 1) (fun i => i ∈ Set.range e)
  have hp := (measurePreserving_fst
    (μ := Measure.pi (fun _ : Set.range e => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => gaussianReal 0 1))).comp hs
  have hr := measurePreserving_piCongrLeft (fun _ : Set.range e => gaussianReal 0 1) eR
  exact (hr.symm.comp hp).map_eq

theorem stdGaussian_map_injective_coordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun z => (WithLp.toLp 2 (fun i => z (e i)) : EuclideanSpace ℝ κ)) =
        stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (fun z : EuclideanSpace ℝ ι =>
      (WithLp.toLp 2 (fun i => z (e i)) : EuclideanSpace ℝ κ)) ∘ WithLp.toLp 2 =
      WithLp.toLp 2 ∘ (fun z : ι → ℝ => fun i => z (e i)) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    pi_gaussianReal_map_injective e he, map_pi_eq_stdGaussian]

def sampleColumnSelection {m n k : ℕ} (e : Fin k → Fin n)
    (z : ComplexSample (m := m) (n := n)) : ComplexSample (m := m) (n := k) :=
  WithLp.toLp 2 (fun ijl => z ((ijl.1.1, e ijl.1.2), ijl.2))

@[fun_prop]
theorem measurable_sampleColumnSelection {m n k : ℕ} (e : Fin k → Fin n) :
    Measurable (sampleColumnSelection (m := m) e) := by
  unfold sampleColumnSelection
  fun_prop

theorem stdGaussian_sampleColumnSelection_law {m n k : ℕ}
    (e : Fin k → Fin n) (he : Function.Injective e) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (sampleColumnSelection e) =
      stdGaussian (ComplexSample (m := m) (n := k)) := by
  apply stdGaussian_map_injective_coordinates
  rintro ⟨⟨i, j⟩, l⟩ ⟨⟨i', j'⟩, l'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨hi, hj⟩, hl⟩
  simp only [hi, he hj, hl]

theorem complexSampleMatrix_columnSelection {m n k : ℕ} (e : Fin k → Fin n)
    (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix (sampleColumnSelection e z) = (complexSampleMatrix z).submatrix id e := by
  ext i j
  rfl

theorem complexGram_columnSelection {m n k : ℕ} (e : Fin k → Fin n)
    (X : Matrix (Fin m) (Fin n) ℂ) :
    complexGram (X.submatrix id e) = (complexGram X).submatrix e e := by
  ext i j
  simp [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]

/-- Entire actual principal block distribution for any injective ordered columns. -/
theorem complexWishart_principalSubmatrix_law {m n k : ℕ}
    (e : Fin k → Fin n) (he : Function.Injective e) :
    (complexWishart (m := m) (n := n)).map (fun A => A.submatrix e e) =
      complexWishart (m := m) (n := k) := by
  have hf : (fun A : Matrix (Fin n) (Fin n) ℂ => A.submatrix e e) ∘ complexSampleGram =
      complexSampleGram ∘ sampleColumnSelection (m := m) e := by
    funext z
    change (complexGram (complexSampleMatrix z)).submatrix e e = _
    rw [← complexGram_columnSelection, ← complexSampleMatrix_columnSelection]
    rfl
  rw [complexWishart, Measure.map_map (by fun_prop) measurable_complexSampleGram,
    hf, ← Measure.map_map measurable_complexSampleGram (measurable_sampleColumnSelection e),
    stdGaussian_sampleColumnSelection_law e he]
  rfl

end
end JinWishart

#print axioms JinWishart.pi_gaussianReal_map_injective
#print axioms JinWishart.stdGaussian_map_injective_coordinates
#print axioms JinWishart.measurable_sampleColumnSelection
#print axioms JinWishart.stdGaussian_sampleColumnSelection_law
#print axioms JinWishart.complexSampleMatrix_columnSelection
#print axioms JinWishart.complexGram_columnSelection
#print axioms JinWishart.complexWishart_principalSubmatrix_law
