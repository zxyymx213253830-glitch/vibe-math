import JinWishartFormalization.CentralBartlettFiberVolume
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume-preserving general Hermitian real-coordinate block splitting

Codex proofs. One pivot, n complex upper-row coordinates, and n^2 real lower
coordinates exhaust (n+1)^2 real coordinates with no Frobenius factor.
[需人工审查] Coordinate ordering, product Lebesgue normalization and later use.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def realImagColumnIndexEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin n × Fin 2 where
  toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  invFun := fun p => if p.2 = 0 then .inl p.1 else .inr p.1
  left_inv := by intro p; cases p <;> simp
  right_inv := by rintro ⟨i, k⟩; fin_cases k <;> simp

def realImagToColumnEquiv (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ EuclideanSpace ℂ (Fin n) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin 2 => ℝ)
      (realImagColumnIndexEquiv n)).trans
      ((MeasurableEquiv.toLp 2 _).trans (complexColumnCoordinates n).toMeasurableEquiv))

theorem realImagToColumnEquiv_apply (n : ℕ) (p : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    realImagToColumnEquiv n p j = (p.1 j : ℂ) + (p.2 j : ℂ) * Complex.I := by
  rfl

theorem realImagToColumnEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (realImagToColumnEquiv n) := by
  exact ((complexColumnCoordinates n).measurePreserving.comp
    (PiLp.volume_preserving_toLp (Fin n × Fin 2))).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin 2 => ℝ)
        (realImagColumnIndexEquiv n)).comp
        (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin n => ℝ)))

def realMatrixBlockEquiv (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ᵐ
      (ℝ × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  (Matrix.ofMeasurableEquiv (Fin (n + 1)) (Fin (n + 1)) ℝ).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) 0).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        ((MeasurableEquiv.piCongrRight (fun _ : Fin n =>
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)).trans
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin n)))))

theorem realMatrixBlockEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (realMatrixBlockEquiv n) (hermitianRealCoordinateMeasure (n + 1)) volume := by
  have hbase : MeasurePreserving
      (Matrix.ofMeasurableEquiv (Fin (n + 1)) (Fin (n + 1)) ℝ).symm
      (hermitianRealCoordinateMeasure (n + 1)) volume := by
    refine ⟨(Matrix.ofMeasurableEquiv _ _ _).symm.measurable, ?_⟩
    exact Measure.map_id
  have hrow := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) 0
  have hfirst := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hlower := (volume_measurePreserving_arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin n)).comp
    (volume_preserving_pi (fun _ : Fin n => hfirst))
  exact ((hfirst.prod hlower).comp hrow).comp hbase

def hermitianBlockCoordinateEquiv (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ᵐ
      ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) :=
  (realMatrixBlockEquiv n).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodAssoc.symm).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.prodCongr (realImagToColumnEquiv n)
            (Matrix.ofMeasurableEquiv (Fin n) (Fin n) ℝ)))))

theorem hermitianBlockCoordinateEquiv_apply (n : ℕ)
    (q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hermitianBlockCoordinateEquiv n q =
      (q 0 0, (WithLp.toLp 2 (fun j : Fin n => (q 0 j.succ : ℂ) + (q j.succ 0 : ℂ) * Complex.I),
        Matrix.of (fun i j : Fin n => q i.succ j.succ))) := by
  rfl

theorem hermitianBlockCoordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (hermitianBlockCoordinateEquiv n)
      (hermitianRealCoordinateMeasure (n + 1))
      ((volume : Measure ℝ).prod ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (hermitianRealCoordinateMeasure n))) := by
  have hi : MeasurePreserving (MeasurableEquiv.refl ℝ) := ⟨measurable_id, Measure.map_id⟩
  have hmat : MeasurePreserving (Matrix.ofMeasurableEquiv (Fin n) (Fin n) ℝ)
      volume (hermitianRealCoordinateMeasure n) := by
    refine ⟨(Matrix.ofMeasurableEquiv _ _ _).measurable, ?_⟩
    exact Measure.map_id
  have hshuffle := (hi.prod
    (volume_preserving_prodAssoc (α₁ := Fin n → ℝ) (β₁ := Fin n → ℝ)
      (γ₁ := Fin n → Fin n → ℝ)).symm).comp
        (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin n → ℝ)
          (γ₁ := (Fin n → ℝ) × (Fin n → Fin n → ℝ)))
  exact ((hi.prod ((realImagToColumnEquiv_measurePreserving n).prod hmat)).comp hshuffle).comp
    (realMatrixBlockEquiv_measurePreserving n)

end
end JinWishart

#print axioms JinWishart.realImagToColumnEquiv_apply
#print axioms JinWishart.realImagToColumnEquiv_measurePreserving
#print axioms JinWishart.realMatrixBlockEquiv_measurePreserving
#print axioms JinWishart.hermitianBlockCoordinateEquiv_apply
#print axioms JinWishart.hermitianBlockCoordinateEquiv_measurePreserving
