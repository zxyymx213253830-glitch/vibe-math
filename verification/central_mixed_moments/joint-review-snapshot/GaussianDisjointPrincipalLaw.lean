import JinWishartFormalization.CentralWishartDeterminantBias

/-!
# Actual joint law of disjoint principal Gram blocks

Codex proof bodies. Source coordinates, not an assumed Wishart independence rule.
[需人工审查] Finite Gaussian product transport and actual marginal interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def disjointSampleIndex {k l n : ℕ} (m : ℕ) (e : Fin k → Fin n) (f : Fin l → Fin n) :
    (((Fin m × Fin k) × Fin 2) ⊕ ((Fin m × Fin l) × Fin 2)) → ((Fin m × Fin n) × Fin 2) :=
  Sum.elim (fun a => ((a.1.1,e a.1.2),a.2)) (fun a => ((a.1.1,f a.1.2),a.2))

theorem disjointSampleIndex_injective {k l n : ℕ} (m : ℕ)
    (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) : Function.Injective (disjointSampleIndex m e f) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · have hc : (Sum.inl a.1.2 : Fin k ⊕ Fin l) = Sum.inl b.1.2 :=
      h (congrArg (fun x => x.1.2) hab)
    exact congrArg Sum.inl (Prod.ext
      (Prod.ext (congrArg (fun x => x.1.1) hab) (Sum.inl.inj hc)) (congrArg (fun x : (Fin m × Fin n) × Fin 2 => x.2) hab))
  · have hc : (Sum.inl a.1.2 : Fin k ⊕ Fin l) = Sum.inr b.1.2 :=
      h (congrArg (fun x => x.1.2) hab)
    cases hc
  · have hc : (Sum.inr a.1.2 : Fin k ⊕ Fin l) = Sum.inl b.1.2 :=
      h (congrArg (fun x => x.1.2) hab)
    cases hc
  · have hc : (Sum.inr a.1.2 : Fin k ⊕ Fin l) = Sum.inr b.1.2 :=
      h (congrArg (fun x => x.1.2) hab)
    exact congrArg Sum.inr (Prod.ext
      (Prod.ext (congrArg (fun x => x.1.1) hab) (Sum.inr.inj hc)) (congrArg (fun x : (Fin m × Fin n) × Fin 2 => x.2) hab))

theorem stdGaussian_disjoint_columnSelections {m n k l : ℕ}
    (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map
      (fun z => (sampleColumnSelection e z, sampleColumnSelection f z)) =
      (stdGaussian (ComplexSample (m := m) (n := k))).prod
        (stdGaussian (ComplexSample (m := m) (n := l))) := by
  have hi := stdGaussian_map_injective_coordinates (disjointSampleIndex m e f)
    (disjointSampleIndex_injective m e f h)
  have hs := congrArg (fun μ => μ.map
    (euclideanGaussianSplit (ι := (Fin m × Fin k) × Fin 2)
      (κ := (Fin m × Fin l) × Fin 2))) hi
  rw [stdGaussian_sum_split, Measure.map_map measurable_euclideanGaussianSplit (by fun_prop)] at hs
  exact hs

/-- The two principal blocks are independent ACTUAL Wishart laws, with the SAME row count. -/
theorem complexWishart_disjoint_principal_law {m n k l : ℕ}
    (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) :
    (complexWishart (m := m) (n := n)).map
      (fun A => (A.submatrix e e, A.submatrix f f)) =
      (complexWishart (m := m) (n := k)).prod (complexWishart (m := m) (n := l)) := by
  have hs := congrArg (fun μ => μ.map (Prod.map
    (complexSampleGram (m := m) (n := k)) (complexSampleGram (m := m) (n := l))))
      (stdGaussian_disjoint_columnSelections (m := m) e f h)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_complexSampleGram measurable_complexSampleGram] at hs
  have heq : (Prod.map (complexSampleGram (m := m) (n := k))
      (complexSampleGram (m := m) (n := l))) ∘
      (fun z : ComplexSample (m := m) (n := n) =>
        (sampleColumnSelection e z, sampleColumnSelection f z)) =
      (fun A => (A.submatrix e e, A.submatrix f f)) ∘ complexSampleGram := by
    funext z
    simp only [Function.comp_apply, Prod.map_apply]
    change (complexGram (complexSampleMatrix (sampleColumnSelection e z)),
      complexGram (complexSampleMatrix (sampleColumnSelection f z))) = _
    rw [complexSampleMatrix_columnSelection, complexSampleMatrix_columnSelection,
      complexGram_columnSelection, complexGram_columnSelection]
    rfl
  rw [heq, ← Measure.map_map (by fun_prop) measurable_complexSampleGram] at hs
  exact hs

theorem complexWishart_disjoint_determinant_moment (t n k l p q : ℕ)
    (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) (hk : k ≤ t) (hl : l ≤ t) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix e e).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix f f).det‖^q)
      ∂complexWishart (m := t) (n := n)) =
      ENNReal.ofReal (centralDeterminantPowerMoment (t-k) k p) *
        ENNReal.ofReal (centralDeterminantPowerMoment (t-l) l q) := by
  have he := congrArg (fun μ => ∫⁻ a : Matrix (Fin k) (Fin k) ℂ × Matrix (Fin l) (Fin l) ℂ,
    ENNReal.ofReal (‖a.1.det‖^p) * ENNReal.ofReal (‖a.2.det‖^q) ∂μ)
      (complexWishart_disjoint_principal_law (m := t) e f h)
  rw [lintegral_map (by fun_prop) (by fun_prop),
    lintegral_prod_mul
      (f := fun A : Matrix (Fin k) (Fin k) ℂ => ENNReal.ofReal (‖A.det‖^p))
      (g := fun B : Matrix (Fin l) (Fin l) ℂ => ENNReal.ofReal (‖B.det‖^q))
      (by fun_prop) (by fun_prop)] at he
  have h0 := complexWishart_principalSubmatrix_norm_moment t k k p id Function.injective_id hk
  have h1 := complexWishart_principalSubmatrix_norm_moment t l l q id Function.injective_id hl
  simp only [Matrix.submatrix_id_id] at h0 h1
  simpa only [Function.comp_apply, h0, h1] using he

end
end JinWishart
#print axioms JinWishart.disjointSampleIndex_injective
#print axioms JinWishart.stdGaussian_disjoint_columnSelections
#print axioms JinWishart.complexWishart_disjoint_principal_law
#print axioms JinWishart.complexWishart_disjoint_determinant_moment
