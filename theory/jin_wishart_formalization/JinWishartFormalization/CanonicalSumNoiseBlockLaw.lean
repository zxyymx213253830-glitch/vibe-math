import JinWishartFormalization.JointKernelCanonicalMatrix

/-! The actual isometric-noise block law in the Sum row coordinates produced
by the fixed canonical normal form. Reuses the full Fin-indexed law; fixed
frames and means only. Codex. [需人工审查] Exact coordinate/model transport. -/
open Matrix MeasureTheory ProbabilityTheory Module
namespace JinWishart
noncomputable section

theorem actual_sum_isometric_noise_block_law {m p b a c : ℕ}
    (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ) :
    (stdGaussian (ComplexSample (m := m) (n := p))).map (fun z =>
      ((fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inl i)+A i j),
       (fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inr i)+H i j)))=
      (complexGaussianMatrixLaw A).prod (complexGaussianMatrixLaw H) := by
  have hac : a+c=m := by
    have hd := V.toLinearEquiv.finrank_eq
    simpa using hd.symm
  let R : (Fin a ⊕ Fin c) ≃ Fin m := finSumFinEquiv.trans (finCongr hac)
  let W := V.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ R)
  let e : Fin a → Fin m := fun i => R (Sum.inl i)
  let f : Fin c → Fin m := fun i => R (Sum.inr i)
  let M : Matrix (Fin m) (Fin b) ℂ := fun i j =>
    Sum.elim (fun k => A k j) (fun k => H k j) (R.symm i)
  have hcoord (x : EuclideanSpace ℂ (Fin m)) (i : Fin a ⊕ Fin c) :
      W x (R i)=V x i := by
    change V x (R.symm (R i))=V x i
    rw [R.symm_apply_apply]
  have hsel : Function.Injective (Sum.elim e f) := by
    have heq : Sum.elim e f=(fun i => R i) := by
      funext i
      cases i <;> rfl
    rw [heq]
    exact R.injective
  have hMe : M.submatrix e id=A := by
    ext i j
    change Sum.elim (fun k => A k j) (fun k => H k j) (R.symm (R (Sum.inl i)))=A i j
    rw [R.symm_apply_apply]
    rfl
  have hMf : M.submatrix f id=H := by
    ext i j
    change Sum.elim (fun k => A k j) (fun k => H k j) (R.symm (R (Sum.inr i)))=H i j
    rw [R.symm_apply_apply]
    rfl
  have hs := actual_isometric_noise_disjoint_row_blocks U hU W M e f hsel
  rw [hMe,hMf] at hs
  have heq : (fun z : ComplexSample (m := m) (n := p) =>
      ((unitaryActColumns W (complexSampleMatrix z*U)+M).submatrix e id,
        (unitaryActColumns W (complexSampleMatrix z*U)+M).submatrix f id))=
      (fun z =>
        ((fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inl i)+A i j),
         (fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inr i)+H i j))) := by
    funext z
    apply Prod.ext
    · ext i j
      change W (complexMatrixColumn (complexSampleMatrix z*U) j) (R (Sum.inl i))+M (e i) j=_
      rw [hcoord]
      exact congrArg (fun t => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inl i)+t)
        (congrFun (congrFun hMe i) j)
    · ext i j
      change W (complexMatrixColumn (complexSampleMatrix z*U) j) (R (Sum.inr i))+M (f i) j=_
      rw [hcoord]
      exact congrArg (fun t => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inr i)+t)
        (congrFun (congrFun hMf i) j)
  rw [heq] at hs
  exact hs

end
end JinWishart
#print axioms JinWishart.actual_sum_isometric_noise_block_law
