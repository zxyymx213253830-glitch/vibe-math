import JinWishartFormalization.FixedKernelCompression
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! One fixed rank-sized isometric compression for every noise matrix Z.
Deterministic Codex proof; no Gaussian distribution or inverse moment claim.
[需人工审查] Subsequent positive-spectrum/law correspondence. -/
open Matrix
namespace JinWishart
noncomputable section

theorem exists_correlated_fixed_kernel_compression {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
      r=(Matrix.fromRows B M).rank ∧ Cᴴ*C=1 ∧ B*C*Cᴴ=B ∧ M*C*Cᴴ=M ∧
      ∀ Z : Matrix (Fin m) (Fin p) ℂ,
        (Z*B+M)*C*Cᴴ=Z*B+M ∧
        ((Z*B+M)*C)*((Z*B+M)*C)ᴴ=(Z*B+M)*(Z*B+M)ᴴ := by
  obtain ⟨r,C,hr,hiso,hA⟩ := exists_matrix_fixed_kernel_compression (Matrix.fromRows B M)
  have hB : B*C*Cᴴ=B := by
    ext i j
    have h := congrFun (congrFun hA (Sum.inl i)) j
    simpa only [Matrix.fromRows_mul,Matrix.fromRows_apply_inl] using h
  have hM : M*C*Cᴴ=M := by
    ext i j
    have h := congrFun (congrFun hA (Sum.inr i)) j
    simpa only [Matrix.fromRows_mul,Matrix.fromRows_apply_inr] using h
  refine ⟨r,C,hr,hiso,hB,hM,?_⟩
  intro Z
  have hX : (Z*B+M)*C*Cᴴ=Z*B+M := by
    calc
      _ = (Z*B)*C*Cᴴ+M*C*Cᴴ := by rw [Matrix.add_mul,Matrix.add_mul]
      _ = Z*(B*C*Cᴴ)+M*C*Cᴴ := by simp only [Matrix.mul_assoc]
      _ = Z*B+M := by rw [hB,hM]
  refine ⟨hX,?_⟩
  calc
    _ = (Z*B+M)*C*Cᴴ*(Z*B+M)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (Z*B+M)*(Z*B+M)ᴴ := by rw [hX]

end
end JinWishart
#print axioms JinWishart.exists_correlated_fixed_kernel_compression
