import JinWishartFormalization.FullRankPositiveCoordinateTransport
import JinWishartFormalization.CorrelatedFixedKernelCompression

/-! A rank-sized reconstructing common-kernel compression makes the pair
of compressed noise/mean maps jointly injective. No Gaussian or inverse
moment claim. Codex. [需人工审查] Later actual-model canonical transport. -/
open Matrix Module
namespace JinWishart
noncomputable section

theorem correlated_fixed_compression_joint_injective {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin r) ℂ)
    (hr : r=(Matrix.fromRows B M).rank)
    (hB : B*C*Cᴴ=B) (hM : M*C*Cᴴ=M) :
    Function.Injective ((B*C).toEuclideanLin.prod (M*C).toEuclideanLin) := by
  let A := Matrix.fromRows B M
  have hrec : A*C*Cᴴ=A := by
    dsimp [A]
    rw [Matrix.fromRows_mul,Matrix.fromRows_mul,hB,hM]
  have hlo : r≤(A*C).rank := calc
    r=A.rank := hr
    _=(A*C*Cᴴ).rank := congrArg Matrix.rank hrec.symm
    _≤(A*C).rank := Matrix.rank_mul_le_left _ _
  have hhi : (A*C).rank≤r := by simpa only [Fintype.card_fin] using (A*C).rank_le_card_width
  have hrc : (A*C).rank=r := le_antisymm hhi hlo
  have hdim : (A*C).rank=finrank ℂ (A*C).toEuclideanLin.range := by
    convert! (A*C).rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin p ⊕ Fin m) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin r) ℂ).toBasis using 1
  have hkdim : finrank ℂ (A*C).toEuclideanLin.ker=0 := by
    have hd := (A*C).toEuclideanLin.finrank_range_add_finrank_ker
    rw [← hdim,hrc] at hd
    simp only [finrank_euclideanSpace_fin] at hd
    omega
  have hinj : Function.Injective (A*C).toEuclideanLin :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hkdim)
  intro x y hxy
  apply hinj
  change (Matrix.fromRows B M*C).toEuclideanLin x=(Matrix.fromRows B M*C).toEuclideanLin y
  rw [Matrix.fromRows_mul]
  ext i
  rcases i with i | i
  · exact congrArg (fun z => z i) (congrArg Prod.fst hxy)
  · exact congrArg (fun z => z i) (congrArg Prod.snd hxy)

end
end JinWishart
#print axioms JinWishart.correlated_fixed_compression_joint_injective
