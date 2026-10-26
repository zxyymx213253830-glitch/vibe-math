import JinWishartFormalization.PaperNoncentralSpectralOrbitLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory Polynomial JinWishart
namespace SheafPaperSpectralOrbit
noncomputable section
def Padding : Prop := ∀ {a b d : ℕ} {A : Matrix (Fin a) (Fin a) ℂ}
 {B : Matrix (Fin b) (Fin b) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian),
 (∀ i, 0 ≤ hA.eigenvalues₀ i) → B.charpoly = X^d * A.charpoly →
 List.ofFn hB.eigenvalues₀ = List.ofFn hA.eigenvalues₀ ++ List.replicate d 0
def GramList : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ), m ≤ n →
 List.ofFn (complexGram_posSemidef A).1.eigenvalues₀ =
 List.ofFn (complexGram_posSemidef Aᴴ).1.eigenvalues₀ ++ List.replicate (n-m) 0
def GramPrefix : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
 (hmn : m ≤ n) (i : Fin m),
 (complexGram_posSemidef Aᴴ).1.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i) =
 (complexGram_posSemidef A).1.eigenvalues₀
  (Fin.cast (Fintype.card_fin n).symm (Fin.castLE hmn i))
def PaperList : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ),
 List.ofFn (complexGram_posSemidef A).1.eigenvalues₀ =
 List.ofFn (paperSmallSideGram_posSemidef A).1.eigenvalues₀ ++ List.replicate (n-min m n) 0
def PaperPrefix : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin (min m n)),
 (paperSmallSideGram_posSemidef A).1.eigenvalues₀
  (Fin.cast (Fintype.card_fin (min m n)).symm i) =
 (complexGram_posSemidef A).1.eigenvalues₀
  (Fin.cast (Fintype.card_fin n).symm (Fin.castLE (Nat.min_le_right m n) i))
def FromColumn : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ),
 (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ =
 (Matrix.isHermitian_conjTranspose_mul_self N).eigenvalues₀ →
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N)
def FromSmall : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ),
 (paperSmallSideGram_posSemidef M).1.eigenvalues₀ =
 (paperSmallSideGram_posSemidef N).1.eigenvalues₀ →
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N)
end
end SheafPaperSpectralOrbit
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.hermitian_ordered_zero_padding,`SheafPaperSpectralOrbit.Padding),
 (`JinWishart.gram_ordered_column_eq_row_append_zeros,`SheafPaperSpectralOrbit.GramList),
 (`JinWishart.gram_ordered_row_column_prefix,`SheafPaperSpectralOrbit.GramPrefix),
 (`JinWishart.paperSmallSide_ordered_column_zero_padding,`SheafPaperSpectralOrbit.PaperList),
 (`JinWishart.paperSmallSide_ordered_column_prefix,`SheafPaperSpectralOrbit.PaperPrefix),
 (`JinWishart.actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues,`SheafPaperSpectralOrbit.FromColumn),
 (`JinWishart.actualNoncentral_paperJointSpectrum_law_of_smallMeanGram_eigenvalues,`SheafPaperSpectralOrbit.FromSmall)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Paper spectral orbit literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
