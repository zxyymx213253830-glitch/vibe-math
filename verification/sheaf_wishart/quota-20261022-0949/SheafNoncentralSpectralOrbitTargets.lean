import JinWishartFormalization.ActualNoncentralSpectralOrbitLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
namespace SheafNoncentralSpectralOrbit
noncomputable section
def Charpoly : Prop := ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian),
 A.charpoly = B.charpoly → hA.eigenvalues₀ = hB.eigenvalues₀
def Invariant : Prop := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
 (hA : A.IsHermitian) (U : Matrix.unitaryGroup (Fin n) ℂ),
 (Matrix.isHermitian_conjTranspose_mul_mul (U : Matrix (Fin n) (Fin n) ℂ) hA).eigenvalues₀ =
 hA.eigenvalues₀
def Conjugate : Prop := ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian), hA.eigenvalues₀ = hB.eigenvalues₀ →
 ∃ U : Matrix.unitaryGroup (Fin n) ℂ, B = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * U
def Transport : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ)
 (U : Matrix.unitaryGroup (Fin n) ℂ),
 Nᴴ * N = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Mᴴ * M) *
  (U : Matrix (Fin n) (Fin n) ℂ) →
 (stdGaussian (ComplexSample (m := m) (n := n))).map
  (fun z => fun i => complexNoncentralSampleEigenvalue M i z) =
 (stdGaussian (ComplexSample (m := m) (n := n))).map
  (fun z => fun i => complexNoncentralSampleEigenvalue N i z)
def Parameters : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ),
 (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ =
 (Matrix.isHermitian_conjTranspose_mul_self N).eigenvalues₀ →
 (stdGaussian (ComplexSample (m := m) (n := n))).map
  (fun z => fun i => complexNoncentralSampleEigenvalue M i z) =
 (stdGaussian (ComplexSample (m := m) (n := n))).map
  (fun z => fun i => complexNoncentralSampleEigenvalue N i z)
end
end SheafNoncentralSpectralOrbit
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.hermitian_eigenvalues₀_eq_of_charpoly_eq,`SheafNoncentralSpectralOrbit.Charpoly),
 (`JinWishart.hermitian_eigenvalues₀_unitary_conjugation,`SheafNoncentralSpectralOrbit.Invariant),
 (`JinWishart.exists_unitary_conjugation_of_eigenvalues₀_eq,`SheafNoncentralSpectralOrbit.Conjugate),
 (`JinWishart.actualNoncentral_orderedSpectrum_law_of_meanGram_unitary,`SheafNoncentralSpectralOrbit.Transport),
 (`JinWishart.actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues,`SheafNoncentralSpectralOrbit.Parameters)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full ordered spectrum literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
