import JinWishartFormalization.ActualCompressedPositiveMinimum
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafPositiveTransport
noncomputable section
def Root : Prop := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x : ℝ),
 (x : ℂ) ∈ A.charpoly.roots ↔ ∃ i : Fin (Fintype.card (Fin n)),hA.eigenvalues₀ i=x
def Adjoint : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ),z≠0 →
 z ∈ (JinWishart.complexGram X).charpoly.roots ↔ z ∈ (JinWishart.complexGram Xᴴ).charpoly.roots
def Members : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
 (Y : Matrix (Fin m) (Fin q) ℂ),X*Xᴴ=Y*Yᴴ → ∀ x : ℝ,0<x →
 (∃ i : Fin (Fintype.card (Fin n)),(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i=x) ↔
 ∃ j : Fin (Fintype.card (Fin q)),(JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ j=x
def Minimum : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
 (Y : Matrix (Fin m) (Fin q) ℂ),X*Xᴴ=Y*Yᴴ →
 ∀ (i : Fin (Fintype.card (Fin n))) (j : Fin (Fintype.card (Fin q))),
 0<(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i →
 0<(JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ j →
 (∀ k,0<(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ k →
 (JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i≤(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ k) →
 (∀ k,0<(JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ k →
 (JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ j≤(JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ k) →
 (JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i=(JinWishart.complexGram_posSemidef Y).1.eigenvalues₀ j
def Actual : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ)
 (M : Matrix (Fin m) (Fin n) ℂ),0<min m (Matrix.fromRows B M).rank →
 ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
 r=(Matrix.fromRows B M).rank ∧ Cᴴ*C=1 ∧ B*C*Cᴴ=B ∧ M*C*Cᴴ=M ∧
 ∃ (i : Fin (Fintype.card (Fin n))) (j : Fin (Fintype.card (Fin r))),
 i.val+1=min m (Matrix.fromRows B M).rank ∧ j.val+1=min m (Matrix.fromRows B M).rank ∧
 Measurable (JinWishart.actualCorrelatedEigenvalue B M i) ∧
 Measurable (JinWishart.actualCorrelatedEigenvalue (B*C) (M*C) j) ∧
 ∀ᵐ z ∂stdGaussian (JinWishart.ComplexSample (m := m) (n := p)),
 0<JinWishart.actualCorrelatedEigenvalue B M i z ∧
 0<JinWishart.actualCorrelatedEigenvalue (B*C) (M*C) j z ∧
 JinWishart.actualCorrelatedEigenvalue B M i z=JinWishart.actualCorrelatedEigenvalue (B*C) (M*C) j z
end
end SheafPositiveTransport
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.hermitian_real_root_iff_ordered_eigenvalue,`SheafPositiveTransport.Root),
 (`JinWishart.gram_nonzero_root_mem_iff_conjTranspose,`SheafPositiveTransport.Adjoint),
 (`JinWishart.gram_positive_eigenvalue_mem_iff_of_rowGram_eq,`SheafPositiveTransport.Members),
 (`JinWishart.gram_min_positive_eq_of_rowGram_eq,`SheafPositiveTransport.Minimum),
 (`JinWishart.exists_actual_fixed_compression_min_positive_ae,`SheafPositiveTransport.Actual)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
