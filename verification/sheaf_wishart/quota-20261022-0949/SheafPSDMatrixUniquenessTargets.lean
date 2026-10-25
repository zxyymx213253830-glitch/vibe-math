import JinWishartFormalization.ActualNoncentralLaplaceCharacterization
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
open scoped ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] JinWishart.matrixRealDualNorm
namespace SheafPSDMatrixUniqueness
noncomputable section

def Entry : Prop := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}, A.PosSemidef →
 ∀ i j : Fin n, ‖A i j‖ ≤ A.trace.re

def Norm : Prop := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}, A.PosSemidef → ‖A‖ ≤ A.trace.re

def Dual : Prop := ∀ {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ),
 ∃ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian ∧
 (∀ W : Matrix (Fin n) (Fin n) ℂ, W.IsHermitian → L W = (H * W).trace.re) ∧ ‖H‖ ≤ 2 * ‖L‖

def Shift : Prop := ∀ {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}, H.IsHermitian →
 ∀ c : ℝ, (n : ℝ) * ‖H‖ ≤ c → ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H).PosSemidef

def Unique : Prop := ∀ {n : ℕ} {μ ν : Measure (Matrix (Fin n) (Fin n) ℂ)}
 [IsFiniteMeasure μ] [IsFiniteMeasure ν],
 (∀ᵐ W ∂μ, W.PosSemidef) → (∀ᵐ W ∂ν, W.PosSemidef) →
 (∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef →
  (∫ W, Real.exp (-(T * W).trace.re) ∂μ) = ∫ W, Real.exp (-(T * W).trace.re) ∂ν) → μ = ν

def Actual : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
 {ν : Measure (Matrix (Fin n) (Fin n) ℂ)} [IsFiniteMeasure ν],
 (∀ᵐ W ∂ν, W.PosSemidef) →
 (∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef →
  (∫ W, Real.exp (-(T * W).trace.re) ∂ν) =
  (‖(1 + T).det‖ ^ m)⁻¹ * Real.exp (-(M * T * (1 + T)⁻¹ * Mᴴ).trace.re)) →
 ν = complexNoncentralWishart M
end
end SheafPSDMatrixUniqueness
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.psd_entry_norm_le_trace_re,`SheafPSDMatrixUniqueness.Entry),
 (`JinWishart.psd_entrySupNorm_le_trace_re,`SheafPSDMatrixUniqueness.Norm),
 (`JinWishart.exists_hermitian_trace_dual_norm_le,`SheafPSDMatrixUniqueness.Dual),
 (`JinWishart.hermitian_scalar_shift_posSemidef,`SheafPSDMatrixUniqueness.Shift),
 (`JinWishart.finite_PSD_measures_eq_of_matrixLaplace,`SheafPSDMatrixUniqueness.Unique),
 (`JinWishart.noncentralWishart_eq_of_PSD_matrixLaplace,`SheafPSDMatrixUniqueness.Actual)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "PSD matrix uniqueness literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
