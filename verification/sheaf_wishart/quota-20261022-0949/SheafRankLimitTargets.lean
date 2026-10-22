import JinWishartFormalization.RegularizedSpectrumRankLimit
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafRankLimit
noncomputable section
def Bound : Prop := ∀ u r : ℝ,0≤u → 0≤r → ∀ k : ℕ,
 0≤(r*u/(1+r*u))^k ∧ (r*u/(1+r*u))^k≤1
def Pointwise : Prop := ∀ u : ℝ,0≤u → ∀ k : ℕ,0<k →
 Tendsto (fun r : ℝ=>(r*u/(1+r*u))^k) atTop (𝓝 (if 0<u then 1 else 0))
def Integral : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
 (f : α→ℝ),Measurable f → (∀ᵐ a ∂μ,0≤f a) → ∀ k : ℕ,0<k →
 Tendsto (fun r : ℝ=>∫ a,(r*f a/(1+r*f a))^k ∂μ) atTop
 (𝓝 (∫ a,(if 0<f a then (1:ℝ) else 0) ∂μ))
def Actual : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (k : ℕ),0<k → Tendsto (fun r : ℝ=>∑ i,∫ z,
 (r*JinWishart.actualCorrelatedEigenvalue B M i z/(1+r*JinWishart.actualCorrelatedEigenvalue B M i z))^k ∂stdGaussian _)
 atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ))
def First : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 Tendsto (fun r : ℝ=>r*deriv (fun x : ℝ=>∫ z,JinWishart.actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) r)
 atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ))
def Second : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 Tendsto (fun r : ℝ=> -(r^2)*(deriv^[2] (fun x : ℝ=>∫ z,JinWishart.actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)) r)
 atTop (𝓝 ((min m (Matrix.fromRows B M).rank : ℕ) : ℝ))
end
end SheafRankLimit
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.regularized_spectral_power_bound,`SheafRankLimit.Bound),
 (`JinWishart.regularized_spectral_power_tendsto,`SheafRankLimit.Pointwise),
 (`JinWishart.integral_regularized_spectral_power_tendsto,`SheafRankLimit.Integral),
 (`JinWishart.actualCorrelated_regularized_spectral_power_rank_limit,`SheafRankLimit.Actual),
 (`JinWishart.actualCorrelated_scaled_expected_logdet_deriv_rank_limit,`SheafRankLimit.First),
 (`JinWishart.actualCorrelated_scaled_expected_logdet_curvature_rank_limit,`SheafRankLimit.Second)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
