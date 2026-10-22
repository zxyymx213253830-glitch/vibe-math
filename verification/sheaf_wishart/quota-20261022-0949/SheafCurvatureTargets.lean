import JinWishartFormalization.ExpectedLogDetStrictConcavity
import Lean
open Matrix Finset Function MeasureTheory ProbabilityTheory Set
namespace SheafCurvature
noncomputable section
def F {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
 ∫ z,JinWishart.actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _
def D {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
 ∑ i,∫ z,JinWishart.actualCorrelatedEigenvalue B M i z/(1+r*JinWishart.actualCorrelatedEigenvalue B M i z) ∂stdGaussian _
def K {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
 ∑ i,∫ z,(JinWishart.actualCorrelatedEigenvalue B M i z/(1+r*JinWishart.actualCorrelatedEigenvalue B M i z))^2 ∂stdGaussian _
def Bound : Prop := ∀ u r x : ℝ,0≤u → 0<r → r/2<x → (u/(1+x*u))^2≤(2/r)*u
def Generic : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α→ℝ),
 Measurable f → Integrable f μ → (∀ᵐ a ∂μ,0≤f a) → ∀ r : ℝ,0<r →
 Integrable (fun a=>(f a/(1+r*f a))^2) μ ∧
 HasDerivAt (fun x : ℝ=>∫ a,f a/(1+x*f a) ∂μ) (-(∫ a,(f a/(1+r*f a))^2 ∂μ)) r
def ActualD : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (r : ℝ),0<r → HasDerivAt (D B M) (-K B M r) r
def ActualFprime : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (r : ℝ),0<r → HasDerivAt (deriv (F B M)) (-K B M r) r
def ActualF2 : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (r : ℝ),0<r → (deriv^[2] (F B M)) r= -K B M r
def GramPos : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (r : ℝ),0<r → 0<X.rank →
 0<∑ i,((JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i/(1+r*(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i))^2
def GramZero : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ),X.rank=0 →
 ∀ i : Fin (Fintype.card (Fin n)),(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i=0
def KPos : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 0<min m (Matrix.fromRows B M).rank → ∀ r : ℝ,0<r → 0<K B M r
def Nonpos : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (r : ℝ),0<r → (deriv^[2] (F B M)) r≤0
def Concave : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 ConcaveOn ℝ (Ioi 0) (F B M)
def Strict : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 0<min m (Matrix.fromRows B M).rank → StrictConcaveOn ℝ (Ioi 0) (F B M)
def Zero : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 min m (Matrix.fromRows B M).rank=0 → ∀ r : ℝ,0≤r → F B M r=0
def Iff : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 StrictConcaveOn ℝ (Ioi 0) (F B M) ↔ 0<min m (Matrix.fromRows B M).rank
end
end SheafCurvature
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.nonnegative_resolvent_square_bound,`SheafCurvature.Bound),
 (`JinWishart.integral_resolvent_hasDerivAt,`SheafCurvature.Generic),
 (`JinWishart.actualCorrelated_expected_resolvent_hasDerivAt,`SheafCurvature.ActualD),
 (`JinWishart.actualCorrelated_expected_logdet_deriv_hasDerivAt,`SheafCurvature.ActualFprime),
 (`JinWishart.actualCorrelated_expected_logdet_second_deriv,`SheafCurvature.ActualF2),
 (`JinWishart.gram_resolvent_square_sum_pos,`SheafCurvature.GramPos),
 (`JinWishart.gram_eigenvalues_zero_of_rank_zero,`SheafCurvature.GramZero),
 (`JinWishart.actualCorrelated_expected_curvature_pos,`SheafCurvature.KPos),
 (`JinWishart.actualCorrelated_expected_logdet_second_deriv_nonpos,`SheafCurvature.Nonpos),
 (`JinWishart.actualCorrelated_expected_logdet_concave,`SheafCurvature.Concave),
 (`JinWishart.actualCorrelated_expected_logdet_strictConcave,`SheafCurvature.Strict),
 (`JinWishart.actualCorrelated_expected_logdet_zero_of_generic_rank_zero,`SheafCurvature.Zero),
 (`JinWishart.actualCorrelated_expected_logdet_strictConcave_iff,`SheafCurvature.Iff)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
