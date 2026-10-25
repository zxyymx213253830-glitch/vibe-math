import JinWishartFormalization.PSDTraceNormGeometry
import Mathlib.Analysis.Normed.Operator.Basic
open scoped Matrix.Norms.Elementwise
noncomputable example : Norm (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ) :=
 ContinuousLinearMap.hasOpNorm (E := Matrix (Fin 2) (Fin 2) ℂ) (F := ℝ) (𝕜 := ℝ) (𝕜₂ := ℝ)
#synth NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ)
#synth NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ)
