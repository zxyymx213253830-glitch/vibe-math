import JinWishartFormalization.PSDTraceNormGeometry
import Mathlib.Analysis.Normed.Operator.Basic
open scoped Matrix.Norms.Elementwise
#synth NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ)
#synth NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ)
#synth Norm ((Matrix (Fin 2) (Fin 2) ℂ) →L[ℝ] ℝ)
#check ContinuousLinearMap.hasOpNorm
#check ContinuousLinearMap.le_opNorm
