import JinWishartFormalization.Theorem2SingleColumnAnyRows
import JinWishartFormalization.Theorem1SingleColumnTwoRows
import JinWishartFormalization.NuttallQ21Positive

/-!
# Two-row, one-column noncentral formula candidates without denominator hypotheses

For positive noncentrality, strict positivity of the defining `Q_{2,1}`
integral discharges the explicit denominator side condition in the one-column
specializations of Theorems 1 and 2.  These are formula-side results; they do
not assert that the candidates equal Wishart probabilities.
-/

namespace JinWishart

/-- In the `(s,t,L)=(1,2,1)` Theorem 1 specialization, positive `lambda`
ensures the normalizing `Q_{2,1}` denominator is nonzero. -/
theorem theorem1TwoRowsCandidate_eq_normalizedNuttallQ_of_pos
    (lambda x : ℝ) (hlambda : 0 < lambda) :
    theorem1CdfCandidate 1 2 1 (by omega) (by omega)
      (fun _ : Fin 1 => lambda) x =
      1 - ‖theorem1TwoRowScalarQ lambda x‖ /
        ‖nuttallQ 2 1 (Real.sqrt (2 * lambda)) 0‖ := by
  apply theorem1ScalarTwoRowsCandidate_eq_normalizedNuttallQ
  apply nuttallQ21_zeroThreshold_ne_zero
  exact Real.sqrt_pos.2 (by positivity)

/-- In the `(s,t,L)=(1,2,1)` Theorem 2 specialization, positive `lambda`
ensures the normalizing `Q_{2,1}` denominator is nonzero. -/
theorem theorem2TwoRowsCandidate_eq_normalizedNuttallQIncrement_of_pos
    (lambda x : ℝ) (hlambda : 0 < lambda) :
    theorem2CdfCandidate 1 2 1 (by omega) (by omega)
      (fun _ : Fin 1 => lambda) x =
      ‖nuttallQ 2 1 (Real.sqrt (2 * lambda)) 0 -
        nuttallQ 2 1 (Real.sqrt (2 * lambda)) (Real.sqrt (2 * x))‖ /
      ‖nuttallQ 2 1 (Real.sqrt (2 * lambda)) 0‖ := by
  exact theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement
    2 (by omega) lambda x
    (nuttallQ21_zeroThreshold_ne_zero (Real.sqrt (2 * lambda))
      (Real.sqrt_pos.2 (by positivity)))

end JinWishart
