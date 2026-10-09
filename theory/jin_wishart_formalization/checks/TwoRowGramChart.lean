import JinWishartFormalization.TwoRowGramChart

open MeasureTheory JinWishart
open scoped ENNReal

#print axioms twoRowGramChart_eq_BartlettGram_real
#print axioms twoRowGramChart_left_inverse
#print axioms twoRowGramChart_injOn
#print axioms hasFDerivAt_twoRowGramChart
#print axioms twoRowGramChartDerivative_det
#print axioms twoRowGramChart_lintegral_change

example : twoRowGramChart ![1, 2, 3, 4] = ![1, 2, 3, 17] := by
  ext i
  fin_cases i <;> norm_num [twoRowGramChart]

example (p : GramChartSpace) (hp : 0 < p 0) :
    twoRowGramChartInverse (twoRowGramChart p) = p :=
  twoRowGramChart_left_inverse p hp

example (p : GramChartSpace) (hp : 0 < p 0) :
    (twoRowGramChartDerivative p).toLinearMap.det = p 0 :=
  twoRowGramChartDerivative_det p hp

example (p : ℝ × (ℂ × ℝ)) :
    twoRowGramChart (twoRowBartlettRealCoordinates p) =
      twoRowGramRealCoordinates (twoRowBartlettGram p) :=
  twoRowGramChart_eq_BartlettGram_real p

example (g : GramChartSpace → ℝ≥0∞) :
    ∫⁻ q in twoRowGramChart '' {p : GramChartSpace | 0 < p 0}, g q =
      ∫⁻ p in {p : GramChartSpace | 0 < p 0},
        ENNReal.ofReal (p 0) * g (twoRowGramChart p) :=
  twoRowGramChart_lintegral_change g
