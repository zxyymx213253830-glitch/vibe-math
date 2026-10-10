import JinWishartFormalization.TwoRowGramChart

open JinWishart

theorem twoRowGramChart_positive_image :
    twoRowGramChart '' {p : GramChartSpace | 0 < p 0 ∧ 0 < p 3} =
      {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3} := by
  sorry
