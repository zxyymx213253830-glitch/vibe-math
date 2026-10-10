import JinWishartFormalization.TwoRowGramChart

open JinWishart

/- The first support-image attempt failed. This is the smaller first step.
Expand the four chart entries, rewrite squares of products, and use
Real.sq_sqrt (le_of_lt hp). The remaining equality is polynomial algebra.
Do not change the definitions or target. -/
theorem twoRowGramChart_determinant (p : GramChartSpace) (hp : 0 < p 0) :
    twoRowGramChart p 0 * twoRowGramChart p 3 -
      (twoRowGramChart p 1) ^ 2 - (twoRowGramChart p 2) ^ 2 = p 0 * p 3 := by
  sorry
