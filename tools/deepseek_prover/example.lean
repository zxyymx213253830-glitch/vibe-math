import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Reference result: 120% of 30 minus 130% of 20 is 10.
theorem prover_install_example :
    abs ((120 : Real) / 100 * 30 - 130 / 100 * 20) = 10 := by
  sorry
