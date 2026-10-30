import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Codex. Seed 2026103006 Nuttall/Gamma quadrature controls precede source.
Unconditional one-dimensional positive-half-line substitution, not a
Wishart-law identification. [需人工审查] Change-of-variables and endpoints. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

theorem quadraticEnergy_image_Ioi (a : ℝ) (ha : 0 ≤ a) :
 (fun r : ℝ => r^2/2) '' Ioi a = Ioi (a^2/2) := by
 ext y
 constructor
 · rintro ⟨r,hr,rfl⟩
   change a < r at hr
   change a^2/2 < r^2/2
   nlinarith [sq_nonneg (r-a)]
 · intro hy
   have hypos : 0 ≤ 2*y := by
     have hsq := sq_nonneg a
     change a^2/2 < y at hy
     nlinarith
   refine ⟨Real.sqrt (2*y), ?_, ?_⟩
   · have hs := Real.sq_sqrt hypos
     have hr := Real.sqrt_nonneg (2*y)
     change a^2/2 < y at hy
     change a < Real.sqrt (2*y)
     nlinarith
   · change (Real.sqrt (2*y))^2/2 = y
     rw [Real.sq_sqrt hypos]
     ring

theorem quadraticEnergy_tail_substitution (a : ℝ) (ha : 0 ≤ a) (g : ℝ → ℝ) :
 (∫ y in Ioi (a^2/2), g y) = ∫ r in Ioi a, r * g (r^2/2) := by
 have hd : ∀ r ∈ Ioi a, HasDerivWithinAt (fun t : ℝ => t^2/2) r (Ioi a) r := by
   intro r hr
   have h : HasDerivAt (fun t : ℝ => t^2/2) r r := by
     convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;>
       simp only [Pi.pow_apply,id_eq] <;> ring
   exact h.hasDerivWithinAt
 have hinj : InjOn (fun r : ℝ => r^2/2) (Ioi a) := by
   intro r hr s hs he
   have hr0 : 0 < r := lt_of_le_of_lt ha hr
   have hs0 : 0 < s := lt_of_le_of_lt ha hs
   nlinarith [sq_nonneg (r-s)]
 have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
 rw [quadraticEnergy_image_Ioi a ha] at h
 calc
   _ = ∫ r in Ioi a, |r| * g (r^2/2) := by simpa [smul_eq_mul] using h
   _ = _ := by
     apply setIntegral_congr_fun measurableSet_Ioi
     intro r hr
     change |r| * g (r^2/2) = r * g (r^2/2)
     rw [abs_of_pos (lt_of_le_of_lt ha hr)]

end
end JinWishart
#print axioms JinWishart.quadraticEnergy_image_Ioi
#print axioms JinWishart.quadraticEnergy_tail_substitution
