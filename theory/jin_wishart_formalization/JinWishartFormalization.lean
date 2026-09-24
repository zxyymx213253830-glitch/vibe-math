import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import JinWishartFormalization.IncompleteGamma
import JinWishartFormalization.NuttallQ
import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.WishartProbability
import JinWishartFormalization.RadialIntegration
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.MIMOPerformance
import JinWishartFormalization.GaussianQ
import JinWishartFormalization.MIMOWishartSER

/-!
# A Lean feasibility prototype for Jin--McKay--Gao--Collings (2008)

This file formalizes self-contained algebraic and analytic consequences used in
"MIMO Multichannel Beamforming: SER and Outage Using New Eigenvalue
Distributions of Complex Noncentral Wishart Matrices" (arXiv:cs/0611007).

It deliberately does **not** claim to formalize the paper's new Wishart
eigenvalue-distribution theorems.  See `README.md` for the exact scope.
-/

namespace JinWishart

open Real

/-- The Rice-factor term in the leading low-outage approximation, with the
integer exponent `n = s * t` abstracted as a natural number. -/
noncomputable def riceFactor (n : ℕ) (K : ℝ) : ℝ :=
  (K + 1) ^ n * Real.exp (-(K * n))

/-- Equation (45) of the paper: the derivative of the Rice-factor term. -/
theorem hasDerivAt_riceFactor (n : ℕ) (K : ℝ) :
    HasDerivAt (riceFactor n)
      (-(n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n))) K := by
  cases n with
  | zero =>
      convert (hasDerivAt_const (x := K) (c := (1 : ℝ))) using 1
      · funext x
        norm_num [riceFactor]
      · norm_num
  | succ n =>
      have hpow :
            HasDerivAt (fun x : ℝ => (x + 1) ^ (n + 1))
            ((n + 1 : ℕ) * (K + 1) ^ n) K := by
        convert ((hasDerivAt_id K).add_const 1).pow (n + 1) using 1
        · funext x
          simp
        · push_cast
          simp [id]
      have hinner :
          HasDerivAt (fun x : ℝ => -(x * (n + 1 : ℕ))) (-(n + 1 : ℕ)) K := by
        convert ((hasDerivAt_id K).mul_const (n + 1 : ℕ)).neg using 1
        · funext x
          simp
        · push_cast
          ring
      have hexp :
          HasDerivAt (fun x : ℝ => Real.exp (-(x * (n + 1 : ℕ))))
            (Real.exp (-(K * (n + 1 : ℕ))) * (-(n + 1 : ℕ))) K :=
        (Real.hasDerivAt_exp _).comp K hinner
      convert hpow.mul hexp using 1
      · funext x
        simp only [riceFactor, Nat.cast_add, Nat.cast_one, Pi.mul_apply]
      · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
        ring

/-- For a nonzero antenna product and positive Rice factor, the derivative in
Equation (45) is strictly negative.  This is the local monotonicity statement
behind the paper's low-outage conclusion. -/
theorem riceFactor_derivative_neg {n : ℕ} {K : ℝ}
    (hn : 0 < n) (hK : 0 < K) :
    -(n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n)) < 0 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hbase : 0 < K + 1 := by linarith
  have hpow : 0 < (K + 1) ^ (n - 1) := pow_pos hbase _
  have hexp : 0 < Real.exp (-(K * n)) := Real.exp_pos _
  have hprod :
      0 < (n : ℝ) * K * (K + 1) ^ (n - 1) * Real.exp (-(K * n)) := by
    positivity
  nlinarith

/-- For a nonzero antenna product, the Rice-factor term is strictly decreasing
on the physically relevant region `K > 0`.  This packages the derivative-sign
calculation into the monotonicity conclusion used after Equation (45). -/
theorem riceFactor_strictAntiOn {n : ℕ} (hn : 0 < n) :
    StrictAntiOn (riceFactor n) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact (continuous_iff_continuousAt.mpr fun K =>
      (hasDerivAt_riceFactor n K).continuousAt).continuousOn
  · intro K hK
    rw [(hasDerivAt_riceFactor n K).deriv]
    exact riceFactor_derivative_neg hn (by simpa using hK)

/-- A finite Gram energy is nonnegative.  In the MIMO model this is the
coordinate form of `xᴴ Hᴴ H x = ‖Hx‖² ≥ 0`, the deterministic fact behind the
nonnegative eigenmode gains of a Wishart/Gram matrix. -/
theorem gram_energy_nonneg {m n : ℕ}
    (H : Fin m → Fin n → ℂ) (x : Fin n → ℂ) :
    0 ≤ ∑ i, ‖∑ j, H i j * x j‖ ^ 2 := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- With equal nonnegative power/scaling, an ordered weakest eigenmode has the
smallest SNR.  This isolates the order argument used when the paper says the
weakest active subchannel dominates high-SNR error/outage. -/
theorem weakest_mode_has_smallest_snr
    {φweak φ : ℝ} {scale power : ℝ}
    (hφ : φweak ≤ φ) (hscale : 0 ≤ scale) (hpower : 0 ≤ power) :
    scale * φweak * power ≤ scale * φ * power := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hφ hscale) hpower

end JinWishart
