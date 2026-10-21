import JinWishartFormalization.BivariateGaussianPolynomialLog
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

/-! Finite products of planar standard complex Gaussians, each with complex
second moment2. This is NOT the proper CN1 scaling bridge or a Wishart offset.
Real.log0=0 is totalized; no extended-real log claim. Codex proofs.
[需人工审查] Gaussian normalization, null sets, product transport and Fubini.
-/
open MeasureTheory ProbabilityTheory Filter
namespace JinWishart
noncomputable section

def planarGaussianSplit (n : ℕ) :
    (Fin (n+1) → ℂ) ≃ᵐ ((Fin n → ℂ) × ℂ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).trans
    MeasurableEquiv.prodComm

theorem planarGaussianSplit_measurePreserving (n : ℕ) :
    MeasurePreserving (planarGaussianSplit n)
      (Measure.pi (fun _ : Fin (n+1) => stdGaussian ℂ))
      ((Measure.pi (fun _ : Fin n => stdGaussian ℂ)).prod (stdGaussian ℂ)) := by
  exact (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => stdGaussian ℂ) 0).trans Measure.measurePreserving_swap

theorem planarGaussianSplit_cons (n : ℕ) (x : Fin (n+1) → ℂ) :
    Fin.cons (planarGaussianSplit n x).2 (planarGaussianSplit n x).1 = x := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [planarGaussianSplit,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm]
  · intro j
    rfl

theorem stdGaussian_pi_mvPolynomial_ne_zero_ae :
    ∀ n (P : MvPolynomial (Fin n) ℂ), P≠0 →
      ∀ᵐ x ∂Measure.pi (fun _ : Fin n => stdGaussian ℂ),
        MvPolynomial.eval x P ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have hc : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
      have hn : P.coeff 0 ≠ 0 := by
        intro h
        apply hP
        rw [hc,h,MvPolynomial.C_0]
      exact ae_of_all _ (fun x => by rw [hc,MvPolynomial.eval_C]; exact hn)
  | succ n ih =>
      intro P hP
      classical
      let q := MvPolynomial.finSuccEquiv ℂ n P
      have hq : q≠0 := fun h => hP ((MvPolynomial.finSuccEquiv ℂ n).injective h)
      have hr : q.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      have hae := ih q.leadingCoeff hr
      have hcont : Continuous (fun w : (Fin n → ℂ) × ℂ =>
          MvPolynomial.eval (Fin.cons w.2 w.1) P) := by
        apply (MvPolynomial.continuous_eval P).comp
        apply continuous_pi
        intro i
        refine Fin.cases continuous_snd ?_ i
        intro j
        exact (continuous_apply j).comp continuous_fst
      have hpair : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => stdGaussian ℂ)).prod (stdGaussian ℂ),
          MvPolynomial.eval (Fin.cons w.2 w.1) P ≠ 0 := by
        apply (Measure.ae_prod_iff_ae_ae (isClosed_singleton.preimage hcont).isOpen_compl.measurableSet).mpr
        filter_upwards [hae] with y hy
        have hmap : Polynomial.map (MvPolynomial.eval y) q ≠ 0 := by
          apply Polynomial.leadingCoeff_ne_zero.mp
          rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy]
          exact hy
        have hf := stdGaussian_complex_polynomial_eval_ne_zero_ae
          (Polynomial.map (MvPolynomial.eval y) q) hmap
        simpa only [MvPolynomial.eval_eq_eval_mv_eval',q,Set.mem_preimage,Set.mem_singleton_iff] using hf
      have hb := (planarGaussianSplit_measurePreserving n).quasiMeasurePreserving.ae hpair
      simpa only [planarGaussianSplit_cons] using hb

theorem stdGaussian_pi_mvPolynomial_negativeLog_integrable :
    ∀ n (P : MvPolynomial (Fin n) ℂ),
      Integrable (fun x => complexNegativeLog (MvPolynomial.eval x P))
        (Measure.pi (fun _ : Fin n => stdGaussian ℂ)) := by
  intro n
  induction n with
  | zero =>
      intro P
      have hc : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
      rw [hc]
      simp only [MvPolynomial.eval_C]
      exact integrable_const _
  | succ n ih =>
      intro P
      classical
      by_cases hP : P=0
      · subst P
        simp [complexNegativeLog]
      let q := MvPolynomial.finSuccEquiv ℂ n P
      have hq : q≠0 := fun h => hP ((MvPolynomial.finSuccEquiv ℂ n).injective h)
      have hae := stdGaussian_pi_mvPolynomial_ne_zero_ae n q.leadingCoeff
        (Polynomial.leadingCoeff_ne_zero.mpr hq)
      have heq : (fun y => complexNegativeLog (Polynomial.map (MvPolynomial.eval y) q).leadingCoeff)
          =ᵐ[Measure.pi (fun _ : Fin n => stdGaussian ℂ)]
        (fun y => complexNegativeLog (MvPolynomial.eval y q.leadingCoeff)) := by
        filter_upwards [hae] with y hy
        rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy]
      have hcoeff := (ih q.leadingCoeff).congr heq.symm
      have hcont : Continuous (fun w : (Fin n → ℂ) × ℂ =>
          MvPolynomial.eval (Fin.cons w.2 w.1) P) := by
        apply (MvPolynomial.continuous_eval P).comp
        apply continuous_pi
        intro i
        refine Fin.cases continuous_snd ?_ i
        intro j
        exact (continuous_apply j).comp continuous_fst
      have heval (w : (Fin n → ℂ) × ℂ) :
          (Polynomial.map (MvPolynomial.eval w.1) q).eval w.2 =
            MvPolynomial.eval (Fin.cons w.2 w.1) P := by
        exact (MvPolynomial.eval_eq_eval_mv_eval' w.1 w.2 P).symm
      have hm : Measurable (fun w : (Fin n → ℂ) × ℂ =>
          (Polynomial.map (MvPolynomial.eval w.1) q).eval w.2) := by
        simpa only [heval] using hcont.measurable
      have hs := (integrable_polynomial_section_negativeLog
        (Measure.pi (fun _ : Fin n => stdGaussian ℂ))
        (fun y => Polynomial.map (MvPolynomial.eval y) q) hm hcoeff q.natDegree
        (ae_of_all _ (fun _ => Polynomial.natDegree_map_le))).1
      have hb := (planarGaussianSplit_measurePreserving n).integrable_comp_of_integrable hs
      simpa only [Function.comp_def,heval,planarGaussianSplit_cons] using hb

theorem integrable_stdGaussian_pi_mvPolynomial_eval (n : ℕ)
    (P : MvPolynomial (Fin n) ℂ) :
    Integrable (fun x => MvPolynomial.eval x P)
      (Measure.pi (fun _ : Fin n => stdGaussian ℂ)) := by
  classical
  simp_rw [MvPolynomial.eval_eq']
  apply integrable_finsetSum
  intro d _
  apply Integrable.const_mul
  apply Integrable.fintype_prod
  intro i
  have heq : (npowRec (d i) : ℂ → ℂ) = (fun z => z^d i) := by
    funext z
    induction d i with
    | zero => rfl
    | succ k ih => simpa only [npowRec,pow_succ,ih]
  rw [heq]
  simpa using integrable_stdGaussian_complex_polynomial_eval ((Polynomial.X : Polynomial ℂ)^d i)

theorem stdGaussian_pi_mvPolynomial_log_integrable (n : ℕ)
    (P : MvPolynomial (Fin n) ℂ) :
    Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖)
      (Measure.pi (fun _ : Fin n => stdGaussian ℂ)) := by
  have hf := (integrable_stdGaussian_pi_mvPolynomial_eval n P).norm
  have hn := stdGaussian_pi_mvPolynomial_negativeLog_integrable n P
  apply (hf.add hn).mono' (MvPolynomial.continuous_eval P).norm.measurable.log.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |Real.log ‖MvPolynomial.eval x P‖| ≤
    ‖MvPolynomial.eval x P‖+max 0 (-Real.log ‖MvPolynomial.eval x P‖)
  by_cases hz : MvPolynomial.eval x P=0
  · simp [hz]
  have hu := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)
  have h1 := le_max_left (0 : ℝ) (-Real.log ‖MvPolynomial.eval x P‖)
  have h2 := le_max_right (0 : ℝ) (-Real.log ‖MvPolynomial.eval x P‖)
  have hnorm := norm_nonneg (MvPolynomial.eval x P)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end JinWishart
#print axioms JinWishart.planarGaussianSplit_measurePreserving
#print axioms JinWishart.planarGaussianSplit_cons
#print axioms JinWishart.stdGaussian_pi_mvPolynomial_ne_zero_ae
#print axioms JinWishart.stdGaussian_pi_mvPolynomial_negativeLog_integrable
#print axioms JinWishart.integrable_stdGaussian_pi_mvPolynomial_eval
#print axioms JinWishart.stdGaussian_pi_mvPolynomial_log_integrable
