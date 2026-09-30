import JinWishartFormalization.RepeatedRootNullSets
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Null zero sets of real multivariate polynomials

The proof is by induction on the number of variables.  Split off the first coordinate, regard the
polynomial as univariate with multivariate coefficients, and apply the induction hypothesis to its
nonzero leading coefficient.  Outside that exceptional null set, the one-dimensional fiber is a
finite polynomial zero set.  Tonelli/Fubini then gives the product-space null result.
-/

open MeasureTheory

namespace JinWishart

set_option maxRecDepth 4096

/-- A nonzero polynomial in finitely many real variables has a Lebesgue-null zero set.

The ambient space is the finite product `Fin n → ℝ`, equipped with its standard product
Lebesgue measure (definitionally the finite-dimensional Lebesgue volume used by Mathlib). -/
theorem mvPolynomial_zeroSet_volume_eq_zero :
    ∀ n (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hconst : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.eq_C_of_isEmpty p
      have hc : p.coeff 0 ≠ 0 := by
        intro hzero
        apply hp
        rw [hconst, hzero, MvPolynomial.C_0]
      have hset : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hconst, MvPolynomial.eval_C]
        exact hc
      rw [hset]
      simp
  | succ n ih =>
      intro p hp
      classical
      let q : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n p
      have hq : q ≠ 0 := by
        intro h
        exact hp ((MvPolynomial.finSuccEquiv ℝ n).injective h)
      let r : MvPolynomial (Fin n) ℝ := q.leadingCoeff
      have hr : r ≠ 0 := by
        intro h
        exact hq ((Polynomial.leadingCoeff_eq_zero).mp h)
      have hException : volume {y : Fin n → ℝ | MvPolynomial.eval y r = 0} = 0 :=
        ih r hr
      have hExceptionAE : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
          MvPolynomial.eval y r ≠ 0 := by
        simpa [ae_iff, Set.mem_setOf_eq] using hException

      let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let S : Set (ℝ × (Fin n → ℝ)) :=
        {z | MvPolynomial.eval
          (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) p = 0}
      have hS : MeasurableSet S := by
        have hcons : Continuous (fun z : ℝ × (Fin n → ℝ) =>
            (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)) := by
          apply continuous_pi
          intro i
          refine Fin.cases ?_ ?_ i
          · exact continuous_fst
          · intro j
            exact (continuous_apply j).comp continuous_snd
        have heval : Continuous (fun z : ℝ × (Fin n → ℝ) =>
            MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) p) :=
          (MvPolynomial.continuous_eval p).comp hcons
        change MeasurableSet {z : ℝ × (Fin n → ℝ) |
          MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) p = 0}
        exact (isClosed_singleton.preimage heval).measurableSet

      have hpres : MeasurePreserving e :=
        MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hpre : e ⁻¹' S = {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
        have hpoint :
            (Fin.cons (e x).1 (e x).2 : Fin (n + 1) → ℝ) = x := by
          funext i
          refine Fin.cases ?_ ?_ i
          · simp [e, MeasurableEquiv.piFinSuccAbove]
          · intro j
            rfl
        rw [hpoint]
      have hmeasure :
          volume {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} = volume S := by
        rw [← hpre, ← hpres.map_eq]
        exact (e.map_apply S).symm

      have hqEval_ne (y : Fin n → ℝ) (hy : MvPolynomial.eval y r ≠ 0) :
          Polynomial.map (MvPolynomial.eval y) q ≠ 0 := by
        intro hzero
        have hlead : (Polynomial.map (MvPolynomial.eval y) q).leadingCoeff = 0 := by
          simp [hzero]
        have hlead' : (Polynomial.map (MvPolynomial.eval y) q).leadingCoeff =
            MvPolynomial.eval y r := by
          rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy]
        rw [hlead'] at hlead
        exact hy hlead

      have hFiber (y : Fin n → ℝ) (hy : MvPolynomial.eval y r ≠ 0) :
          volume {t : ℝ | MvPolynomial.eval (Fin.cons t y : Fin (n + 1) → ℝ) p = 0} = 0 := by
        have hset : {t : ℝ | MvPolynomial.eval (Fin.cons t y : Fin (n + 1) → ℝ) p = 0} =
            {t : ℝ | Polynomial.eval t (Polynomial.map (MvPolynomial.eval y) q) = 0} := by
          ext t
          change (MvPolynomial.eval (Fin.cons t y : Fin (n + 1) → ℝ) p = 0) ↔
            Polynomial.eval t (Polynomial.map (MvPolynomial.eval y) q) = 0
          rw [MvPolynomial.eval_eq_eval_mv_eval' y t p]
        rw [hset]
        exact real_polynomial_zeroSet_volume_eq_zero
          (Polynomial.map (MvPolynomial.eval y) q) (hqEval_ne y hy)

      have hFiberAE :
          (fun y : Fin n → ℝ => volume ((fun t : ℝ => (t, y)) ⁻¹' S)) =ᵐ[volume] 0 := by
        filter_upwards [hExceptionAE] with y hy
        simpa [S] using hFiber y hy

      have hSzero : volume S = 0 := by
        rw [Measure.volume_eq_prod ℝ (Fin n → ℝ), Measure.prod_apply_symm hS]
        exact lintegral_eq_zero_of_ae_eq_zero hFiberAE
      rw [hmeasure, hSzero]

end JinWishart
