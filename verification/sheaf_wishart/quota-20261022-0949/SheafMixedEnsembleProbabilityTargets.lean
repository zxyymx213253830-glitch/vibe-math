import JinWishartFormalization.MixedEnsembleProbability
import Lean
open MeasureTheory Matrix Set JinWishart
open scoped ENNReal
namespace SheafMixedEnsembleProbability
noncomputable section
def Scalar : Prop := ∀ (q k : ℕ) (lambda : ℝ), 0 ≤ lambda →
 IntegrableOn (fun t : ℝ => t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t) (Ioi 0) ∧
 (∫ t in Ioi (0 : ℝ), t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t) =
   Real.exp lambda * poissonFactorialMomentPolynomial q k lambda
def Pair : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ i j : Fin (p+L),
 IntegrableOn (fun t => mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t) (Ioi 0) ∧
 (∫ t in Ioi (0 : ℝ), mixedEnsembleF p L i t * mixedEnsembleG p L q lambda j t) =
   match (finSumFinEquiv (m := p) (n := L)).symm j with
   | Sum.inl a => ((q+i.val+a.val).factorial : ℝ)
   | Sum.inr b => Real.exp (lambda b)*poissonFactorialMomentPolynomial q i.val (lambda b)
def MatrixEq : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda) =
 (Matrix.of (fun i j => mixedEnsembleColumnFactor p L lambda j *
   mixedNoncentralMomentMatrix q p L lambda i j)).submatrix
     (finSumFinEquiv (m := p) (n := L)).symm (finSumFinEquiv (m := p) (n := L)).symm
def MatrixPositive : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) →
 0 < (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda)).det
def Probability : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → IsProbabilityMeasure (mixedCandidateEnsemble p L q lambda)
def Count : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (E : Set ℝ), MeasurableSet E → ∀ (k : ℕ), k ≤ p+L →
 ((mixedCandidateEnsemble p L q lambda) {z | coordinateMembershipCount E z = k}).toReal =
 ((rowAffinePolynomialMatrix
   (Matrix.of (fun i j => ∫ y in E, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
     ∂(volume.restrict (Ioi (0 : ℝ)))))
   (Matrix.of (fun i j => ∫ y in Eᶜ, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
     ∂(volume.restrict (Ioi (0 : ℝ)))))).det).coeff k /
       (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
         (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
end
end SheafMixedEnsembleProbability
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.scalarSeriesKernel_weightedMoment,`SheafMixedEnsembleProbability.Scalar),
 (`JinWishart.mixedEnsemble_pair_moment,`SheafMixedEnsembleProbability.Pair),
 (`JinWishart.mixedEnsemble_momentMatrix_eq,`SheafMixedEnsembleProbability.MatrixEq),
 (`JinWishart.mixedEnsemble_momentMatrix_det_pos,`SheafMixedEnsembleProbability.MatrixPositive),
 (`JinWishart.mixedCandidateEnsemble_probability,`SheafMixedEnsembleProbability.Probability),
 (`JinWishart.mixedCandidateEnsemble_count,`SheafMixedEnsembleProbability.Count)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed ensemble probability literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
