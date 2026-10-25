import JinWishartFormalization.QuadraticChristoffelMomentDeterminant
import Lean
open Polynomial Matrix JinWishart
namespace SheafQuadraticChristoffel
noncomputable section
def Target : Prop := ∀ (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (p q : ℂ[X]),
 p.natDegree=n → p.Monic → q.natDegree=n+1 → q.Monic →
 (∀ i : Fin n,F (X^i.val*p)=0) → (∀ i : Fin n,F (X^i.val*q)=0) → ∀ z : ℂ,
 Matrix.det (fun i j : Fin n => F ((X-C z)^2*X^(i.val+j.val))) =
 Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))*
 (p.eval z*(Polynomial.derivative q).eval z-q.eval z*(Polynomial.derivative p).eval z)
end
end SheafQuadraticChristoffel
open Lean Meta in
#eval show MetaM Unit from do
 let a ← inferType (← mkConstWithFreshMVarLevels `JinWishart.quadratic_christoffel_moment_det)
 let e ← whnf (← mkConstWithFreshMVarLevels `SheafQuadraticChristoffel.Target)
 unless ← isDefEq a e do throwError "Quadratic Christoffel literal type differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
