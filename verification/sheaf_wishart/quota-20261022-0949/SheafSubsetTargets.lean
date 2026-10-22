import JinWishartFormalization.GramAllMinorCoefficient
import Lean
open Matrix Finset Function Polynomial
namespace SheafSubset
noncomputable section
def Fiber : Prop := ∀ {q m : ℕ} (S : {S : Finset (Fin m) // S.card=q}),
 Nonempty ((Equiv.Perm (Fin q)) ≃ {f : {f : Fin q→Fin m // Injective f} // JinWishart.injectiveFunctionImage f=S})
def Grouping : Prop := ∀ {q m : ℕ} (w : (Fin q→Fin m)→ℂ),
 (∀ f,¬Injective f → w f=0) → (∀ f (σ : Equiv.Perm (Fin q)),w (fun i=>f (σ i))=w f) →
 (∑ f : Fin q→Fin m,w f)=(q.factorial : ℂ)*∑ S : {S : Finset (Fin m) // S.card=q},
 w (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val)
def Invariance : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ)
 (f : Fin q→Fin m) (σ : Equiv.Perm (Fin q)),
 (A.submatrix id (fun i=>f (σ i))).det*(B.submatrix (fun i=>f (σ i)) id).det=
 (A.submatrix id f).det*(B.submatrix f id).det
def CB : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ),
 (A*B).det=∑ S : {S : Finset (Fin m) // S.card=q},
 (A.submatrix id (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val)).det*
 (B.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val) id).det
def Gram : Prop := ∀ {m q : ℕ} (B : Matrix (Fin m) (Fin q) ℂ),
 (JinWishart.complexGram B).det=∑ S : {S : Finset (Fin m) // S.card=q},
 star ((B.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val) id).det)*
 (B.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val) id).det
def Principal : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
 (T : {T : Finset (Fin n) // T.card=q}),
 ((JinWishart.complexGram X).submatrix (Subtype.val : T.val→Fin n) Subtype.val).det=
 (JinWishart.complexGram (X.submatrix id (fun j=>(JinWishart.cardinalSubsetEnumeration T j).val))).det
def Coeff : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (q : ℕ),
 ((1+(Polynomial.X : ℂ[X]) • (JinWishart.complexGram X).map Polynomial.C).det).coeff q=
 ∑ T : {T : Finset (Fin n) // T.card=q},∑ S : {S : Finset (Fin m) // S.card=q},
 star ((X.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val)
 (fun j=>(JinWishart.cardinalSubsetEnumeration T j).val)).det)*
 (X.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val)
 (fun j=>(JinWishart.cardinalSubsetEnumeration T j).val)).det
def RealCoeff : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (q : ℕ),
 (((1+(Polynomial.X : ℂ[X]) • (JinWishart.complexGram X).map Polynomial.C).det).coeff q).re=
 ∑ T : {T : Finset (Fin n) // T.card=q},∑ S : {S : Finset (Fin m) // S.card=q},
 Complex.normSq ((X.submatrix (fun i=>(JinWishart.cardinalSubsetEnumeration S i).val)
 (fun j=>(JinWishart.cardinalSubsetEnumeration T j).val)).det)
end
end SheafSubset
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.permutation_injective_image_fiber_equiv,`SheafSubset.Fiber),
 (`JinWishart.sum_functions_eq_factorial_sum_cardinal_subsets,`SheafSubset.Grouping),
 (`JinWishart.rectangular_minor_product_permutation_invariant,`SheafSubset.Invariance),
 (`JinWishart.det_mul_rectangular_sum_cardinal_subsets,`SheafSubset.CB),
 (`JinWishart.gram_det_sum_squared_cardinal_minors,`SheafSubset.Gram),
 (`JinWishart.gram_principal_minor_eq_enumerated_gram,`SheafSubset.Principal),
 (`JinWishart.gram_polynomial_coefficient_eq_sum_squared_minors,`SheafSubset.Coeff),
 (`JinWishart.gram_polynomial_coefficient_re_eq_sum_normSq_minors,`SheafSubset.RealCoeff)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
