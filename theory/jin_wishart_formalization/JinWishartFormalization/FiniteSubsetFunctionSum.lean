import JinWishartFormalization.AveragedCauchyBinet
import Mathlib.Data.Finset.Powerset

/-! Group permutation-invariant function weights by their injective image.
The target sum includes all cardinality-q subsets, including the empty case.
Codex finite algebra; no stochastic or analytic assumptions. -/
open Finset Function
namespace JinWishart
noncomputable section

def cardinalSubsetEnumeration {q m : ℕ} (S : {S : Finset (Fin m) // S.card = q}) :
    Fin q ≃ S.val := Fintype.equivOfCardEq (by simpa using S.property.symm)

def injectiveFunctionImage {q m : ℕ} (f : {f : Fin q → Fin m // Injective f}) :
    {S : Finset (Fin m) // S.card = q} :=
  ⟨univ.image f.val, by simp [card_image_of_injective _ f.property]⟩

theorem permutation_injective_image_fiber_equiv {q m : ℕ}
    (S : {S : Finset (Fin m) // S.card = q}) :
    Nonempty ((Equiv.Perm (Fin q)) ≃
      {f : {f : Fin q → Fin m // Injective f} // injectiveFunctionImage f = S}) := by
  classical
  let e := cardinalSubsetEnumeration S
  let F : Equiv.Perm (Fin q) → {f : {f : Fin q → Fin m // Injective f} // injectiveFunctionImage f = S} :=
    fun σ => ⟨⟨fun i => (e (σ i)).val, Subtype.val_injective.comp (e.injective.comp σ.injective)⟩, by
      apply Subtype.ext
      ext j
      simp only [injectiveFunctionImage,mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩
        exact (e (σ i)).property
      · intro hj
        obtain ⟨i,hi⟩ := (e.surjective.comp σ.surjective) ⟨j,hj⟩
        exact ⟨i,congrArg Subtype.val hi⟩⟩
  have hF : Bijective F := by
    constructor
    · intro σ τ h
      apply Equiv.ext
      intro i
      apply e.injective
      apply Subtype.ext
      exact congrFun (congrArg (fun x => x.val.val) h) i
    · intro f
      have hm (i : Fin q) : f.val.val i ∈ S.val := by
        have h := congrArg Subtype.val f.property
        rw [← h]
        exact mem_image_of_mem _ (mem_univ i)
      let g : Fin q → S.val := fun i => ⟨f.val.val i,hm i⟩
      have hg : Injective g := by
        intro i j h
        exact f.val.property (congrArg Subtype.val h)
      let E : Fin q ≃ S.val := Equiv.ofBijective g ⟨hg,hg.surjective_of_finite e⟩
      refine ⟨E.trans e.symm, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext i
      change (e (e.symm (E i))).val = f.val.val i
      simp only [e.apply_symm_apply]
      rfl
  exact ⟨Equiv.ofBijective F hF⟩

theorem sum_functions_eq_factorial_sum_cardinal_subsets {q m : ℕ}
    (w : (Fin q → Fin m) → ℂ)
    (hz : ∀ f, ¬ Injective f → w f = 0)
    (hp : ∀ f (σ : Equiv.Perm (Fin q)), w (fun i => f (σ i)) = w f) :
    (∑ f : Fin q → Fin m, w f) = (q.factorial : ℂ) *
      ∑ S : {S : Finset (Fin m) // S.card = q},
        w (fun i => (cardinalSubsetEnumeration S i).val) := by
  classical
  have hr : (∑ f : Fin q → Fin m, w f) =
      ∑ f : {f : Fin q → Fin m // Injective f}, w f.val := by
    rw [← Finset.sum_subtype (univ.filter Injective) (by simp) w]
    exact (Finset.sum_filter_of_ne fun f _ hf => by
      by_contra h; exact hf (hz f h)).symm
  rw [hr,← Fintype.sum_fiberwise injectiveFunctionImage (fun f => w f.val)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  let e := cardinalSubsetEnumeration S
  obtain ⟨E⟩ := permutation_injective_image_fiber_equiv S
  -- The fiber has q! elements; each is a permutation of the chosen enumeration.
  have hc : Fintype.card {f : {f : Fin q → Fin m // Injective f} // injectiveFunctionImage f = S} = q.factorial := by
    rw [← Fintype.card_congr E,Fintype.card_perm,Fintype.card_fin]
  have hw (f : {f : {f : Fin q → Fin m // Injective f} // injectiveFunctionImage f = S}) :
      w f.val.val = w (fun i => (e i).val) := by
    have hm (i : Fin q) : f.val.val i ∈ S.val := by
      have h := congrArg Subtype.val f.property
      rw [← h]
      exact mem_image_of_mem _ (mem_univ i)
    let g : Fin q → S.val := fun i => ⟨f.val.val i,hm i⟩
    have hg : Injective g := by
      intro i j h
      exact f.val.property (congrArg Subtype.val h)
    let E' : Fin q ≃ S.val := Equiv.ofBijective g ⟨hg,hg.surjective_of_finite e⟩
    have he : (fun i => (e ((E'.trans e.symm) i)).val) = f.val.val := by
      funext i
      change (e (e.symm (E' i))).val = f.val.val i
      simp only [e.apply_symm_apply]
      rfl
    rw [← he]
    exact hp (fun i => (e i).val) (E'.trans e.symm)
  simp_rw [hw]
  simp [hc,e]

end
end JinWishart
#print axioms JinWishart.permutation_injective_image_fiber_equiv
#print axioms JinWishart.sum_functions_eq_factorial_sum_cardinal_subsets
