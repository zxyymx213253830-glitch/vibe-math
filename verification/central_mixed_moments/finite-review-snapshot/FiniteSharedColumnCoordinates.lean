import JinWishartFormalization.CentralWishartOverlappingSelectors
import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite common/exclusive coordinates for arbitrary column-set pairs.
Codex deterministic proofs; no probability or spectral-density premises.
-/
namespace JinWishart
noncomputable section

def sharedFront (c k : ℕ) (i : Fin c) : Fin (k+c) :=
  Fin.cast (Nat.add_comm c k) (Fin.castAdd k i)

def sharedTail (c k : ℕ) (i : Fin k) : Fin (k+c) :=
  Fin.cast (Nat.add_comm c k) (Fin.natAdd c i)

def sharedCoordinates (c k : ℕ) : Fin (k+c) ≃ Fin c ⊕ Fin k :=
  (finCongr (Nat.add_comm k c)).trans finSumFinEquiv.symm

theorem sharedCoordinates_symm_inl (c k : ℕ) (i : Fin c) :
    (sharedCoordinates c k).symm (Sum.inl i) = sharedFront c k i := by rfl

theorem sharedCoordinates_symm_inr (c k : ℕ) (i : Fin k) :
    (sharedCoordinates c k).symm (Sum.inr i) = sharedTail c k i := by rfl

theorem centralSharedPrefixSelection_front {k n : ℕ} (c : ℕ)
    (e : Fin k → Fin n) (i : Fin c) :
    centralSharedPrefixSelection c e (sharedFront c k i) = sharedFront c n i := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · have h0 : sharedFront (c+1) k 0 = 0 := by ext; rfl
        rw [h0]
        change (0 : Fin (n+(c+1))) = _
        apply Fin.ext
        rfl
      · have hs : sharedFront (c+1) k j.succ = (sharedFront c k j).succ := by ext; rfl
        rw [hs]
        change (centralSharedPrefixSelection c e (sharedFront c k j)).succ = _
        rw [ih]
        apply Fin.ext
        rfl

theorem centralSharedPrefixSelection_tail {k n : ℕ} (c : ℕ)
    (e : Fin k → Fin n) (i : Fin k) :
    centralSharedPrefixSelection c e (sharedTail c k i) = sharedTail c n (e i) := by
  induction c with
  | zero => simp [centralSharedPrefixSelection, sharedTail]
  | succ c ih =>
      have hs : sharedTail (c+1) k i = (sharedTail c k i).succ := by
        apply Fin.ext
        simp [sharedTail]
        omega
      rw [hs]
      change (centralSharedPrefixSelection c e (sharedTail c k i)).succ = _
      rw [ih]
      apply Fin.ext
      simp [sharedTail]
      omega

theorem centralSharedPrefixSelection_coordinates {k n : ℕ} (c : ℕ)
    (e : Fin k → Fin n) (i : Fin (k+c)) :
    (sharedCoordinates c n) (centralSharedPrefixSelection c e i) =
      Sum.map id e ((sharedCoordinates c k) i) := by
  obtain ⟨j,rfl⟩ := (sharedCoordinates c k).symm.surjective i
  rcases j with j | j
  · rw [sharedCoordinates_symm_inl, centralSharedPrefixSelection_front]
    rw [← sharedCoordinates_symm_inl c n j, ← sharedCoordinates_symm_inl c k j]
    simp
  · rw [sharedCoordinates_symm_inr, centralSharedPrefixSelection_tail]
    rw [← sharedCoordinates_symm_inr c n (e j), ← sharedCoordinates_symm_inr c k j]
    simp

end
end JinWishart
#print axioms JinWishart.sharedCoordinates_symm_inl
#print axioms JinWishart.sharedCoordinates_symm_inr
#print axioms JinWishart.centralSharedPrefixSelection_front
#print axioms JinWishart.centralSharedPrefixSelection_tail
#print axioms JinWishart.centralSharedPrefixSelection_coordinates
