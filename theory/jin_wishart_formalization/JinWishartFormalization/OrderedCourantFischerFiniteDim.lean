import JinWishartFormalization.SpectralRayleighCoordinates
import JinWishartFormalization.SpectralRayleighPrefix
import JinWishartFormalization.SubspaceIntersectionFinrank
import JinWishartFormalization.IndexedCourantFischerAttempt

/-!
# Courant--Fischer extrema for real symmetric operators

This file sets up the actual `sSup`/`sInf` formulation on nonzero vectors in
finite-dimensional subspaces. It also proves the boundedness facts needed for
these extrema. The remaining theorem is the indexed subspace min--max
characterization.
-/

namespace JinWishart

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Rayleigh quotients attained by nonzero vectors of a subspace. -/
noncomputable def rayleighValues (T : E →L[ℝ] E) (U : Submodule ℝ E) : Set ℝ :=
  Set.range fun x : {x : U // x.1 ≠ 0} => T.rayleighQuotient x.1.1

/-- All Rayleigh quotients of a bounded operator lie below its operator norm. -/
theorem rayleighValues_bddAbove (T : E →L[ℝ] E) (U : Submodule ℝ E) :
    BddAbove (rayleighValues T U) := by
  refine ⟨‖T‖, ?_⟩
  rintro y ⟨x, rfl⟩
  have h := abs_rayleighQuotient_sub_le_operatorNorm T 0 x.1.1
  have h' : |T.rayleighQuotient x.1.1| ≤ ‖T‖ := by simpa using h
  exact le_trans (le_abs_self (T.rayleighQuotient x.1.1)) h'

/-- The exact supremum of the Rayleigh quotient over nonzero vectors of `U`. -/
noncomputable def rayleighSup (T : E →L[ℝ] E) (U : Submodule ℝ E) : ℝ :=
  sSup (rayleighValues T U)

/-- Every Rayleigh quotient in `U` is below its supremum. -/
theorem rayleighQuotient_le_rayleighSup
    (T : E →L[ℝ] E) (U : Submodule ℝ E) (x : U) (hx : x.1 ≠ 0) :
    T.rayleighQuotient x.1 ≤ rayleighSup T U := by
  unfold rayleighSup
  apply le_csSup (rayleighValues_bddAbove T U)
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Admissible subspaces in the indexed min--max statement. -/
def CourantFischerSubspaces (n : ℕ) (i : Fin n) :=
  {U : Submodule ℝ E // Module.finrank ℝ U = n - i.val}

/-- The inner supremum, indexed by admissible subspaces of dimension `n-i`. -/
noncomputable def indexedRayleighSupSet (T : E →L[ℝ] E) (n : ℕ) (i : Fin n) : Set ℝ :=
  Set.range fun U : CourantFischerSubspaces (E := E) n i => rayleighSup T U.1

/-- The indexed Courant--Fischer min--max value, with the descending eigenvalue
indexing convention used by Mathlib. -/
noncomputable def indexedCourantFischerValue
    (T : E →L[ℝ] E) (n : ℕ) (i : Fin n) : ℝ :=
  sInf (indexedRayleighSupSet T n i)

end JinWishart
