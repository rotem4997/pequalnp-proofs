import PEqualNP.MetaComplexity.Helpers.Columns
import PEqualNP.MetaComplexity.Helpers.LocalHardPatch

/-!
# The patching lemma, with the changed entries counted by position

`LocalHardPatch.lipschitz` counts the changed entries over the inputs. Here they are counted
over the positions below `2 ^ n'` of the two tables. It is a separate file because it needs
`Columns` (`tableIndex` is injective and below `2 ^ n'`).
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalHardIdx

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- Partial circuit size is `(2 n' + 2)`-Lipschitz in the number of changed positions. -/
theorem lipschitz_idx : ∀ (n' k s : ℕ) (T T' : List (Option Bool)), ((Finset.range (2 ^ n')).filter fun e : ℕ => T.getD e none ≠ T'.getD e none).card ≤ k → (∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T' f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) → ∃ g : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T g ∧ PEqualNP.MetaComplexity.HasCircuitSize n' g (s + (2 * n' + 2) * k) := by
  classical
  intro n' k s T T' hk h
  refine LocalHardPatch.lipschitz n' k s T T' (le_trans ?_ hk) h
  refine Finset.card_le_card_of_injOn (fun x : Fin n' → Bool => tableIndex x) ?_ ?_
  · intro x hx
    have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (tableIndex_lt x), hx'⟩)
  · intro x _ y _ hxy
    exact tableIndex_injective hxy

end PEqualNP.MetaComplexity.Helpers.LocalHardIdx
