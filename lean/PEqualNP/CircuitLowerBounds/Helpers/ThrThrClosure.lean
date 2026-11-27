import Mathlib
import PEqualNP.Defs

/-!
Helper for L-clb-029: depth-two threshold circuits are closed under complement with the same
number of bottom gates. Keep the bottom gates, negate the top weights, and replace the top
threshold `t0` by `1 - t0`: for an integer `S`, `¬ t0 ≤ S` is the same as `1 - t0 ≤ -S`.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

theorem thrthr_compl (s : ℕ → ℕ) (L : Language Bool)
    (h : L ∈ PEqualNP.CircuitLowerBounds.THRTHR s) :
    Lᶜ ∈ PEqualNP.CircuitLowerBounds.THRTHR s := by
  intro n
  obtain ⟨k, w, t, a, t0, hk, hx⟩ := h n
  refine ⟨k, w, t, fun j => -a j, 1 - t0, hk, fun x => ?_⟩
  have hc : List.ofFn x ∈ Lᶜ ↔ ¬ List.ofFn x ∈ L := Set.mem_compl_iff L (List.ofFn x)
  rw [hc, hx x]
  simp only [neg_mul, Finset.sum_neg_distrib]
  constructor <;> intro h' <;> omega

end PEqualNP.CircuitLowerBounds.Helpers
