import PEqualNP.MetaComplexity.Helpers.LupanovLibrary
import PEqualNP.MetaComplexity.Helpers.LupanovMux

/-!
# The two-level construction: a library of all functions of `k` variables, then a multiplexer

Helper for `L-meta-003`. Every function of `n` variables, for any split `k ≤ n`, has a circuit
with at most `2 ^ 2 ^ k * (5 * 2 ^ k) + 4 * 2 ^ (n - k)` gates.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : HasCircuitSize n f s) (hst : s ≤ t) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, h2.trans hst, h3⟩

theorem lupanovTwoLevel (k n : ℕ) (hk : k ≤ n) (f : (Fin n → Bool) → Bool) :
    HasCircuitSize n f (2 ^ 2 ^ k * (5 * 2 ^ k) + 4 * 2 ^ (n - k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  obtain ⟨lib, idx, okl, lenl, hidx, evl⟩ := lupanovLibrary k (k + j) (Nat.le_add_right k j)
  obtain ⟨mx, out, okm, lenm, _, evm⟩ :=
    lupanovMux k idx j f (k + j + lib.length) (by omega) hidx
  refine ⟨⟨lib ++ mx, out⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact okl g hg
    · exact okm g hg
  · simp only [Circuit.size, List.length_append]; omega
  · intro x
    have hlen : (List.ofFn x).length = k + j := by simp
    have lw : (wiresFrom lib (List.ofFn x)).length = k + j + lib.length := by
      rw [length_wiresFrom, hlen]
    have pre : ∀ i : ℕ, i < k + j →
        (wiresFrom lib (List.ofFn x)).getD i false = (List.ofFn x).getD i false :=
      fun i hi => getD_wiresFrom _ _ _ (by rw [hlen]; exact hi)
    have hlib : ∀ g : (Fin k → Bool) → Bool,
        (wiresFrom lib (List.ofFn x)).getD (idx g) false
          = g (fun i : Fin k => (wiresFrom lib (List.ofFn x)).getD i false) := by
      intro g
      rw [evl (List.ofFn x) hlen g]
      congr 1; funext i
      exact (pre i (by have := i.isLt; omega)).symm
    have h := evm (wiresFrom lib (List.ofFn x)) lw hlib
    simp only [Circuit.eval, wires_eq, wiresFrom_append, h]
    congr 1; funext i
    rw [pre i i.isLt]; simp

end PEqualNP.MetaComplexity.Helpers
