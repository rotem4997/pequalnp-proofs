import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# The library of all functions of the first `k` wires

Helper 1 for `L-meta-003`. One Shannon circuit for each of the `2 ^ 2 ^ k` functions of the
first `k` wires, appended one after another at an arbitrary wire offset `m ≥ k`; `idx g` is
the output wire of the circuit for `g`.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The list version: one Shannon circuit for each function in `L`. -/
theorem lupanovLibraryList (k : ℕ) : ∀ (L : List ((Fin k → Bool) → Bool)) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (idx : ((Fin k → Bool) → Bool) → ℕ),
      (∀ g ∈ gs, Ok g) ∧ gs.length ≤ L.length * (5 * 2 ^ k) ∧
      ∀ g ∈ L, idx g < m + gs.length ∧
        ∀ w : List Bool, w.length = m →
          (wiresFrom gs w).getD (idx g) false = g (fun i : Fin k => w.getD i false) := by
  intro L
  induction L with
  | nil =>
    intro m _
    exact ⟨[], fun _ => 0, by simp, by simp, by simp⟩
  | cons g L ih =>
    intro m hm
    classical
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ := shannon k g m hm
    obtain ⟨gs1, idx1, ok1, len1, hidx1⟩ := ih (m + gs0.length) (by omega)
    refine ⟨gs0 ++ gs1, fun h => if h = g then o0 else idx1 h, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ok0 x hx
      · exact ok1 x hx
    · simp only [List.length_append, List.length_cons]
      rw [Nat.succ_mul]; omega
    · intro h hh
      by_cases hg : h = g
      · subst hg
        simp only [ite_true]
        refine ⟨by simp only [List.length_append]; omega, ?_⟩
        intro w hw
        rw [wiresFrom_append,
          getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; omega)]
        exact ev0 w hw
      · simp only [hg, ite_false]
        have hL : h ∈ L := by
          rcases List.mem_cons.mp hh with h' | h'
          · exact absurd h' hg
          · exact h'
        obtain ⟨hlt, hev⟩ := hidx1 h hL
        refine ⟨by simp only [List.length_append]; omega, ?_⟩
        intro w hw
        have l1 : (wiresFrom gs0 w).length = m + gs0.length := by rw [length_wiresFrom, hw]
        rw [wiresFrom_append, hev _ l1]
        congr 1; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)

theorem lupanovLibrary (k m : ℕ) (hk : k ≤ m) :
    ∃ (gs : List Gate) (idx : ((Fin k → Bool) → Bool) → ℕ),
      (∀ g ∈ gs, Ok g) ∧ gs.length ≤ 2 ^ 2 ^ k * (5 * 2 ^ k) ∧
      (∀ g, idx g < m + gs.length) ∧
      ∀ w : List Bool, w.length = m → ∀ g : (Fin k → Bool) → Bool,
        (wiresFrom gs w).getD (idx g) false = g (fun i : Fin k => w.getD i false) := by
  obtain ⟨gs, idx, ok, len, h⟩ :=
    lupanovLibraryList k (Finset.univ : Finset ((Fin k → Bool) → Bool)).toList m hk
  have hcard : (Finset.univ : Finset ((Fin k → Bool) → Bool)).toList.length = 2 ^ 2 ^ k := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  refine ⟨gs, idx, ok, by rw [← hcard]; exact len, fun g => (h g (by simp)).1, ?_⟩
  intro w hw g
  exact (h g (by simp)).2 w hw

end PEqualNP.MetaComplexity.Helpers
