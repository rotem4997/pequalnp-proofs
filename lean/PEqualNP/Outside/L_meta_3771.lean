import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_3771

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma four_points : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter fun l : Fin 13 =>
      a + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      b + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      c + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      d + l ∉ ({0, 1, 3, 9} : Finset (Fin 13))).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3771

theorem PEqualNP.Outside.L_meta_3771 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
    ∀ (x2 x3 : Finset (Fin (13 : ℕ))),
      (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) →
      x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro D X Y h
  by_cases hX : X.card ≤ 3
  · exact Or.inl hX
  right
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq
    (s := X) (n := 4) (Nat.succ_le_of_lt (Nat.lt_of_not_ge hX))
  let f := S.orderEmbOfFin hcard
  have hm : ∀ i, f i ∈ X := fun i => hS (S.orderEmbOfFin_mem hcard i)
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have hk := PEqualNP.Outside.L_meta_3771.four_points
    (f 0) (f 1) (f 2) (f 3) h01 h12 h23
  have hsub : Y ⊆ Finset.univ.filter fun l : Fin 13 =>
      f 0 + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      f 1 + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      f 2 + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      f 3 + l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h _ (hm 0) l hl, h _ (hm 1) l hl,
      h _ (hm 2) l hl, h _ (hm 3) l hl⟩
  exact (Finset.card_le_card hsub).trans hk
