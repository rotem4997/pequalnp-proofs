import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2054_aux

theorem key : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter fun l : Fin 13 =>
      ¬ ((a : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((b : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧
      ¬ ((c : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((d : ℕ) + l) % 13 ∈ [0, 1, 3, 9]).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2054_aux

theorem PEqualNP.Outside.L_meta_2054 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro P X Y h
  by_contra hc
  push_neg at hc
  obtain ⟨X', hX', hc'⟩ := Finset.exists_subset_card_eq (s := X) (n := 4) (by omega)
  let f := X'.orderEmbOfFin hc'
  have hm : ∀ i, f i ∈ X := fun i => hX' (X'.orderEmbOfFin_mem hc' i)
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have hk := PEqualNP.Outside.L_meta_2054_aux.key _ _ _ _ h01 h12 h23
  have hsub : Y ⊆ Finset.univ.filter fun l : Fin 13 =>
      ¬ ((f 0 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((f 1 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧
      ¬ ((f 2 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((f 3 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h _ (hm 0) l hl, h _ (hm 1) l hl, h _ (hm 2) l hl, h _ (hm 3) l hl⟩
  have := Finset.card_le_card hsub
  omega
