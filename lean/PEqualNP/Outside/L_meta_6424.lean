import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6424

lemma quad : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter (fun y : Fin 13 =>
      (a.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (b.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      (c.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (d.val + y.val) % 13 ∉ [0, 1, 3, 9])).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_6424

theorem PEqualNP.Outside.L_meta_6424 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, (↑x3 + ↑x5) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro A B h
  by_contra hcon
  push_neg at hcon
  have h4 : 4 ≤ A.card := by omega
  have hmem : ∀ i : Fin 4, A.orderEmbOfCardLe h4 i ∈ A := fun i => Finset.orderEmbOfCardLe_mem A h4 i
  have hmono := (A.orderEmbOfCardLe h4).strictMono
  have hq := PEqualNP.Outside.L_meta_6424.quad (A.orderEmbOfCardLe h4 0) (A.orderEmbOfCardLe h4 1)
    (A.orderEmbOfCardLe h4 2) (A.orderEmbOfCardLe h4 3)
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
  have hsub : B ⊆ Finset.univ.filter (fun y : Fin 13 =>
      ((A.orderEmbOfCardLe h4 0).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 1).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 2).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 3).val + y.val) % 13 ∉ [0, 1, 3, 9]) := by
    intro y hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h _ (hmem 0) y hy, h _ (hmem 1) y hy, h _ (hmem 2) y hy,
      h _ (hmem 3) y hy⟩
  have := Finset.card_le_card hsub
  omega
