import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7473
open PEqualNP.CircuitLowerBounds



set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (Finset.univ.filter fun e : Fin 13 =>
      ¬((a.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((b.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((c.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((d.val + e.val) % 13 ∈ [0, 1, 3, 9])).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_7473

open PEqualNP.Outside.L_meta_7473 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7473 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => Fin.castAdd (13 : ℕ) x2; have x3 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x3 : Fin (13 : ℕ)) => Fin.natAdd (13 : ℕ) x3; have x4 : (Fin (13 : ℕ) → Fin (26 : ℕ)) → Finset (Fin (26 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Fin (13 : ℕ) → Fin (26 : ℕ)) (x5 : Finset (Fin (26 : ℕ))) => {x6 : Fin (13 : ℕ) | x4 x6 ∉ x5}; have x5 : Finset (Fin (26 : ℕ)) → Prop := fun (x5 : Finset (Fin (26 : ℕ))) => ∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x6 ∈ x5 ∨ x3 x7 ∈ x5; ∀ (x6 : Finset (Fin (26 : ℕ))), x5 x6 → (x4 x2 x6).card ≤ (3 : ℕ) ∨ (x4 x3 x6).card ≤ (3 : ℕ) := by
  intro inc pt ln cmp cov S hS
  have h : ∀ a ∈ cmp pt S, ∀ e ∈ cmp ln S, ¬((a.val + e.val) % 13 ∈ [0, 1, 3, 9]) := by
    intro a ha e he hinc
    have ha' : pt a ∉ S := by simpa [cmp] using ha
    have he' : ln e ∉ S := by simpa [cmp] using he
    rcases hS a e hinc with h1 | h1
    · exact ha' h1
    · exact he' h1
  generalize cmp pt S = X at h ⊢
  generalize cmp ln S = Y at h ⊢
  by_contra hc
  push_neg at hc
  obtain ⟨hX, hY⟩ := hc
  have h4 : ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, ∃ d ∈ X, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < X.card)
    have c1 : (X.erase a).card = X.card - 1 := Finset.card_erase_of_mem ha
    obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < (X.erase a).card)
    have c2 : ((X.erase a).erase b).card = (X.erase a).card - 1 := Finset.card_erase_of_mem hb
    obtain ⟨c, hc⟩ := Finset.card_pos.1 (by omega : 0 < ((X.erase a).erase b).card)
    have c3 : (((X.erase a).erase b).erase c).card = ((X.erase a).erase b).card - 1 :=
      Finset.card_erase_of_mem hc
    obtain ⟨d, hd⟩ := Finset.card_pos.1 (by omega : 0 < (((X.erase a).erase b).erase c).card)
    simp only [Finset.mem_erase] at hb hc hd
    exact ⟨a, ha, b, hb.2, c, hc.2.2, d, hd.2.2.2, fun h => hb.1 h.symm, fun h => hc.2.1 h.symm,
      fun h => hd.2.2.1 h.symm, fun h => hc.1 h.symm, fun h => hd.2.1 h.symm, fun h => hd.1 h.symm⟩
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ := h4
  have hsub : Y ⊆ Finset.univ.filter fun e : Fin 13 =>
      ¬((a.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((b.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((c.val + e.val) % 13 ∈ [0, 1, 3, 9]) ∧ ¬((d.val + e.val) % 13 ∈ [0, 1, 3, 9]) := by
    intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h a ha e he, h b hb e he, h c hc e he, h d hd e he⟩
  have h1 := Finset.card_le_card hsub
  have h2 := key a b c d hab hac had hbc hbd hcd
  omega
