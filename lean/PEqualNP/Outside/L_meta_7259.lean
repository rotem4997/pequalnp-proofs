import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7259
open PEqualNP.CircuitLowerBounds



set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (Finset.univ.filter fun e : Fin 13 =>
      ¬(a = e ∨ a = e + 1 ∨ a = e + 3 ∨ a = e + 9) ∧ ¬(b = e ∨ b = e + 1 ∨ b = e + 3 ∨ b = e + 9) ∧
      ¬(c = e ∨ c = e + 1 ∨ c = e + 3 ∨ c = e + 9) ∧ ¬(d = e ∨ d = e + 1 ∨ d = e + 3 ∨ d = e + 9)).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_7259

open PEqualNP.Outside.L_meta_7259 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7259 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, ¬(x3 = x5 ∨ x3 = x5 + (1 : Fin (13 : ℕ)) ∨ x3 = x5 + (3 : Fin (13 : ℕ)) ∨ x3 = x5 + (9 : Fin (13 : ℕ)))) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro X Y h
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
      ¬(a = e ∨ a = e + 1 ∨ a = e + 3 ∨ a = e + 9) ∧ ¬(b = e ∨ b = e + 1 ∨ b = e + 3 ∨ b = e + 9) ∧
      ¬(c = e ∨ c = e + 1 ∨ c = e + 3 ∨ c = e + 9) ∧ ¬(d = e ∨ d = e + 1 ∨ d = e + 3 ∨ d = e + 9) := by
    intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h a ha e he, h b hb e he, h c hc e he, h d hd e he⟩
  have h1 := Finset.card_le_card hsub
  have h2 := key a b c d hab hac had hbc hbd hcd
  omega
