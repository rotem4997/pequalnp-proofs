import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7873
open PEqualNP.CircuitLowerBounds



set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (Finset.univ.filter fun e : Fin 13 =>
      ¬(a + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(b + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(c + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(d + e ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_7873

open PEqualNP.Outside.L_meta_7873 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7873 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : Finset (Fin (13 : ℕ))),   x2.card = (4 : ℕ) →     have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x2, x5 + x4 ∉ x1};     x4.card ≤ (3 : ℕ) := by
  intro D X hX B
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
  have hsub : B ⊆ Finset.univ.filter fun e : Fin 13 =>
      ¬(a + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(b + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(c + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧ ¬(d + e ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by
    intro e he
    have he' : ∀ x ∈ X, x + e ∉ D := by simpa [B] using he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he' a ha, he' b hb, he' c hc, he' d hd⟩
  have h1 := Finset.card_le_card hsub
  have h2 := key a b c d hab hac had hbc hbd hcd
  show B.card ≤ 3
  omega
