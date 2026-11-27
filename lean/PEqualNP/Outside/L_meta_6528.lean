import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6528
open PEqualNP.CircuitLowerBounds



def gd (a e : ℕ) : Bool := decide ((a + e) % 13 ∉ [0, 1, 3, 9])

theorem chk : (List.range 13).all (fun a => (List.range 13).all fun b => (List.range 13).all fun c =>
    (List.range 13).all fun d =>
      (a == b || a == c || a == d || b == c || b == d || c == d) ||
      decide (((List.range 13).filter fun e => gd a e && gd b e && gd c e && gd d e).length ≤ 3)) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_6528

open PEqualNP.Outside.L_meta_6528 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6528 : ∀ (x1 : Finset (Fin (13 : ℕ))),   (4 : ℕ) ≤ x1.card →     have x3 : Finset (Fin (13 : ℕ)) := {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x1, (↑x4 + ↑x3) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]};     x3.card ≤ (3 : ℕ) := by
  intro X hX B
  classical
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
  have hsub : B.image Fin.val ⊆ ((List.range 13).filter fun e =>
      gd a e && gd b e && gd c e && gd d e).toFinset := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    have hB : ∀ x ∈ X, ((x : ℕ) + (e : ℕ)) % 13 ∉ [0, 1, 3, 9] := by
      have he' := he
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at he'
      exact he'
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨List.mem_range.2 e.isLt, ?_⟩
    simp only [gd, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hB a ha, hB b hb⟩, hB c hc⟩, hB d hd⟩
  have hk := chk
  simp only [List.all_eq_true, List.mem_range] at hk
  have hk' := hk a a.isLt b b.isLt c c.isLt d d.isLt
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hk'
  have hcard : B.card = (B.image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  rcases hk' with ((((((h | h) | h) | h) | h) | h) | h)
  · exact absurd (Fin.ext h) hab
  · exact absurd (Fin.ext h) hac
  · exact absurd (Fin.ext h) had
  · exact absurd (Fin.ext h) hbc
  · exact absurd (Fin.ext h) hbd
  · exact absurd (Fin.ext h) hcd
  · have h1 := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le ((List.range 13).filter fun e =>
      gd a e && gd b e && gd c e && gd d e)
    show B.card ≤ 3
    omega
