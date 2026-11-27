import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8051_aux

def pts (l : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter (fun p : Fin 21 => (l.val + 21 - p.val) % 21 ∈ [0, 5, 7, 17, 20])

theorem pts_card : ∀ l : Fin 21, (pts l).card = 5 := by
  unfold pts; decide +kernel

theorem pts_inter : ∀ i j : Fin 21, i ≠ j → (pts i ∩ pts j).card ≤ 1 := by
  unfold pts; decide +kernel

theorem union_ge : ∀ S : Finset (Fin 21),
    10 * S.card ≤ 2 * (S.biUnion pts).card + S.card * (S.card - 1) := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha, Finset.biUnion_insert]
    have h1 : (pts a ∩ S.biUnion pts).card ≤ S.card := by
      have : pts a ∩ S.biUnion pts = S.biUnion (fun s => pts a ∩ pts s) := by
        ext x; simp only [Finset.mem_inter, Finset.mem_biUnion]
        constructor
        · rintro ⟨h, s, hs, h'⟩; exact ⟨s, hs, h, h'⟩
        · rintro ⟨s, hs, h, h'⟩; exact ⟨h, s, hs, h'⟩
      rw [this]
      calc _ ≤ S.card * 1 := Finset.card_biUnion_le_card_mul _ _ 1 (fun s hs => pts_inter a s (by
              rintro rfl; exact ha hs))
        _ = S.card := by ring
    have h2 := Finset.card_union_add_card_inter (pts a) (S.biUnion pts)
    have h3 := pts_card a
    have h4 : 5 ≤ (pts a ∪ S.biUnion pts).card + 0 := by
      have := Finset.card_le_card (Finset.subset_union_left (s₁ := pts a) (s₂ := S.biUnion pts))
      omega
    have e : (S.card + 1) * (S.card + 1 - 1) = S.card * (S.card - 1) + 2 * S.card := by
      cases S.card with
      | zero => simp
      | succ m => simp; ring
    rw [e]
    nlinarith [h1, h2, h3, ih]

end PEqualNP.Outside.L_meta_8051_aux

theorem PEqualNP.Outside.L_meta_8051 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), x1 x3 x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => List.countP (fun (x4 : Fin (21 : ℕ)) => x3 (Fin.castAdd (21 : ℕ) x4)) (List.finRange (21 : ℕ)) ≤ (6 : ℕ) ∨ List.countP (fun (x4 : Fin (21 : ℕ)) => x3 (Fin.natAdd (21 : ℕ) x4)) (List.finRange (21 : ℕ)) ≤ (5 : ℕ); ∀ (x4 : Fin (42 : ℕ) → Bool), ¬x2 x4 → x3 x4 := by
  dsimp only
  intro x4 hn
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hP, hL⟩ := hcon
  have cP : List.countP (fun (x : Fin 21) => x4 (Fin.castAdd 21 x)) (List.finRange 21)
      = (Finset.univ.filter (fun p : Fin 21 => x4 (Fin.castAdd 21 p) = true)).card := by
    simp [Fin.univ_def, Finset.card, Finset.filter_val, List.countP_eq_length_filter]
  have cL : List.countP (fun (x : Fin 21) => x4 (Fin.natAdd 21 x)) (List.finRange 21)
      = (Finset.univ.filter (fun p : Fin 21 => x4 (Fin.natAdd 21 p) = true)).card := by
    simp [Fin.univ_def, Finset.card, Finset.filter_val, List.countP_eq_length_filter]
  rw [cP] at hP
  rw [cL] at hL
  push_neg at hP hL
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show 6 ≤ _ by omega : 6 ≤ (Finset.univ.filter (fun p : Fin 21 => x4 (Fin.natAdd 21 p) = true)).card)
  have hU := PEqualNP.Outside.L_meta_8051_aux.union_ge S
  rw [hSc] at hU
  have hdisj : Disjoint (Finset.univ.filter (fun p : Fin 21 => x4 (Fin.castAdd 21 p) = true))
      (S.biUnion PEqualNP.Outside.L_meta_8051_aux.pts) := by
    rw [Finset.disjoint_left]
    intro p hp hp2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Finset.mem_biUnion] at hp2
    obtain ⟨l, hl, hpl⟩ := hp2
    have hl2 := hS hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl2
    simp only [PEqualNP.Outside.L_meta_8051_aux.pts, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    apply hn
    refine ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, ⟨?_, ?_, ?_⟩, hp, hl2⟩
    · simp
    · simp
    · simp only [Fin.coe_castAdd, Fin.coe_natAdd]
      have : (21 + (l : ℕ) + 21 - (p : ℕ)) % 21 = ((l : ℕ) + 21 - (p : ℕ)) % 21 := by
        have hp21 := p.isLt
        omega
      rw [this]; exact hpl
  have hcard := Finset.card_le_univ (Finset.univ.filter (fun p : Fin 21 => x4 (Fin.castAdd 21 p) = true) ∪ S.biUnion PEqualNP.Outside.L_meta_8051_aux.pts)
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  simp only [Fintype.card_fin] at hcard
  omega
