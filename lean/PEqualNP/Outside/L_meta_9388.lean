import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9388

def rows : List ℕ := [0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710]

def Z (i j : Fin 32) : Prop := (rows.getD i.val 0).testBit j.val = false

instance : DecidableRel Z := fun _ _ => inferInstanceAs (Decidable (_ = false))

theorem tS : ∀ i1 : Fin 32, i1 ≠ 0 → (Finset.univ.filter (fun j : Fin 32 => j ≠ 0 ∧ Z i1 j)).card ≤ 15 := by decide +kernel

theorem tP : ∀ i1 i2 : Fin 32, i1 ≠ 0 → i2 ≠ 0 → i1 ≠ i2 → (Finset.univ.filter (fun j : Fin 32 => j ≠ 0 ∧ Z i1 j ∧ Z i2 j)).card ≤ 7 := by decide +kernel

theorem tT : ∀ i1 i2 i3 : Fin 32, i1 ≠ 0 → i2 ≠ 0 → i3 ≠ 0 → i1 ≠ i2 → i3 ≠ i1 → i3 ≠ i2 → i3 ≠ i1 ^^^ i2 → (Finset.univ.filter (fun j : Fin 32 => j ≠ 0 ∧ Z i1 j ∧ Z i2 j ∧ Z i3 j)).card ≤ 3 := by decide +kernel

theorem tsym : ∀ i j : Fin 32, Z i j → Z j i := by decide +kernel

theorem tcnt : (Finset.univ.filter (fun p : Fin 32 × Fin 32 => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Z p.1 p.2)).card = 465 := by decide +kernel

theorem colb (R C : Finset (Fin 32)) (h : ∀ i ∈ R, ∀ j ∈ C, Z i j) :
    (1 ≤ (R.erase 0).card → (C.erase 0).card ≤ 15) ∧ (2 ≤ (R.erase 0).card → (C.erase 0).card ≤ 7) ∧ (4 ≤ (R.erase 0).card → (C.erase 0).card ≤ 3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    obtain ⟨i1, h1⟩ := Finset.card_pos.mp ha
    rw [Finset.mem_erase] at h1
    refine le_trans (Finset.card_le_card ?_) (tS i1 h1.1)
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj.1, h i1 h1.2 j hj.2⟩
  · intro ha
    obtain ⟨i1, h1, i2, h2, h12⟩ := Finset.one_lt_card.mp ha
    rw [Finset.mem_erase] at h1 h2
    refine le_trans (Finset.card_le_card ?_) (tP i1 i2 h1.1 h2.1 h12)
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj.1, h i1 h1.2 j hj.2, h i2 h2.2 j hj.2⟩
  · intro ha
    obtain ⟨i1, h1, i2, h2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (R.erase 0).card)
    have e1 := Finset.pred_card_le_card_erase (s := R.erase 0) (a := i1)
    have e2 := Finset.pred_card_le_card_erase (s := (R.erase 0).erase i1) (a := i2)
    have e3 := Finset.pred_card_le_card_erase (s := ((R.erase 0).erase i1).erase i2) (a := i1 ^^^ i2)
    obtain ⟨i3, h3⟩ := Finset.card_pos.mp (by omega : 0 < ((((R.erase 0).erase i1).erase i2).erase (i1 ^^^ i2)).card)
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at h3
    rw [Finset.mem_erase] at h1 h2
    refine le_trans (Finset.card_le_card ?_) (tT i1 i2 i3 h1.1 h2.1 h3.2.2.2.1 h12 h3.2.2.1 h3.2.1 h3.1)
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj.1, h i1 h1.2 j hj.2, h i2 h2.2 j hj.2, h i3 h3.2.2.2.2 j hj.2⟩

theorem rect (R C : Finset (Fin 32)) (h : ∀ i ∈ R, ∀ j ∈ C, Z i j) :
    (R.erase 0).card * (C.erase 0).card ≤ 21 := by
  obtain ⟨c1, c2, c4⟩ := colb R C h
  obtain ⟨r1, r2, r4⟩ := colb C R (fun j hj i hi => tsym i j (h i hi j hj))
  generalize (R.erase 0).card = a at *
  generalize (C.erase 0).card = b at *
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp
  by_cases ha4 : 4 ≤ a
  · have hb3 := c4 ha4
    by_cases hb2 : 2 ≤ b
    · exact le_trans (Nat.mul_le_mul (r2 hb2) hb3) (by norm_num)
    · have hb1 : b = 1 := by omega
      subst hb1
      have := r1 hb
      omega
  · by_cases ha2 : 2 ≤ a
    · exact le_trans (Nat.mul_le_mul (by omega : a ≤ 3) (c2 ha2)) (by norm_num)
    · have ha1 : a = 1 := by omega
      subst ha1
      have := c1 ha
      omega

theorem main (L : List (Finset (Fin 32) × Finset (Fin 32))) (hlen : L.length ≤ 17)
    (hz : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, Z i j)
    (hcov : ∀ (i : Fin 32) (j : Fin 32), Z i j → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  have hsub : (Finset.univ.filter (fun p : Fin 32 × Fin 32 => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Z p.1 p.2)) ⊆ L.toFinset.biUnion (fun r => (r.1.erase 0) ×ˢ (r.2.erase 0)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨r, hr, hi, hj⟩ := hcov p.1 p.2 hp.2.2
    rw [Finset.mem_biUnion]
    refine ⟨r, List.mem_toFinset.mpr hr, ?_⟩
    rw [Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
    exact ⟨⟨hp.1, hi⟩, ⟨hp.2.1, hj⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le_card_mul L.toFinset (fun r => (r.1.erase 0) ×ˢ (r.2.erase 0)) 21 (by
    intro r hr
    rw [Finset.card_product]
    exact rect r.1 r.2 (hz r (List.mem_toFinset.mp hr)))
  have h3 := L.toFinset_card_le
  rw [tcnt] at h1
  omega

end PEqualNP.Outside.L_meta_9388

theorem PEqualNP.Outside.L_meta_9388 : ¬ (∃ L : List (Finset (Fin 32) × Finset (Fin 32)), L.length ≤ 17 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 32) (j : Fin 32), (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  intro h
  obtain ⟨L, hlen, hz, hcov⟩ := h
  exact PEqualNP.Outside.L_meta_9388.main L hlen hz hcov
