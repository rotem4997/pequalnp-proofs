import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9395

-- The matrix is the inner product modulo two on five bits. An all-0 rectangle with sides A and B has at most 32
-- entries (row orthogonality and a sum of squares), so it covers at most 21 of the 465 zero entries outside row 0 and column 0.

def z (i j : Fin 32) : Bool :=
  (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val

def s (i j : Fin 32) : ℤ := if z i j = true then -1 else 1

set_option maxRecDepth 100000 in
lemma diag : ∀ a : Fin 32, ∑ y, s a y * s a y = 32 := by decide +kernel

set_option maxRecDepth 100000 in
lemma orth : ∀ a b : Fin 32, a ≠ b → ∑ y, s a y * s b y = 0 := by decide +kernel

lemma row0 : ∀ j : Fin 32, z 0 j = false := by decide +kernel

lemma col0 : ∀ i : Fin 32, z i 0 = false := by decide +kernel

lemma lind (A B : Finset (Fin 32)) (h : ∀ i ∈ A, ∀ j ∈ B, z i j = false) : A.card * B.card ≤ 32 := by
  have h1 : ∑ y, (∑ a ∈ A, s a y) ^ 2 = 32 * (A.card : ℤ) := by
    have e : ∀ y, (∑ a ∈ A, s a y) ^ 2 = ∑ a ∈ A, ∑ b ∈ A, s a y * s b y := fun y => by
      rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
    have e2 : ∀ a ∈ A, ∑ y, ∑ b ∈ A, s a y * s b y = 32 := fun a ha => by
      rw [Finset.sum_comm, Finset.sum_eq_single a]
      · exact diag a
      · intro b _ hb
        exact orth a b (Ne.symm hb)
      · intro hn
        exact absurd ha hn
    rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h2 : (B.card : ℤ) * (A.card : ℤ) ^ 2 ≤ ∑ y, (∑ a ∈ A, s a y) ^ 2 := by
    have e : ∑ y ∈ B, (∑ a ∈ A, s a y) ^ 2 = (B.card : ℤ) * (A.card : ℤ) ^ 2 := by
      have e1 : ∀ y ∈ B, (∑ a ∈ A, s a y) ^ 2 = (A.card : ℤ) ^ 2 := fun y hy => by
        have e0 : ∑ a ∈ A, s a y = (A.card : ℤ) := by
          rw [Finset.sum_congr rfl (fun a ha => show s a y = 1 by simp [s, h a ha y hy])]
          simp
        rw [e0]
      rw [Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]
    rw [← e]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun _ _ _ => sq_nonneg _)
  rcases Nat.eq_zero_or_pos A.card with h0 | h0
  · rw [h0]
    simp
  · have h3 : (B.card : ℤ) * (A.card : ℤ) ^ 2 ≤ 32 * (A.card : ℤ) := h1 ▸ h2
    have h4 : B.card * A.card ^ 2 ≤ 32 * A.card := by exact_mod_cast h3
    have h5 : A.card * B.card * A.card ≤ 32 * A.card := by
      calc A.card * B.card * A.card = B.card * A.card ^ 2 := by ring
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_right h5 h0

lemma small (a b : ℕ) (h : (a + 1) * (b + 1) ≤ 32) : a * b ≤ 21 := by
  have ha : a ≤ 31 := by nlinarith
  interval_cases a <;> omega

lemma rect (r : Finset (Fin 32) × Finset (Fin 32)) (h : ∀ i ∈ r.1, ∀ j ∈ r.2, z i j = false) :
    ((r.1.erase 0) ×ˢ (r.2.erase 0)).card ≤ 21 := by
  rw [Finset.card_product]
  apply small
  have ha : (insert 0 (r.1.erase 0)).card = (r.1.erase 0).card + 1 :=
    Finset.card_insert_of_notMem (Finset.notMem_erase 0 r.1)
  have hb : (insert 0 (r.2.erase 0)).card = (r.2.erase 0).card + 1 :=
    Finset.card_insert_of_notMem (Finset.notMem_erase 0 r.2)
  rw [← ha, ← hb]
  apply lind
  intro i hi j hj
  rcases Finset.mem_insert.1 hi with rfl | hi
  · exact row0 j
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact col0 i
  exact h i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)

def P : Finset (Fin 32 × Fin 32) := Finset.univ.filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ z p.1 p.2 = false)

set_option maxRecDepth 100000 in
lemma cardP : P.card = 465 := by decide +kernel

lemma main (L : List (Finset (Fin 32) × Finset (Fin 32))) (hl : L.length ≤ 21)
    (hz : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, z i j = false)
    (hc : ∀ i j : Fin 32, z i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  have hsub : P ⊆ L.toFinset.biUnion (fun r => (r.1.erase 0) ×ˢ (r.2.erase 0)) := by
    intro p hp
    obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.1 hp
    obtain ⟨r, hr, hi, hj⟩ := hc p.1 p.2 h3
    refine Finset.mem_biUnion.2 ⟨r, List.mem_toFinset.2 hr, Finset.mem_product.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_erase.2 ⟨h1, hi⟩
    · exact Finset.mem_erase.2 ⟨h2, hj⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (L.toFinset.biUnion (fun r => (r.1.erase 0) ×ˢ (r.2.erase 0))).card ≤ L.toFinset.card * 21 :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun r hr => rect r (hz r (List.mem_toFinset.1 hr)))
  have h3 : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  rw [cardP] at h1
  omega

end PEqualNP.Outside.L_meta_9395

theorem PEqualNP.Outside.L_meta_9395 : ¬ (∃ L : List (Finset (Fin 32) × Finset (Fin 32)), L.length ≤ 21 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 32) (j : Fin 32), (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hl, hz, hc⟩
  exact PEqualNP.Outside.L_meta_9395.main L hl hz hc
