import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9368

-- The matrix is the inner product mod 2 on 4 bits. Every all-0 rectangle covers at most
-- 9 of the 105 zero entries with both indices nonzero, and 11 * 9 < 105.

def rows : List ℕ := [0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260,
  39270, 4080, 42330, 49980, 27030]

def M (i j : Fin 16) : Bool := (rows.getD i.val 0).testBit j.val

theorem F1 : ∀ i : Fin 16, i ≠ 0 →
    (Finset.univ.filter (fun j : Fin 16 => j ≠ 0 ∧ M i j = false)).card ≤ 7 := by
  decide +kernel

theorem F2 : ∀ i1 i2 : Fin 16, i1 ≠ 0 → i2 ≠ 0 → i1 ≠ i2 →
    (Finset.univ.filter (fun j : Fin 16 => j ≠ 0 ∧ M i1 j = false ∧ M i2 j = false)).card ≤ 3 := by
  decide +kernel

theorem Msymm : ∀ i j : Fin 16, M i j = M j i := by
  decide +kernel

theorem Zcard : ((Finset.univ : Finset (Fin 16 × Fin 16)).filter
    (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ M p.1 p.2 = false)).card = 105 := by
  decide +kernel

theorem side (A B : Finset (Fin 16)) (h : ∀ i ∈ A, ∀ j ∈ B, M i j = false) :
    2 ≤ (A.filter (· ≠ 0)).card → (B.filter (· ≠ 0)).card ≤ 3 := by
  intro hA
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A.filter (· ≠ 0)).card)
  rw [Finset.mem_filter] at ha hb
  refine le_trans (Finset.card_le_card ?_) (F2 a b ha.2 hb.2 hab)
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ _, hj.2, h a ha.1 j hj.1, h b hb.1 j hj.1⟩

theorem side1 (A B : Finset (Fin 16)) (h : ∀ i ∈ A, ∀ j ∈ B, M i j = false) :
    1 ≤ (A.filter (· ≠ 0)).card → (B.filter (· ≠ 0)).card ≤ 7 := by
  intro hA
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (A.filter (· ≠ 0)).card)
  rw [Finset.mem_filter] at ha
  refine le_trans (Finset.card_le_card ?_) (F1 a ha.2)
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ _, hj.2, h a ha.1 j hj.1⟩

theorem rect (A B : Finset (Fin 16)) (h : ∀ i ∈ A, ∀ j ∈ B, M i j = false) :
    ((A ×ˢ B).filter (fun p : Fin 16 × Fin 16 => p.1 ≠ 0 ∧ p.2 ≠ 0)).card ≤ 9 := by
  have e : (A ×ˢ B).filter (fun p : Fin 16 × Fin 16 => p.1 ≠ 0 ∧ p.2 ≠ 0)
      = (A.filter (· ≠ 0)) ×ˢ (B.filter (· ≠ 0)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [e, Finset.card_product]
  have h' : ∀ j ∈ B, ∀ i ∈ A, M j i = false := fun j hj i hi => by
    rw [Msymm]; exact h i hi j hj
  have s1 := side A B h
  have s2 := side B A h'
  have s3 := side1 A B h
  have s4 := side1 B A h'
  generalize (A.filter (· ≠ 0)).card = a at *
  generalize (B.filter (· ≠ 0)).card = b at *
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · simp
    · have := s3 (by norm_num)
      omega
  · rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · simp
      · have := s4 (by norm_num)
        omega
    · have x1 := s1 ha
      have x2 := s2 hb
      exact le_trans (Nat.mul_le_mul x2 x1) (by norm_num)

theorem main (L : List (Finset (Fin 16) × Finset (Fin 16))) (hlen : L.length ≤ 11)
    (hz : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, M i j = false)
    (hc : ∀ (i : Fin 16) (j : Fin 16), M i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  have sub : (Finset.univ : Finset (Fin 16 × Fin 16)).filter
      (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ M p.1 p.2 = false) ⊆
      L.toFinset.biUnion (fun r => (r.1 ×ˢ r.2).filter
        (fun p : Fin 16 × Fin 16 => p.1 ≠ 0 ∧ p.2 ≠ 0)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨r, hr, h1, h2⟩ := hc p.1 p.2 hp.2.2.2
    rw [Finset.mem_biUnion]
    exact ⟨r, List.mem_toFinset.mpr hr,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hp.2.1, hp.2.2.1⟩⟩
  have c1 := Finset.card_le_card sub
  rw [Zcard] at c1
  have c2 := Finset.card_biUnion_le (s := L.toFinset) (t := fun r => (r.1 ×ˢ r.2).filter
        (fun p : Fin 16 × Fin 16 => p.1 ≠ 0 ∧ p.2 ≠ 0))
  have c3 : ∑ r ∈ L.toFinset, ((r.1 ×ˢ r.2).filter
        (fun p : Fin 16 × Fin 16 => p.1 ≠ 0 ∧ p.2 ≠ 0)).card ≤ ∑ _r ∈ L.toFinset, 9 :=
    Finset.sum_le_sum (fun r hr => rect r.1 r.2 (hz r (List.mem_toFinset.mp hr)))
  rw [Finset.sum_const, smul_eq_mul] at c3
  have c4 := List.toFinset_card_le L
  omega

end PEqualNP.Outside.L_meta_9368

theorem PEqualNP.Outside.L_meta_9368 : ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 16)), L.length ≤ 11 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 16), (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hz, hc⟩
  exact PEqualNP.Outside.L_meta_9368.main L hlen hz hc
