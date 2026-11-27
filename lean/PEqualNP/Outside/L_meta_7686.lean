import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7686
open PEqualNP.CircuitLowerBounds



theorem half {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (k : ℕ) (A B : Finset (Fin n))
    (hC : ∀ a a' b b' : Fin n, R a b → R a b' → R a' b → R a' b' → a = a' ∨ b = b')
    (a0 : Fin n) (ha0 : a0 ∈ A) (hA : k < (B.filter fun b => R a0 b).card)
    (hB : ∀ b ∈ B, k < (A.filter fun a => R a b).card) : k * (k + 1) < A.card := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (show k + 1 ≤ (B.filter fun b => R a0 b).card from hA)
  have hTm : ∀ b ∈ T, b ∈ B ∧ R a0 b := fun b hb => by simpa using hT hb
  have hdisj : ∀ b ∈ T, ∀ b' ∈ T, b ≠ b' →
      Disjoint ((A.filter fun a => R a b).erase a0) ((A.filter fun a => R a b').erase a0) := by
    intro b hb b' hb' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hxa, hx1⟩ := Finset.mem_erase.1 hx
    obtain ⟨_, hx2⟩ := Finset.mem_erase.1 hx'
    have r1 := (Finset.mem_filter.1 hx1).2
    have r2 := (Finset.mem_filter.1 hx2).2
    rcases hC a0 x b b' (hTm b hb).2 (hTm b' hb').2 r1 r2 with h | h
    · exact hxa h.symm
    · exact hne h
  have hc := Finset.card_biUnion hdisj
  have hs : ∀ b ∈ T, k ≤ ((A.filter fun a => R a b).erase a0).card := by
    intro b hb
    have hmem : a0 ∈ A.filter fun a => R a b := Finset.mem_filter.2 ⟨ha0, (hTm b hb).2⟩
    rw [Finset.card_erase_of_mem hmem]
    have := hB b (hTm b hb).1
    omega
  have hsum : T.card * k ≤ ∑ b ∈ T, ((A.filter fun a => R a b).erase a0).card := by
    have h := Finset.card_nsmul_le_sum T _ k hs
    simpa using h
  have hsub : (T.biUnion fun b => (A.filter fun a => R a b).erase a0) ⊆ A.erase a0 := by
    intro x hx
    obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨hxa, hx1⟩ := Finset.mem_erase.1 hxb
    exact Finset.mem_erase.2 ⟨hxa, (Finset.mem_filter.1 hx1).1⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ha0, hc] at h1
  rw [hTc] at hsum
  have hpos := Finset.card_pos.2 ⟨a0, ha0⟩
  have e : (k + 1) * k = k * (k + 1) := Nat.mul_comm _ _
  omega

end PEqualNP.Outside.L_meta_7686

open PEqualNP.Outside.L_meta_7686 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7686 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)) (x4 x5 : Finset (Fin x1)), (∀ (x6 x7 x8 x9 : Fin x1), (x6, x8) ∈ x3 → (x6, x9) ∈ x3 → (x7, x8) ∈ x3 → (x7, x9) ∈ x3 → x6 = x7 ∨ x8 = x9) → x4.Nonempty → x5.Nonempty → (∀ x9 ∈ x4, x2 < {x11 ∈ x5 | (x9, x11) ∈ x3}.card) → (∀ x10 ∈ x5, x2 < {x12 ∈ x4 | (x12, x10) ∈ x3}.card) → x2 * (x2 + (1 : ℕ)) < x4.card ∧ x2 * (x2 + (1 : ℕ)) < x5.card ∧ (x2 + (1 : ℕ)) * (x2 * (x2 + (1 : ℕ)) + (1 : ℕ)) ≤ {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5}.card := by
  intro n k E A B hC hAne hBne hA hB
  classical
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  have h1 : k * (k + 1) < A.card :=
    half (fun a b => (a, b) ∈ E) k A B hC a0 ha0 (hA a0 ha0) hB
  have h2 : k * (k + 1) < B.card :=
    half (fun b a => (a, b) ∈ E) k B A
      (fun b b' a a' r1 r2 r3 r4 => (hC a a' b b' r1 r3 r2 r4).symm) b0 hb0 (hB b0 hb0) hA
  refine ⟨h1, h2, ?_⟩
  have hdisj : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      Disjoint ((B.filter fun b => (a, b) ∈ E).image fun b => (a, b))
        ((B.filter fun b => (a', b) ∈ E).image fun b => (a', b)) := by
    intro a _ a' _ hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b', _, hbb⟩ := Finset.mem_image.1 hp'
    exact hne (congrArg Prod.fst hbb).symm
  have hc := Finset.card_biUnion hdisj
  have hsub : (A.biUnion fun a => (B.filter fun b => (a, b) ∈ E).image fun b => (a, b))
      ⊆ E.filter fun e => e.1 ∈ A ∧ e.2 ∈ B := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hpa
    obtain ⟨hbB, hbE⟩ := Finset.mem_filter.1 hb
    exact Finset.mem_filter.2 ⟨hbE, ha, hbB⟩
  have h3 := Finset.card_le_card hsub
  rw [hc] at h3
  have hs : ∀ a ∈ A, k + 1 ≤ ((B.filter fun b => (a, b) ∈ E).image fun b => (a, b)).card := by
    intro a ha
    rw [Finset.card_image_of_injective _ (fun b b' h => (Prod.mk.inj h).2)]
    exact hA a ha
  have hsum := Finset.card_nsmul_le_sum A _ (k + 1) hs
  have h4 : (k + 1) * (k * (k + 1) + 1) ≤ A.card * (k + 1) := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ h1
  have h5 : A.card * (k + 1) ≤ ∑ a ∈ A, ((B.filter fun b => (a, b) ∈ E).image fun b => (a, b)).card := by
    simpa using hsum
  exact le_trans h4 (le_trans h5 h3)
