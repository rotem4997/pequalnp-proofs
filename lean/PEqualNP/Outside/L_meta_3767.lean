import Mathlib
import PEqualNP.Defs

-- Points and lines with q + 1 points on every line and a unique line through two
-- distinct points: a cover inside the stated set A is all of A.
namespace PEqualNP.Outside.L_meta_3767

-- A line outside a set T of at most q lines has a point on no line of T:
-- each line of T shares at most one point with it.
theorem exists_uncovered {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (T : Finset (Fin N)) (hT : T.card ≤ q) (l : Fin N) (hl : l ∉ T) :
    ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k := by
  by_contra hcon
  have hcov : ∀ p : Fin N, I p l → ∃ k ∈ T, I p k := by
    intro p hp
    by_contra hno
    exact hcon ⟨p, hp, fun k hk hpk => hno ⟨k, hk, hpk⟩⟩
  have h1 : (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
    rw [← Fintype.card_subtype]
    exact hcard l
  have h2 : Finset.univ.filter (fun p : Fin N => I p l)
      ⊆ T.biUnion (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨k, hk, hpk⟩ := hcov p hp.2
    rw [Finset.mem_biUnion]
    exact ⟨k, hk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2, hpk⟩⟩
  have h3 : ∀ k ∈ T, (Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)).card ≤ 1 := by
    intro k hk
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    obtain ⟨l0, _, hl0⟩ := huniq a b hab
    have e1 : l = l0 := hl0 l ⟨ha.2.1, hb.2.1⟩
    have e2 : k = l0 := hl0 k ⟨ha.2.2, hb.2.2⟩
    exact hl (by rw [e1, ← e2]; exact hk)
  have h4 := Finset.card_le_card h2
  have h5 := Finset.card_biUnion_le_card_mul T
    (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) 1 h3
  omega

end PEqualNP.Outside.L_meta_3767

theorem PEqualNP.Outside.L_meta_3767 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)) (x8 x9 : Finset ℕ), x7.card ≤ x1 → x9 ⊆ x8 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → ↑x12 ∈ x9 ∨ x2 + ↑x13 ∈ x9) → (∀ (x13 : Fin x2), (↑x13 ∈ x8 ↔ ∃ x14 ∈ x7, x3 x13 x14) ∧ (x2 + ↑x13 ∈ x8 ↔ x13 ∉ x7)) → ∀ (x14 : Fin x2), (↑x14 ∈ x9 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ (x2 + ↑x14 ∈ x9 ↔ x14 ∉ x7) := by
  intro q N I instI hcard huniq T A B hT hBA hcov hA p
  refine ⟨⟨fun hpB => (hA p).1.mp (hBA hpB), ?_⟩, ⟨fun hB => (hA p).2.mp (hBA hB), ?_⟩⟩
  · intro hex
    obtain ⟨l, hlT, hpl⟩ := hex
    rcases hcov p l hpl with h | h
    · exact h
    · exact absurd hlT ((hA l).2.mp (hBA h))
  · intro hpT
    obtain ⟨p0, hp0, hno⟩ :=
      PEqualNP.Outside.L_meta_3767.exists_uncovered I hcard huniq T hT p hpT
    rcases hcov p0 p hp0 with h | h
    · exfalso
      obtain ⟨k, hk, hIk⟩ := (hA p0).1.mp (hBA h)
      exact hno k hk hIk
    · exact h
