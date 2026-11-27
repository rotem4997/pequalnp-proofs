import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5815 : ∀ (x1 : ℕ) (x2 x3 x4 : Finset (Finset (Fin x1))) (x5 x6 : Set (Fin x1)),   have x7 : Finset (Finset (Fin x1)) → Prop := fun (x7 : Finset (Finset (Fin x1))) => (∀ x8 ∈ x7, ∃ x10 ∈ x8, x10 ∈ x5) ∧ ∃ x8 ∈ x7, ∀ x9 ∈ x8, x9 ∈ x6;   (x4 = x2 ∪ x3 ∨ x4 = x2.biUnion fun (x8 : Finset (Fin x1)) => Finset.image (fun (x9 : Finset (Fin x1)) => x8 ∪ x9) x3) → x7 x4 → x7 x2 ∨ x7 x3 := by
  classical
  intro n A B X P Q
  intro S hX hS
  obtain ⟨hall, c, hc, hcQ⟩ := hS
  rcases hX with rfl | rfl
  · rcases Finset.mem_union.mp hc with h | h
    · exact Or.inl ⟨fun a ha => hall a (Finset.mem_union_left _ ha), c, h, hcQ⟩
    · exact Or.inr ⟨fun a ha => hall a (Finset.mem_union_right _ ha), c, h, hcQ⟩
  · rw [Finset.mem_biUnion] at hc
    obtain ⟨a, ha, hc⟩ := hc
    rw [Finset.mem_image] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    have haQ : ∀ i ∈ a, i ∈ Q := fun i hi => hcQ i (Finset.mem_union_left _ hi)
    have hbQ : ∀ i ∈ b, i ∈ Q := fun i hi => hcQ i (Finset.mem_union_right _ hi)
    by_cases hA : ∀ a' ∈ A, ∃ i ∈ a', i ∈ P
    · exact Or.inl ⟨hA, a, ha, haQ⟩
    · refine Or.inr ⟨fun b' hb' => ?_, b, hb, hbQ⟩
      push_neg at hA
      obtain ⟨a', ha', hmiss⟩ := hA
      have hmem : a' ∪ b' ∈ A.biUnion fun (x8 : Finset (Fin n)) =>
          Finset.image (fun (x9 : Finset (Fin n)) => x8 ∪ x9) B := by
        rw [Finset.mem_biUnion]
        exact ⟨a', ha', Finset.mem_image.mpr ⟨b', hb', rfl⟩⟩
      obtain ⟨i, hi, hiP⟩ := hall _ hmem
      rcases Finset.mem_union.mp hi with h | h
      · exact absurd hiP (hmiss i h)
      · exact ⟨i, h, hiP⟩
