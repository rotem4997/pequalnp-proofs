import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6750 : ∀ (x1 : Finset (Sym2 (Fin (11 : ℕ)))) (x2 : Finset ℕ) (x3 : ℕ → Finset (Sym2 (Fin (11 : ℕ)))), ∃ x4 ⊆ x1, (x1 \ x4).card ≤ {x5 ∈ x2 | Disjoint x4 (x3 x5)}.card ∧ ∀ x5 ∈ x2, (x4 ∩ x3 x5).card ≠ (1 : ℕ) := by
  intro E I S
  classical
  have key : ∀ k (X : Finset (Sym2 (Fin 11))), X.card = k → X ⊆ E →
      (E \ X).card ≤ (I.filter fun i => Disjoint X (S i)).card →
      ∃ X' ⊆ E, (E \ X').card ≤ (I.filter fun i => Disjoint X' (S i)).card ∧
        ∀ i ∈ I, (X' ∩ S i).card ≠ 1 := by
    intro k
    induction k with
    | zero =>
      intro X hk hX hinv
      refine ⟨X, hX, hinv, fun i _ => ?_⟩
      rw [Finset.card_eq_zero.1 hk]
      simp
    | succ k ih =>
      intro X hk hX hinv
      by_cases hall : ∀ i ∈ I, (X ∩ S i).card ≠ 1
      · exact ⟨X, hX, hinv, hall⟩
      · push_neg at hall
        obtain ⟨i0, hi0, hc⟩ := hall
        obtain ⟨e, he⟩ := Finset.card_eq_one.1 hc
        have hmem : e ∈ X ∩ S i0 := by rw [he]; exact Finset.mem_singleton_self e
        have heX : e ∈ X := (Finset.mem_inter.1 hmem).1
        have heS : e ∈ S i0 := (Finset.mem_inter.1 hmem).2
        apply ih (X.erase e) (by rw [Finset.card_erase_of_mem heX, hk]; rfl)
          ((Finset.erase_subset _ _).trans hX)
        have h1 : E \ X.erase e = insert e (E \ X) := by
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨haE, hna⟩
            by_cases hae : a = e
            · exact Or.inl hae
            · exact Or.inr ⟨haE, fun h => hna ⟨hae, h⟩⟩
          · rintro (hae | ⟨haE, hna⟩)
            · rw [hae]; exact ⟨hX heX, fun h => h.1 rfl⟩
            · exact ⟨haE, fun h => hna h.2⟩
        have h2 : (insert e (E \ X)).card = (E \ X).card + 1 :=
          Finset.card_insert_of_notMem (by simp [heX])
        have h3 : insert i0 (I.filter fun i => Disjoint X (S i))
            ⊆ I.filter fun i => Disjoint (X.erase e) (S i) := by
          intro i hi
          rcases Finset.mem_insert.1 hi with hii | hi
          · rw [hii]
            refine Finset.mem_filter.2 ⟨hi0, ?_⟩
            rw [Finset.disjoint_left]
            intro a ha haS
            have h6 : a ∈ X ∩ S i0 := Finset.mem_inter.2 ⟨(Finset.mem_erase.1 ha).2, haS⟩
            rw [he, Finset.mem_singleton] at h6
            exact (Finset.mem_erase.1 ha).1 h6
          · obtain ⟨hiI, hd⟩ := Finset.mem_filter.1 hi
            exact Finset.mem_filter.2 ⟨hiI, hd.mono_left (Finset.erase_subset _ _)⟩
        have h4 : i0 ∉ I.filter fun i => Disjoint X (S i) := by
          intro h
          exact (Finset.disjoint_left.1 (Finset.mem_filter.1 h).2 heX) heS
        have h5 := Finset.card_le_card h3
        rw [Finset.card_insert_of_notMem h4] at h5
        rw [h1, h2]
        omega
  exact key E.card E rfl (Finset.Subset.refl _) (by simp)
