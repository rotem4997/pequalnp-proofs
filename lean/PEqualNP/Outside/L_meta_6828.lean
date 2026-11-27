import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6828 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Fin x1 → Fin x1 → Prop), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 x8 : Fin x1), x4 x7 x8 → x2.Adj x7 x8) → ((∃ (x8 : Fin x1) (x9 : Fin x1), x4 x8 x9 ∧ ∀ (x10 x11 : Fin x1), x4 x10 x11 → x10 = x8 ∨ x11 = x8 ∨ x10 = x9 ∨ x11 = x9) ∨ ∃ (x8 : Fin x1) (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x4 x8 x9 ∧ x4 x9 x10 ∧ x4 x10 x11 ∧ x4 x11 x12 ∧ x4 x12 x8) → (∃ (x9 : Fin x1), ∀ (x10 x11 : Fin x1), x4 x10 x11 → x10 = x9 ∨ x11 = x9) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), (x4 x9 x10 ∨ x4 x10 x9) ∧ x4 x10 x11 ∧ (x4 x11 x12 ∨ x4 x12 x11) ∧ ¬x2.Adj x9 x11 ∧ ¬x2.Adj x10 x12 ∧ ¬x2.Adj x9 x12 := by
  intro n G _ R htri h4 hsub hcase
  unfold PEqualNP.TopForm.NoFourCycle at h4
  rcases hcase with ⟨a, b, hab, hcov⟩ | ⟨v0, v1, v2, v3, v4, h01, h12, h23, h34, h40⟩
  · by_cases hA : ∀ u v, R u v → u = a ∨ v = a
    · exact Or.inl ⟨a, hA⟩
    by_cases hB : ∀ u v, R u v → u = b ∨ v = b
    · exact Or.inl ⟨b, hB⟩
    push_neg at hA hB
    obtain ⟨u1, w1, r1, hu1, hw1⟩ := hB
    obtain ⟨u2, w2, r2, hu2, hw2⟩ := hA
    have hcex : ∃ c, (R c a ∨ R a c) ∧ c ≠ b := by
      rcases hcov u1 w1 r1 with h | h | h | h
      · subst h; exact ⟨w1, Or.inr r1, hw1⟩
      · subst h; exact ⟨u1, Or.inl r1, hu1⟩
      · exact absurd h hu1
      · exact absurd h hw1
    have hdex : ∃ d, (R b d ∨ R d b) ∧ d ≠ a := by
      rcases hcov u2 w2 r2 with h | h | h | h
      · exact absurd h hu2
      · exact absurd h hw2
      · subst h; exact ⟨w2, Or.inl r2, hw2⟩
      · subst h; exact ⟨u2, Or.inr r2, hu2⟩
    obtain ⟨c, hc, hcb⟩ := hcex
    obtain ⟨d, hd, hda⟩ := hdex
    have hca : G.Adj c a := by
      rcases hc with h | h
      · exact hsub _ _ h
      · exact G.adj_symm (hsub _ _ h)
    have hbd : G.Adj b d := by
      rcases hd with h | h
      · exact hsub _ _ h
      · exact G.adj_symm (hsub _ _ h)
    have hab' : G.Adj a b := hsub _ _ hab
    refine Or.inr ⟨c, a, b, d, ?_, hab, hd, ?_, ?_, ?_⟩
    · rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro h; exact htri c a b hca hab' (G.adj_symm h)
    · intro h; exact htri a b d hab' hbd (G.adj_symm h)
    · intro hcd
      by_cases hcd' : c = d
      · subst hcd'; exact G.irrefl hcd
      have had : a ≠ d := fun h => hda h.symm
      have hle := h4 a d had
      have hb : b ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj d w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hab', G.adj_symm hbd⟩
      have hcm : c ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj d w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨G.adj_symm hca, G.adj_symm hcd⟩
      have h2 : 1 < (Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj d w)).card :=
        Finset.one_lt_card.mpr ⟨b, hb, c, hcm, fun h => hcb h.symm⟩
      omega
  · refine Or.inr ⟨v0, v1, v2, v3, Or.inl h01, h12, Or.inl h23, ?_, ?_, ?_⟩
    · intro h; exact htri v0 v1 v2 (hsub _ _ h01) (hsub _ _ h12) (G.adj_symm h)
    · intro h; exact htri v1 v2 v3 (hsub _ _ h12) (hsub _ _ h23) (G.adj_symm h)
    · exact htri v3 v4 v0 (hsub _ _ h34) (hsub _ _ h40)
