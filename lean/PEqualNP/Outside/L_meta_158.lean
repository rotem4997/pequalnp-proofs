import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_158 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (mk : Fin n → Fin n → Prop) [DecidableRel mk],
    (∀ u v : Fin n, G.Adj u v → mk u v ∨ mk v u) →
    ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧
      T.card ≤
        (G.edgeFinset.filter (fun e => ∀ a b : Fin n, e = s(a, b) → mk a b ∧ mk b a)).card +
        (Finset.univ.filter (fun u => ∃ v : Fin n, G.Adj u v ∧ ¬ mk u v)).card := by
  intro n G _ mk _ h
  classical
  refine ⟨(Finset.univ.filter (fun u => ∃ v : Fin n, G.Adj u v ∧ ¬ mk u v)) ∪
    (G.edgeFinset.filter (fun e => ∀ a b : Fin n, e = s(a, b) → mk a b ∧ mk b a)).image
      (fun e => (Quot.out e).1), ?_, ?_⟩
  · intro u w huw
    by_cases h1 : mk u w
    · by_cases h2 : mk w u
      · have hD : s(u, w) ∈ G.edgeFinset.filter
            (fun e => ∀ a b : Fin n, e = s(a, b) → mk a b ∧ mk b a) := by
          rw [Finset.mem_filter]
          refine ⟨by rw [SimpleGraph.mem_edgeFinset]; exact huw, ?_⟩
          intro a b hab
          rw [Sym2.eq_iff] at hab
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨h1, h2⟩
          · exact ⟨h2, h1⟩
        have hout : s((Quot.out s(u, w)).1, (Quot.out s(u, w)).2) = s(u, w) :=
          Quot.out_eq _
        have hmem := Finset.mem_image_of_mem (fun e : Sym2 (Fin n) => (Quot.out e).1) hD
        rw [Sym2.eq_iff] at hout
        rcases hout with ⟨e1, _⟩ | ⟨e1, _⟩
        · left
          exact Finset.mem_union_right _ (e1 ▸ hmem)
        · right
          exact Finset.mem_union_right _ (e1 ▸ hmem)
      · right
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, u, huw.symm, h2⟩)
    · left
      exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, w, huw, h1⟩)
  · refine (Finset.card_union_le _ _).trans ?_
    rw [add_comm]
    exact Nat.add_le_add_right Finset.card_image_le _
