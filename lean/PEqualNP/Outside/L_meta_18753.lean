import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18753
open PEqualNP.BicliqueBlockCost
open scoped BigOperators

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (cover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    HasBlockCost G (G.edgeSet.ncard + T.card - 1) := by
  classical
  let N (a : Fin n) := Finset.univ.filter fun b => G.Adj a b ∧ (b ∉ T ∨ a < b)
  let S := T.filter fun a => (N a).Nonempty
  let star (a : Fin n) : Block n := ({a}, N a)
  have inj : Function.Injective star := by
    intro a b eq
    have e : ({a} : Finset (Fin n)) = {b} := congrArg Prod.fst eq
    simpa using e
  let F := S.image star
  have owns {a b : Fin n} : b ∈ N a ↔ G.Adj a b ∧ (b ∉ T ∨ a < b) := by simp [N]
  have active {a : Fin n} : a ∈ S ↔ a ∈ T ∧ (N a).Nonempty := by simp [S]
  have hit {a b : Fin n} (hab : G.Adj a b) :
      (a ∈ S ∧ b ∈ N a) ∨ (b ∈ S ∧ a ∈ N b) := by
    by_cases ha : a ∈ T
    · by_cases h : b ∉ T ∨ a < b
      · have hn := owns.mpr ⟨hab,h⟩
        exact Or.inl ⟨active.mpr ⟨ha,b,hn⟩, hn⟩
      · push_neg at h
        have hn := owns.mpr ⟨hab.symm, Or.inr (lt_of_le_of_ne h.2 hab.ne.symm)⟩
        exact Or.inr ⟨active.mpr ⟨h.1,a,hn⟩, hn⟩
    · have hn := owns.mpr ⟨hab.symm,Or.inl ha⟩
      exact Or.inr ⟨active.mpr ⟨(cover _ _ hab).resolve_left ha,a,hn⟩, hn⟩
  refine ⟨F, ⟨?_,?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨?_,?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hn
      have hv' : v = a := by simpa [star] using hv
      subst v
      exact (owns.mp hn).1.ne rfl
    · exact ⟨a, by simp [star]⟩
    · exact (active.mp ha).2
    · intro u hu v hv
      have hu' : u = a := by simpa [star] using hu
      subst u
      exact (owns.mp hv).1
  · intro a b hab
    rcases hit hab with ⟨ha,hn⟩ | ⟨hb,hn⟩
    · exact ⟨star a, Finset.mem_image_of_mem _ ha, Or.inl ⟨by simp [star], hn⟩⟩
    · exact ⟨star b, Finset.mem_image_of_mem _ hb, Or.inr ⟨by simp [star], hn⟩⟩
  · have hc : F.card = S.card := Finset.card_image_of_injective _ inj
    have ht : S.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have sum : (∑ i ∈ S, (N i).card) ≤ G.edgeSet.ncard := by
      let edge (p : Σ _ : Fin n, Fin n) : Sym2 (Fin n) := s(p.1,p.2)
      have le : (S.sigma N).card ≤ G.edgeFinset.card := by
        apply Finset.card_le_card_of_injOn edge
        · rintro ⟨a,b⟩ h
          exact SimpleGraph.mem_edgeFinset.mpr ((owns.mp (Finset.mem_sigma.mp h).2).1)
        · rintro ⟨a,b⟩ h ⟨c,d⟩ k eq
          obtain ⟨ha,hb⟩ := Finset.mem_sigma.mp h
          obtain ⟨hc',hd⟩ := Finset.mem_sigma.mp k
          rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · rfl
          · have ab := (owns.mp hb).2.resolve_left (not_not_intro (active.mp hc').1)
            have ba := (owns.mp hd).2.resolve_left (not_not_intro (active.mp ha).1)
            exact (lt_asymm ab ba).elim
      rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
      simpa only [Finset.card_sigma] using le
    have cost : (∑ p ∈ F, blockCost p) = ∑ a ∈ S, (N a).card := by
      rw [show F = S.image star from rfl, Finset.sum_image (fun _ _ _ _ e => inj e)]
      apply Finset.sum_congr rfl
      intro a ha
      simp [blockCost,star]
    rw [familyCost,cost,hc]
    by_cases hS : S = ∅
    · simp [hS]
    · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      omega

end PEqualNP.Outside.L_meta_18753
open PEqualNP.BicliqueBlockCost

theorem PEqualNP.Outside.L_meta_18753 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ))) := by
  intro n G inst T h
  exact PEqualNP.Outside.L_meta_18753.build G T h
