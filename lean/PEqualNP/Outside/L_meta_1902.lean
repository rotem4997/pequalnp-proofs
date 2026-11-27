import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1902

open PEqualNP.BicliqueBlockCost

-- the small side of a star block
noncomputable def small {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.1 else p.2

-- the pairs split by a block, as unordered pairs
noncomputable def pairs {n : ℕ} (p : Block n) : Finset (Sym2 (Fin n)) :=
  (p.1 ×ˢ p.2).image (fun ab => s(ab.1, ab.2))

lemma small_card {n : ℕ} (p : Block n) (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    (small p).card ≤ 1 := by
  unfold small
  split_ifs with h1
  · exact h1
  · rcases h with h | h
    · exact absurd h h1
    · exact h

lemma pairs_card {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hb : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : (pairs p).card ≤ blockCost p := by
  obtain ⟨_, h1, h2, _⟩ := hb
  have a1 : 1 ≤ p.1.card := Finset.card_pos.mpr h1
  have a2 : 1 ≤ p.2.card := Finset.card_pos.mpr h2
  have hc : (pairs p).card ≤ p.1.card * p.2.card := by
    unfold pairs
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_product _ _))
  unfold blockCost
  rcases h with h | h
  · have e : p.1.card = 1 := le_antisymm h a1
    rw [e] at hc ⊢
    omega
  · have e : p.2.card = 1 := le_antisymm h a2
    rw [e] at hc ⊢
    omega

lemma main {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n))
    (hF : IsBlockCover G F) (hs : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    ∃ X : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G X ∧
      G.edgeSet.ncard + X.card ≤ familyCost F + 1 := by
  classical
  obtain ⟨hblk, hcov⟩ := hF
  refine ⟨F.biUnion small, ?_, ?_⟩
  · intro u v huv
    obtain ⟨p, hp, hc⟩ := hcov u v huv
    have key : ∀ a b : Fin n, a ∈ p.1 → b ∈ p.2 → a ∈ small p ∨ b ∈ small p := by
      intro a b ha hb
      unfold small
      split_ifs
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases key u v h1 h2 with h | h
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
    · rcases key v u h1 h2 with h | h
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  · have hsub : G.edgeSet ⊆ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      have huv : G.Adj u v := he
      obtain ⟨p, hp, hc⟩ := hcov u v huv
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩)
      unfold pairs
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨h1, h2⟩, Sym2.eq_swap⟩
    have hE : G.edgeSet.ncard ≤ ∑ p ∈ F, blockCost p := by
      calc G.edgeSet.ncard
          ≤ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (F.biUnion pairs).card := Set.ncard_coe_finset _
        _ ≤ ∑ p ∈ F, (pairs p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ F, blockCost p :=
            Finset.sum_le_sum (fun p hp => pairs_card G p (hblk p hp) (hs p hp))
    have hX : (F.biUnion small).card ≤ F.card := by
      calc (F.biUnion small).card ≤ ∑ p ∈ F, (small p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ F, 1 := Finset.sum_le_sum (fun p hp => small_card p (hs p hp))
        _ = F.card := by simp
    unfold familyCost
    omega

end PEqualNP.Outside.L_meta_1902

theorem PEqualNP.Outside.L_meta_1902 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (PEqualNP.BicliqueBlockCost.Block x1)), PEqualNP.BicliqueBlockCost.IsBlockCover x2 x3 → (∀ x5 ∈ x3, x5.1.card ≤ (1 : ℕ) ∨ x5.2.card ≤ (1 : ℕ)) → ∃ (x6 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x6 ∧ x2.edgeSet.ncard + x6.card ≤ PEqualNP.BicliqueBlockCost.familyCost x3 + (1 : ℕ) := by
  intro n G F hF hs
  exact PEqualNP.Outside.L_meta_1902.main G F hF hs
