import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost

theorem PEqualNP.Outside.R_meta_612_2
    (extractBlocks : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      HasBlockCost G C.size)
    (countStars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (F : Finset (Block n)),
      IsBlockCover G F →
      (∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeSet.ncard + S.card ≤ familyCost F + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hedge hfour _ hmin hmono heval
  obtain ⟨F, hcover, hcost⟩ := extractBlocks n G C hedge hfour hmono heval
  have stars : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
    intro p hp
    by_contra! h
    obtain ⟨a, c, ha, hc, hac⟩ := Finset.one_lt_card_iff.mp h.1
    obtain ⟨b, d, hb, hd, hbd⟩ := Finset.one_lt_card_iff.mp h.2
    obtain ⟨hdisj, _, _, hadj⟩ := hcover.1 p hp
    have sep : ∀ u ∈ p.1, ∀ v ∈ p.2, u ≠ v := by
      rintro u hu v hv rfl
      exact Finset.disjoint_left.mp hdisj hu hv
    exact hfour a b c d (sep _ ha _ hb) hac (sep _ ha _ hd) (sep _ hc _ hb).symm
      hbd (sep _ hc _ hd) (hadj _ ha _ hb) (hadj _ hc _ hb).symm
      (hadj _ hc _ hd) (hadj _ ha _ hd).symm
  obtain ⟨S, hS, hcount⟩ := countStars n G F hcover stars
  exact (Nat.add_le_add_left (hmin S hS) _).trans (hcount.trans (Nat.add_le_add_right hcost 1))
