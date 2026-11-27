import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5328_2
    (hW : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → TopForm G C → ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∃ b : Fin 2, u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b)) ∧ 2 ≤ (orIn n C (opnd C g (1 - b))).card)).card ≤ c * (C.size + 1))
    (hN : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → TopForm G C → ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∃ b : Fin 2, u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b)) ∧ (orIn n C (opnd C g (1 - b))).card ≤ 1)).card ≤ c * (C.size + 1))
    (hR : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → TopForm G C → ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∀ b : Fin 2, ¬ (u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b))))).card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj]
      (x5 : Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → 5 ≤ x7.length) →
      IsLeastAO x3 x5 → TopForm x3 x5 →
      {x9 ∈ Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧
        ∃ x12 ∈ junk x3 x5, x10 ∈ wmax x3 x5 x12 ∧
          gateVal x2 x5 x12 (pairInput x10 x11) = Bool.true ∧
          gateVal x2 x5 x12 (pairInput x10 x10) = Bool.false ∧
          gateVal x2 x5 x12 (pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨c1, h1⟩ := hW
  obtain ⟨c2, h2⟩ := hN
  obtain ⟨c3, h3⟩ := hR
  classical
  refine ⟨c1 + c2 + c3, ?_⟩
  intro n G _inst C hg hL hT
  have key : ∀ (S S1 S2 S3 : Finset (Sym2 (Fin n))), S ⊆ (S1 ∪ S2) ∪ S3 →
      S1.card ≤ c1 * (C.size + 1) → S2.card ≤ c2 * (C.size + 1) →
      S3.card ≤ c3 * (C.size + 1) → S.card ≤ (c1 + c2 + c3) * (C.size + 1) := by
    intro S S1 S2 S3 hs i1 i2 i3
    have hle := Finset.card_le_card hs
    have u1 := Finset.card_union_le (S1 ∪ S2) S3
    have u2 := Finset.card_union_le S1 S2
    have h1' : ((S1 ∪ S2) ∪ S3).card ≤ S1.card + S2.card + S3.card := by omega
    have h2' : S1.card + S2.card + S3.card ≤
        c1 * (C.size + 1) + c2 * (C.size + 1) + c3 * (C.size + 1) := by omega
    have h3' : c1 * (C.size + 1) + c2 * (C.size + 1) + c3 * (C.size + 1) =
        (c1 + c2 + c3) * (C.size + 1) := by ring
    omega
  have hsub : ({x9 ∈ Ustar G C | ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
        ∃ x12 ∈ junk G C, x10 ∈ wmax G C x12 ∧
          gateVal n C x12 (pairInput x10 x11) = Bool.true ∧
          gateVal n C x12 (pairInput x10 x10) = Bool.false ∧
          gateVal n C x12 (pairInput x11 x11) = Bool.false}) ⊆
      ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∃ b : Fin 2, u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b)) ∧ 2 ≤ (orIn n C (opnd C g (1 - b))).card)) ∪ ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∃ b : Fin 2, u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b)) ∧ (orIn n C (opnd C g (1 - b))).card ≤ 1)) ∪ ((Ustar G C).filter (fun e => ∃ (u v : Fin n), e = s(u, v) ∧ ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧ ∀ b : Fin 2, ¬ (u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b))))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heU, u, v, huv, g, hg, hw, hval, hl, hr⟩ := he
    by_cases hb : ∃ b : Fin 2, u ∈ orIn n C (opnd C g b) ∧ v ∈ orIn n C (opnd C g (1 - b))
    · obtain ⟨b, hbu, hbv⟩ := hb
      have hpos : 0 < (orIn n C (opnd C g (1 - b))).card := Finset.card_pos.2 ⟨v, hbv⟩
      by_cases h2c : 2 ≤ (orIn n C (opnd C g (1 - b))).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨heU, u, v, huv, g, hg, hw, hval, hl, hr, b, hbu, hbv, h2c⟩))
      · have h1c : (orIn n C (opnd C g (1 - b))).card ≤ 1 := by omega
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨heU, u, v, huv, g, hg, hw, hval, hl, hr, b, hbu, hbv, h1c⟩))
    · refine Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨heU, u, v, huv, g, hg, hw, hval, hl, hr, ?_⟩)
      intro b hcon
      exact hb ⟨b, hcon.1, hcon.2⟩
  exact key _ _ _ _ hsub (h1 n G C hg hL hT) (h2 n G C hg hL hT) (h3 n G C hg hL hT)
