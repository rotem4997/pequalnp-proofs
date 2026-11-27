import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5330_917
    (bottom : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)), (∀ e ∈ S, e ∈ Ustar G C ∧ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
          OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
          (∀ j ∈ junk G C, ¬InCone n C j g) ∧ ∀ j ∈ junk G C, ¬InCone n C j h) →
        S.card ≤ k * (C.size + 1))
    (deep : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)), (∀ e ∈ S, e ∈ Ustar G C ∧ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
          OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
          gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧
          gateVal n C h (pairInput u u) = false ∧ gateVal n C h (pairInput v v) = false ∧
          ((∃ j ∈ junk G C, InCone n C j g) ∨ ∃ j ∈ junk G C, InCone n C j h)) →
        S.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k1, h1⟩ := bottom
  obtain ⟨k2, h2⟩ := deep
  refine ⟨k1 + k2, ?_⟩
  intro n G _ C hg hL hT
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : Sym2 (Fin n) → Prop, ∀ e, Q e ↔ (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
          OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
          (∀ j ∈ junk G C, ¬InCone n C j g) ∧ ∀ j ∈ junk G C, ¬InCone n C j h) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Sym2 (Fin n) → Prop, ∀ e, P e ↔ (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
          OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
          gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧
          gateVal n C h (pairInput u u) = false ∧ gateVal n C h (pairInput v v) = false ∧
          ((∃ j ∈ junk G C, InCone n C j g) ∨ ∃ j ∈ junk G C, InCone n C j h)) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hb := h1 n G C hg hL hT ((Ustar G C).filter Q)
    (fun e he => ⟨(Finset.mem_filter.mp he).1, (hQ e).mp (Finset.mem_filter.mp he).2⟩)
  have hd := h2 n G C hg hL hT ((Ustar G C).filter P)
    (fun e he => ⟨(Finset.mem_filter.mp he).1, (hP e).mp (Finset.mem_filter.mp he).2⟩)
  rw [Nat.add_mul]
  refine le_trans (le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _))
    (Nat.add_le_add hb hd)
  intro e he
  obtain ⟨heU, u, v, rfl, t, ht, g, hgj, h, hhj, hne, r0, r1, gx, hx, gu, gv, hu, hv⟩ :=
    Finset.mem_filter.mp he
  by_cases hbg : ∀ j ∈ junk G C, ¬InCone n C j g
  · by_cases hbh : ∀ j ∈ junk G C, ¬InCone n C j h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heU, (hQ _).mpr
        ⟨u, v, rfl, t, ht, g, hgj, h, hhj, hne, r0, r1, gx, hx, hbg, hbh⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heU, (hP _).mpr
        ⟨u, v, rfl, t, ht, g, hgj, h, hhj, hne, r0, r1, gx, hx, gu, gv, hu, hv,
          Or.inr (Classical.byContradiction fun hc =>
            hbh fun j hj hin => hc ⟨j, hj, hin⟩)⟩⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heU, (hP _).mpr
      ⟨u, v, rfl, t, ht, g, hgj, h, hhj, hne, r0, r1, gx, hx, gu, gv, hu, hv,
        Or.inl (Classical.byContradiction fun hc =>
          hbg fun j hj hin => hc ⟨j, hj, hin⟩)⟩⟩)
