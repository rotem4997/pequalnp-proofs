import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_5266_306
    (trace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ a ∈ tops G C, ∀ e ∈ gammaE G C a,
      (∀ w ∈ side C a 0 ∪ side C a 1, w ∉ e) →
      ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
        OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
        e ∈ gammaE G C g ∧ e ∈ gammaE G C h)
    (count : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), (∀ v : Fin n, ∀ p : G.Walk v v, p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter fun e => ∃ a ∈ tops G C \ centreless G C,
        ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
        OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
        e ∈ gammaE G C g ∧ e ∈ gammaE G C h).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∀ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∉ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, hk⟩ := count
  refine ⟨k, ?_⟩
  intro n G inst girth edges C least top
  apply le_trans _ (hk n G C girth least top)
  apply Finset.card_le_card
  intro e he
  obtain ⟨hu, _, a, ha, active, disjoint⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hu, a, ha,
    trace n G C least top a (Finset.mem_sdiff.mp ha).1 e active disjoint⟩
