import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5266_517
    (route : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsAO2 n C → TopForm G C → ∀ a ∈ tops G C, ∀ u v : Fin n,
      gateVal n C a (pairInput u v) = true →
      (∀ z ∈ side C a 0 ∪ side C a 1, z ∉ s(u,v)) →
      ∃ i ∈ junk G C, ∃ j ∈ junk G C, i ≠ j ∧
        OrReaches n C (opnd C a 0) i ∧ OrReaches n C (opnd C a 1) j ∧
        ¬ OrReaches n C (opnd C a 1) i ∧ ¬ OrReaches n C (opnd C a 0) j ∧
        gateVal n C i (pairInput u v) = true ∧ gateVal n C j (pairInput u v) = true)
    (charge : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 5 ≤ w.length) →
      G.edgeFinset.Nonempty → ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      ∀ E : Finset (Sym2 (Fin n)), E ⊆ Ustar G C →
      (∀ e ∈ E, ¬ ∃ u v : Fin n, e = s(u,v) ∧
        ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧
          (∀ z ∈ orIn n C (n+h), G.Adj u z) ∧ orIn n C (opnd C h b) = {v}) →
      (∀ e ∈ E, ∃ u v : Fin n, e = s(u,v) ∧ ∃ a ∈ tops G C \ centreless G C,
        (∀ z ∈ side C a 0 ∪ side C a 1, z ∉ s(u,v)) ∧
        ∃ i ∈ junk G C, ∃ j ∈ junk G C, i ≠ j ∧
          OrReaches n C (opnd C a 0) i ∧ OrReaches n C (opnd C a 1) j ∧
          ¬ OrReaches n C (opnd C a 1) i ∧ ¬ OrReaches n C (opnd C a 0) j ∧
          gateVal n C i (pairInput u v) = true ∧ gateVal n C j (pairInput u v) = true) →
      E.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∀ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∉ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k, bound⟩ := charge
  refine ⟨k, ?_⟩
  intro n G _ girth nonempty C least top
  let E := {e ∈ Ustar G C | (¬ ∃ u v : Fin n, e = s(u,v) ∧
    ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧
      (∀ z ∈ orIn n C (n+h), G.Adj u z) ∧ orIn n C (opnd C h b) = {v}) ∧
    ∃ a ∈ tops G C \ centreless G C, e ∈ gammaE G C a ∧
      ∀ z ∈ side C a 0 ∪ side C a 1, z ∉ e}
  change E.card ≤ k * (C.size + 1)
  have hE := fun e (he : e ∈ E) => Finset.mem_filter.mp he
  apply bound n G girth nonempty C least top E
  · exact fun e he => (hE e he).1
  · exact fun e he => (hE e he).2.1
  · intro e he
    obtain ⟨a, ha, hGamma, hside⟩ := (hE e he).2.2
    obtain ⟨_, u, v, heq, hv⟩ := Finset.mem_filter.mp hGamma
    have hdis : ∀ z ∈ side C a 0 ∪ side C a 1, z ∉ s(u,v) := heq ▸ hside
    exact ⟨u, v, heq, a, ha, hdis,
      route n G C least.1 top a (Finset.mem_sdiff.mp ha).1 u v hv hdis⟩
