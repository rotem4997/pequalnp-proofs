import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Each qualifying set of OR-reachable inputs is contained in a neighborhood,
-- or has at least three members with at most one outside the neighborhood.
-- Following a leaf down to a small operand charges it to a gate.
theorem PEqualNP.Outside.R_meta_2579_2
    (covered : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ (C : Circuit), IsAO2 n C → ∀ E : Finset (Sym2 (Fin n)),
      (∀ e ∈ E, ∃ u v : Fin n, e = s(u,v) ∧ ∃ w < n + C.gates.length,
        v ∈ orIn n C w ∧
        ((2 ≤ (orIn n C w).card ∧ ∀ a ∈ orIn n C w, G.Adj u a) ∨
         (3 ≤ (orIn n C w).card ∧ ((orIn n C w).filter fun a => ¬G.Adj u a).card ≤ 1))) →
      E.card ≤ 12 * C.size)
    (core : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ Ustar G C →
      (∀ u v : Fin n, s(u,v) ∈ H → ∀ w < n + C.gates.length, v ∈ orIn n C w →
        (2 ≤ (orIn n C w).card → ∃ a ∈ orIn n C w, ¬G.Adj u a) ∧
        (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun a => ¬G.Adj u a).card)) →
      H.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,hk⟩ := core
  refine ⟨12+k,?_⟩
  intro n G _ girth edges C least top
  let E := Ustar G C
  let P (e : Sym2 (Fin n)) := ∃ u v : Fin n, e = s(u,v) ∧ ∃ w < n + C.gates.length,
    v ∈ orIn n C w ∧ ((2 ≤ (orIn n C w).card ∧ ∀ a ∈ orIn n C w, G.Adj u a) ∨
      (3 ≤ (orIn n C w).card ∧ ((orIn n C w).filter fun a => ¬G.Adj u a).card ≤ 1))
  have first := covered n G girth C least.1 (E.filter P) (fun _ he => (Finset.mem_filter.mp he).2)
  have second := hk n G girth edges C least top (E.filter fun e => ¬P e)
    (Finset.filter_subset _ E) (by
      intro u v huv w hw hv
      have outside := (Finset.mem_filter.mp huv).2
      constructor
      · intro size
        by_contra! all
        exact outside ⟨u,v,rfl,w,hw,hv,Or.inl ⟨size,all⟩⟩
      · intro size
        by_contra! few
        exact outside ⟨u,v,rfl,w,hw,hv,Or.inr ⟨size,by omega⟩⟩)
  have parts := Finset.card_filter_add_card_filter_not (s := E) P
  have full : E.card ≤ (12+k) * (C.size+1) := by rw [Nat.add_mul]; omega
  exact (Finset.card_le_card (Finset.filter_subset _ E)).trans full
