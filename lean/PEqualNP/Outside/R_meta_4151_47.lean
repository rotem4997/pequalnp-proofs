import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4151_47
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → (∃ u ∉ x4, ∃ v ∉ x4, x2.Adj u v ∧ (x7 u).length = (2 : ℕ) ∧ (x7 v).length = (2 : ℕ)) → (∃ v ∉ x4, (x7 v).length = (2 : ℕ) ∧ ∃ g ∈ x7 v, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → (∃ u ∉ x4, ∃ v ∉ x4, x2.Adj u v ∧ (x7 u).length = (2 : ℕ) ∧ (x7 v).length = (2 : ℕ)) → (∀ w ∉ x4, ∀ g ∈ x7 w, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ v ∉ x4, (x7 v).length = (2 : ℕ) ∧ ∃ g ∈ x7 v, g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18)
    (h3 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → (∃ u ∉ x4, ∃ v ∉ x4, x2.Adj u v ∧ (x7 u).length = (2 : ℕ) ∧ (x7 v).length = (2 : ℕ)) → (∀ w ∉ x4, ∀ g ∈ x7 w, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro x1 x2 x3 x4 x5 x6 x7 hdeg hgirth hnoMarked hedge hfan hcomp hmin hread hind
  let S2 : Finset (Fin x1) := {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}
  have hmemS2 : ∀ u : Fin x1, u ∈ S2 ↔ u ∉ x4 ∧ (x7 u).length = 2 := by
    intro u
    simp only [S2, Finset.mem_filter, Finset.mem_compl]
  have hadjS2 : ∃ u ∉ x4, ∃ v ∉ x4, x2.Adj u v ∧ (x7 u).length = 2 ∧ (x7 v).length = 2 :=
    (Classical.em (∃ u ∉ x4, ∃ v ∉ x4, x2.Adj u v ∧ (x7 u).length = 2 ∧ (x7 v).length = 2)).elim id fun hno =>
      False.elim (by
        have hsub : S2 ⊆ x4ᶜ := fun u hu => Finset.mem_compl.mpr ((hmemS2 u).mp hu).1
        have hindep : ∀ u ∈ S2, ∀ v ∈ S2, ¬x2.Adj u v := fun u hu v hv hadj =>
          hno ⟨u, ((hmemS2 u).mp hu).1, v, ((hmemS2 v).mp hv).1, hadj, ((hmemS2 u).mp hu).2, ((hmemS2 v).mp hv).2⟩
        have hle : x4ᶜ.card + 2 * S2.card ≤ 2 * S2.card := hind S2 hsub hindep
        exact hedge.elim fun u0 hv0 => hv0.elim fun v0 hadj0 => by
          have hpos : 0 < x4ᶜ.card := Finset.card_pos.mpr ⟨u0, Finset.mem_compl.mpr (hnoMarked u0 v0 hadj0)⟩
          omega)
  exact (Classical.em (∃ v ∉ x4, (x7 v).length = 2 ∧ ∃ g ∈ x7 v, g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).elim
    (fun hnot => @h1 x1 x2 x3 x4 x5 hdeg hgirth hnoMarked hedge hfan hcomp hmin hread hind hadjS2 hnot)
    fun hno_not =>
      have hAO : ∀ w ∉ x4, ∀ g ∈ x7 w,
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        intro w hw g hg
        have hb := hread w hw
        exact (Classical.em ((x7 w).length = 3)).elim
          (fun hlen3 => Or.inr (hb.2.2 hlen3 g hg))
          fun hne3 => by
            have hlen2 : (x7 w).length = 2 := by
              have hlo : 2 ≤ (x7 w).length := hb.1
              have hhi : (x7 w).length ≤ 3 := hb.2.1
              omega
            have hg_mem : g ∈ x5.gates := (List.mem_filter.mp hg).1
            have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
                g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
              simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hg_mem).1
            exact hop.elim Or.inl fun hor_not =>
              hor_not.elim Or.inr fun hgn =>
                False.elim (hno_not ⟨w, hw, hlen2, g, hg, hgn⟩)
      (Classical.em (∃ v ∉ x4, (x7 v).length = 2 ∧ ∃ g ∈ x7 v, g.op = PEqualNP.CircuitLowerBounds.GateOp.and)).elim
        (fun hand => @h2 x1 x2 x3 x4 x5 hdeg hgirth hnoMarked hedge hfan hcomp hmin hread hind hadjS2 hAO hand)
        fun hno_and =>
          have hAllOr : ∀ w ∉ x4, ∀ g ∈ x7 w, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
            intro w hw g hg
            have hb := hread w hw
            exact (Classical.em ((x7 w).length = 3)).elim
              (fun hlen3 => hb.2.2 hlen3 g hg)
              fun hne3 => by
                have hlen2 : (x7 w).length = 2 := by
                  have hlo : 2 ≤ (x7 w).length := hb.1
                  have hhi : (x7 w).length ≤ 3 := hb.2.1
                  omega
                exact (hAO w hw g hg).elim
                  (fun hga => False.elim (hno_and ⟨w, hw, hlen2, g, hg, hga⟩))
                  id
          @h3 x1 x2 x3 x4 x5 hdeg hgirth hnoMarked hedge hfan hcomp hmin hread hind hadjS2 hAllOr
