import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Two raw OR operands that jointly mask a cubic input must be adjacent.
-- Use this constraint to seek a vertex cover paid for by the gates.
theorem PEqualNP.Outside.R_meta_5022_73
    (mates : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit) (v a b : Fin n),
      (G.neighborSet v).ncard = 3 → (∀ w (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∀ x y, G.Adj x y → x ∉ A) → v ∉ A → a ∉ A → b ∉ A → v ≠ a → v ≠ b →
      FanInTwo C → circuitFun n C = graphFun G A →
      (∀ g ∈ C.gates, v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) →
        g.op = .or ∧ (g.inputs.Perm [v.val, a.val] ∨ g.inputs.Perm [v.val, b.val])) → G.Adj a b)
    (cover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ w (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∀ x y, G.Adj x y → x ∉ A) → IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      let R (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, 2 ≤ (R v).length ∧ ((R v).length = 2 → ∀ g ∈ R v, g.op = .or)) →
      (∃ v ∉ A, (R v).length = 2) →
      (∀ (v a b : Fin n), v ∉ A → a ∉ A → b ∉ A → v ≠ a → v ≠ b → (R v).length = 2 →
        (∀ g ∈ R v, g.inputs.Perm [v.val, a.val] ∨ g.inputs.Perm [v.val, b.val]) → G.Adj a b) →
      ∃ T : Finset (Fin n), (∀ x y, G.Adj x y → x ∈ T ∨ y ∈ T) ∧
        A.card + G.edgeSet.ncard + T.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∀ x17 ∉ x4,                           have x19 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x17) x6.gates;                           x19.length = (2 : ℕ) → ∀ x21 ∈ x19, x21.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                         (∃ x18 ∉ x4, (List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x18) x6.gates).length = (2 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n k G A f C hdegree hgirth hapart he hminimum hfun hfan hcomputes hsize hreads hor htwo
  let R (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  have correct : circuitFun n C = graphFun G A := by
    rw [hcomputes]
    funext x
    apply Bool.eq_iff_iff.mpr
    refine (hfun x).trans ?_
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have minimal : IsMinimalCircuit n C := by
    refine ⟨hfan, fun D hD hEq => hsize D.size ?_⟩
    exact ⟨D, hD, le_rfl, fun x => congrFun (hEq.trans hcomputes) x⟩
  have localMate (v a b : Fin n) (hv : v ∉ A) (ha : a ∉ A) (hb : b ∉ A)
      (hva : v ≠ a) (hvb : v ≠ b) (hlen : (R v).length = 2)
      (hpair : ∀ g ∈ R v, g.inputs.Perm [v.val, a.val] ∨ g.inputs.Perm [v.val, b.val]) :
      G.Adj a b := by
    apply mates n G A C v a b (hdegree v hv) hgirth hapart hv ha hb hva hvb hfan correct
    intro g hg hgv
    have hm : g ∈ R v := List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr hgv⟩
    exact ⟨hor v hv hlen g hm, hpair g hm⟩
  obtain ⟨T, hT, hbound⟩ :=
    cover n G A C hdegree hgirth hapart minimal correct (fun v hv => ⟨hreads v hv, hor v hv⟩) htwo localMate
  have hk := hminimum T hT
  omega
