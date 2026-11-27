import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The cover, reader and adjacent-pair proofs are available as separate local lemmas.
-- They build on L_meta_2086, L_meta_4047 and the wire counting in R_meta_2084_2.
theorem PEqualNP.Outside.R_meta_4051_4
    (cover : ∀ (n s : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∃ u v, G.Adj u v) → (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      G.edgeSet.ncard + T.card ≤ s+1 →
      (∀ x, f x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ v, (G.neighborSet v).ncard = 3 ∧ ∃ t, t+4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (readers : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (b : Bool), FanInTwo C →
      (∃ x : Fin n → Bool, circuitFun n C (Function.update x v b) = false) →
      ∃ t, t + (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v b)) t)
    (lightEdge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), IsMinimalCircuit n C →
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ x, circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        C.size + 1 < G.edgeSet.ncard + T.card) →
      ∃ u v : Fin n, G.Adj u v ∧
        (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains u.val)).length ≤ 2 ∧
        (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 2)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), IsMinimalCircuit n C →
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) → (∃ u v, G.Adj u v) →
      (∀ x, circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        C.size + 1 < G.edgeSet.ncard + T.card) →
      (∀ v : Fin n, (G.neighborSet v).ncard = 3 →
        (C.gates.filter (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 3) →
      (∃ u v : Fin n, G.Adj u v ∧
        (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains u.val)).length ≤ 2 ∧
        (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 2) →
      ∃ v, (G.neighborSet v).ncard = 3 ∧ ∃ t, t+4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 → ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11 := by
  classical
  intro n G f degree girth edges spec s given
  let k := Nat.find (show ∃ k, HasCircuitSize n f k from ⟨s, given⟩)
  have small : HasCircuitSize n f k := Nat.find_spec _
  have least (j) (hj : HasCircuitSize n f j) : k ≤ j := Nat.find_min' _ hj
  obtain ⟨C, fan, cost, computes⟩ := small
  have eq : circuitFun n C = f := funext computes
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan, ?_⟩
    intro D ok same
    exact cost.trans (least D.size ⟨D, ok, le_rfl, congrFun (same.trans eq)⟩)
  have le := cost.trans (least s given)
  by_cases cheap : ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeSet.ncard + T.card ≤ C.size+1
  · obtain ⟨T, hc, ht⟩ := cheap
    exact cover n s G T f degree edges hc (by omega) spec
  have expensive (T : Finset (Fin n)) (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
      C.size+1 < G.edgeSet.ncard + T.card := by
    by_contra! h
    exact cheap ⟨T, hc, h⟩
  by_cases high : ∃ v : Fin n, (G.neighborSet v).ncard = 3 ∧
      4 ≤ (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length
  · obtain ⟨v, deg, count⟩ := high
    have zero : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
      funext i
      by_cases h : i = v <;> simp [Function.update, h]
    have atZero : circuitFun n C (Function.update (fun _ => false) v false) = false := by
      rw [eq, zero, Bool.eq_false_iff]
      simpa using (spec (fun _ => false)).mp
    obtain ⟨t, bound, builds⟩ := readers n C v false fan ⟨_, atZero⟩
    exact ⟨v, deg, t, by omega, by simpa only [eq] using builds⟩
  have low (v : Fin n) (hv : (G.neighborSet v).ncard = 3) :
      (C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 3 := by
    by_contra! h
    exact high ⟨v, hv, by omega⟩
  obtain ⟨v, deg, t, bound, builds⟩ :=
    sparse n G C minimal degree girth edges (by simpa only [eq] using spec) expensive low
      (lightEdge n G C minimal degree (by simpa only [eq] using spec) expensive)
  exact ⟨v, deg, t, by omega, by simpa only [eq] using builds⟩
