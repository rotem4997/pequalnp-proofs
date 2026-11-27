import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2658_529
    (single : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → NoFourCycle G → Monotone2 C →
      circuitFun n C = graphFun G ∅ → (junk G C).card = 1 →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧ junk G D = ∅)
    (decrease : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → NoFourCycle G → Monotone2 C →
      circuitFun n C = graphFun G ∅ → 2 ≤ (junk G C).card →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (junk G D).card < (junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G C edge noCycle model computes
  have edges : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := edge
    exact ⟨s(u, v), by simpa using huv⟩
  have noFour : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
    by_contra hcd
    have ac := hc.1.ne
    have cb := hc.2.symm.ne
    have bd := hd.2.ne
    have ad := hd.1.ne
    exact noCycle a c b d ac hab ad cb hcd bd hc.1 hc.2.symm hd.2 hd.1.symm
  have graphEval (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp
  have computesGraph : circuitFun n C = graphFun G ∅ := by
    funext x
    have eqTrue : C.eval (List.ofFn x) = true ↔ graphFun G ∅ x = true :=
      (computes x).trans (graphEval x).symm
    change C.eval (List.ofFn x) = graphFun G ∅ x
    exact Bool.eq_iff_iff.mpr eqTrue
  have clean : ∀ (k : ℕ) (B : Circuit), (junk G B).card = k →
      Monotone2 B → circuitFun n B = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ B.size ∧ junk G D = ∅ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro B count mono eq
      by_cases zero : k = 0
      · exact ⟨B, mono, eq, le_rfl, Finset.card_eq_zero.mp (count.trans zero)⟩
      by_cases one : k = 1
      · exact single n G B edges noFour mono eq (count.trans one)
      obtain ⟨B', mono', eq', size', smaller⟩ := decrease n G B edges noFour mono eq (by omega)
      obtain ⟨D, dmono, deq, dsize, djunk⟩ := ih (junk G B').card (by omega) B' rfl mono' eq'
      exact ⟨D, dmono, deq, dsize.trans size', djunk⟩
  obtain ⟨D, dm, deq, ds, dj⟩ := clean (junk G C).card C rfl model computesGraph
  refine ⟨D, dm, ?_, ds, ?_⟩
  · intro x
    change circuitFun n D x = true ↔ _
    rw [deq]
    exact graphEval x
  · intro j g get isAnd x on
    have existsGate := (List.getElem?_eq_some_iff.mp get).1
    have gateEq : gateAt D j = g := by
      change D.gates.getD j ⟨.or, []⟩ = g
      rw [List.getD_eq_getElem _ _ existsGate]
      exact (List.getElem?_eq_some_iff.mp get).2
    apply (graphEval x).mp
    cases eval : graphFun G ∅ x with
    | true => rfl
    | false =>
      have bad : j ∈ junk G D := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr existsGate, (congrArg Gate.op gateEq).trans isAnd,
          existsGate, x, on, eval⟩
      rw [dj] at bad
      exact (Finset.notMem_empty j bad).elim
