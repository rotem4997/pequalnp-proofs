import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4750_1
    (h1 :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (26 : ℕ) ∧
          (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
            x1.gates[x2]? = Option.some x3 →
              (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
                ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
          ∀ (x2 : Fin (14 : ℕ) → Bool),
            x1.eval (List.ofFn x2) = Bool.true ↔
              ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)),
                (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧
                  x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true)
    (h2 :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (27 : ℕ) ∧
          (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
            x1.gates[x2]? = Option.some x3 →
              (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
                ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
          (∀ (x2 : Fin (14 : ℕ) → Bool),
            x1.eval (List.ofFn x2) = Bool.true ↔
              ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)),
                (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧
                  x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧
          ∃ (x2 : ℕ),
            (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
              (14 : ℕ) + x2 = x1.output ∧
              PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2
                (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧
              (∀ (x3 : Fin (2 : ℕ)),
                PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3)
                  (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧
                PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3)
                  (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false) ∧
              ∀ (x3 : Fin (2 : ℕ)), ∃ (y : Fin (14 : ℕ) → Bool),
                PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) y = Bool.true ∧
                  x1.eval (List.ofFn y) = Bool.false) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (27 : ℕ) ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
          x1.gates[x2]? = Option.some x3 →
            (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
              ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
        (∀ (x2 : Fin (14 : ℕ) → Bool),
          x1.eval (List.ofFn x2) = Bool.true ↔
            ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)),
              (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧
                x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧
        ∃ (x2 : ℕ),
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (14 : ℕ) + x2 = x1.output ∧
            PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2
              (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧
            ∀ (x3 : Fin (2 : ℕ)),
              PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3)
                (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧
              PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3)
                (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨x1, hsize, hwf, hfano, x2, hop, hout, hpair, hzero⟩
  by_cases hstrict : ∀ (x3 : Fin 2), ∃ (y : Fin 14 → Bool),
      PEqualNP.CleanedNonEdge.wireVal 14 x1 (PEqualNP.TopForm.opnd x1 x2 x3) y = Bool.true ∧
        x1.eval (List.ofFn y) = Bool.false
  · exact h2 ⟨x1, hsize, hwf, hfano, x2, hop, hout, hpair, hzero, hstrict⟩
  · push Not at hstrict
    obtain ⟨b, hb⟩ := hstrict
    have hx2lt : x2 < x1.gates.length := by
      by_contra hge
      have hnone : x1.gates[x2]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      have hdef : PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2 = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        change x1.gates.getD x2 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
        rw [List.getD_eq_getElem?_getD, hnone]
        rfl
      rw [hdef] at hop
      cases hop
    have hget : x1.gates[x2]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2) := by
      have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2 = x1.gates[x2] := by
        change x1.gates.getD x2 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx2lt]
        rfl
      rw [hgat, List.getElem?_eq_getElem hx2lt]
    obtain ⟨_, w0, w1, hinp, _, hw0, hw1⟩ := hwf x2 _ hget
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
        (gs.foldl step init).length = init.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro init; simp
      | cons g rest ih =>
        intro init
        simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
        omega
    have hstab : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (i : ℕ),
        i < init.length → (gs.foldl step init).getD i false = init.getD i false := by
      intro gs
      induction gs with
      | nil => intro init i _; rfl
      | cons g rest ih =>
        intro init i hi
        simp only [List.foldl_cons]
        have hi' : i < (step init g).length := by
          simp only [step, List.length_append, List.length_singleton]; omega
        rw [ih (step init g) i hi']
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hi]
    have hpre : ∀ (y : Fin 14 → Bool) (w : ℕ), w < 14 + x2 →
        ({ gates := x1.gates.take x2, output := w } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn y) =
          PEqualNP.CleanedNonEdge.wireVal 14 x1 w y := by
      intro y w hw
      have hsplit : x1.gates = x1.gates.take x2 ++ x1.gates.drop x2 := (List.take_append_drop x2 x1.gates).symm
      change ((x1.gates.take x2).foldl step (List.ofFn y)).getD w false =
        (x1.gates.foldl step (List.ofFn y)).getD w false
      conv_rhs => rw [hsplit, List.foldl_append]
      have hw' : w < ((x1.gates.take x2).foldl step (List.ofFn y)).length := by
        rw [hlen, List.length_ofFn, List.length_take]
        omega
      exact (hstab (x1.gates.drop x2) _ w hw').symm
    have hgate : ∀ (y : Fin 14 → Bool),
        x1.eval (List.ofFn y) =
          (PEqualNP.CleanedNonEdge.wireVal 14 x1 w0 y && PEqualNP.CleanedNonEdge.wireVal 14 x1 w1 y) := by
      intro y
      have hsplit : x1.gates =
          x1.gates.take x2 ++ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2 :: x1.gates.drop (x2 + 1)) := by
        have hdrop : x1.gates.drop x2 = PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2 :: x1.gates.drop (x2 + 1) := by
          have := (List.cons_getElem_drop_succ (l := x1.gates) (n := x2) (h := hx2lt)).symm
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2 = x1.gates[x2] := by
            change x1.gates.getD x2 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx2lt]
            rfl
          rw [hgat, this]
        rw [← hdrop, List.take_append_drop]
      change (x1.gates.foldl step (List.ofFn y)).getD x1.output false = _
      rw [← hout]
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
      set prev := (x1.gates.take x2).foldl step (List.ofFn y)
      have hlen1 : prev.length = 14 + x2 := by
        rw [hlen, List.length_ofFn, List.length_take]; omega
      have hidx : 14 + x2 < (step prev (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2)).length := by
        simp only [step, List.length_append, List.length_singleton, hlen1]; omega
      rw [hstab (x1.gates.drop (x2 + 1)) _ (14 + x2) hidx]
      change (prev ++ [(PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op.eval
          ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.map fun i => prev.getD i false)]).getD
        (14 + x2) false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : prev.length ≤ 14 + x2),
        hlen1, Nat.sub_self, List.getElem?_singleton, hop, hinp]
      change (prev.getD w0 false && (prev.getD w1 false && true)) = _
      rw [Bool.and_true]
      have hw0eq : prev.getD w0 false = PEqualNP.CleanedNonEdge.wireVal 14 x1 w0 y := hpre y w0 hw0
      have hw1eq : prev.getD w1 false = PEqualNP.CleanedNonEdge.wireVal 14 x1 w1 y := hpre y w1 hw1
      rw [hw0eq, hw1eq]
    have hopnd0 : PEqualNP.TopForm.opnd x1 x2 0 = w0 := by
      change (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.getD 0 0 = w0
      rw [hinp]; rfl
    have hopnd1 : PEqualNP.TopForm.opnd x1 x2 1 = w1 := by
      change (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.getD 1 0 = w1
      rw [hinp]; rfl
    have hopnd_lt : PEqualNP.TopForm.opnd x1 x2 b < 14 + x2 := by
      rcases b with ⟨bv, hbv⟩
      have hbv' : bv = 0 ∨ bv = 1 := by omega
      rcases hbv' with rfl | rfl
      · change PEqualNP.TopForm.opnd x1 x2 0 < 14 + x2; rw [hopnd0]; exact hw0
      · change PEqualNP.TopForm.opnd x1 x2 1 < 14 + x2; rw [hopnd1]; exact hw1
    have heq : ∀ y : Fin 14 → Bool,
        PEqualNP.CleanedNonEdge.wireVal 14 x1 (PEqualNP.TopForm.opnd x1 x2 b) y = x1.eval (List.ofFn y) := by
      intro y
      have hge_eval := hgate y
      cases hval : PEqualNP.CleanedNonEdge.wireVal 14 x1 (PEqualNP.TopForm.opnd x1 x2 b) y
      · rcases b with ⟨bv, hbv⟩
        have hbv' : bv = 0 ∨ bv = 1 := by omega
        rcases hbv' with rfl | rfl
        · change PEqualNP.CleanedNonEdge.wireVal 14 x1 (PEqualNP.TopForm.opnd x1 x2 0) y = false at hval
          rw [hopnd0] at hval; rw [hge_eval, hval]; rfl
        · change PEqualNP.CleanedNonEdge.wireVal 14 x1 (PEqualNP.TopForm.opnd x1 x2 1) y = false at hval
          rw [hopnd1] at hval; rw [hge_eval, hval, Bool.and_false]
      · have hne := hb y hval
        cases hev : x1.eval (List.ofFn y)
        · exact False.elim (hne hev)
        · rfl
    refine h1 ⟨{ gates := x1.gates.take x2, output := PEqualNP.TopForm.opnd x1 x2 b }, ?_, ?_, ?_⟩
    · change (x1.gates.take x2).length ≤ 26
      rw [List.length_take]
      have : x1.gates.length ≤ 27 := hsize
      omega
    · intro j g hj
      have hjlt : j < x2 := by
        have := List.getElem?_eq_some_iff.mp hj
        rcases this with ⟨hjl, _⟩
        rw [List.length_take] at hjl
        omega
      rw [List.getElem?_take_of_lt hjlt] at hj
      exact hwf j g hj
    · intro y
      rw [hpre y (PEqualNP.TopForm.opnd x1 x2 b) hopnd_lt, heq y]
      exact hfano y
