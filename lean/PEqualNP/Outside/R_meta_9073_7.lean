import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- A circuit whose output wire is not an input has that wire produced by one gate, and that gate
-- is an AND or an OR. The step is asked once for each of the two cases, on the top gate.
theorem PEqualNP.Outside.R_meta_9073_7
    (topAnd :
      ∀ (C : Circuit), (26 : ℕ) ≤ C.output → C.output < (26 : ℕ) + C.size →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ))
              ∨ p = l + (9 : Fin (13 : ℕ))) ∧ p ≠ (0 : Fin (13 : ℕ)) ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (26 : ℕ))).op = GateOp.and →
        (59 : ℕ) ≤ C.size)
    (topOr :
      ∀ (C : Circuit), (26 : ℕ) ≤ C.output → C.output < (26 : ℕ) + C.size →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ))
              ∨ p = l + (9 : Fin (13 : ℕ))) ∧ p ≠ (0 : Fin (13 : ℕ)) ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (26 : ℕ))).op = GateOp.or →
        (59 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro x1 hOut hAO hEval
  have wlen : ∀ (gs : List Gate) (us : List Bool),
      (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) us gs).length
        = us.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro us; simp
    | cons g rest ih =>
        intro us
        rw [List.foldl_cons, ih]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  have hsz : x1.size = x1.gates.length := rfl
  have hl (y : Fin (26 : ℕ) → Bool) : (x1.wires (List.ofFn y)).length = (26 : ℕ) + x1.size := by
    change (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn y) x1.gates).length = (26 : ℕ) + x1.gates.length
    rw [wlen, List.length_ofFn]
  -- The output wire has to exist: past the last wire every read is false, and the function is
  -- true at the pair (1, 0).
  have hlt : x1.output < (26 : ℕ) + x1.size := by
    by_contra hnot
    have hge : (26 : ℕ) + x1.size ≤ x1.output := Nat.le_of_not_lt hnot
    have hfalse : x1.eval (List.ofFn (fun i => decide (i = Fin.castAdd (13 : ℕ) (1 : Fin (13 : ℕ))
        ∨ i = Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ))))) = Bool.false := by
      change (x1.wires (List.ofFn (fun i => decide (i = Fin.castAdd (13 : ℕ) (1 : Fin (13 : ℕ))
        ∨ i = Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ)))))).getD x1.output false = false
      apply List.getD_eq_default
      rw [hl]
      omega
    have htrue : x1.eval (List.ofFn (fun i => decide (i = Fin.castAdd (13 : ℕ) (1 : Fin (13 : ℕ))
        ∨ i = Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ))))) = Bool.true :=
      (hEval _).2 ⟨1, 0, Or.inr (Or.inl rfl), by decide, by decide, by decide⟩
    exact Bool.false_ne_true (hfalse ▸ htrue)
  have hj : x1.output - (26 : ℕ) < x1.gates.length := by
    rw [← hsz]; omega
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO.1
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))
      = x1.gates[x1.output - (26 : ℕ)] :=
    List.getD_eq_getElem _ _ hj
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op
      = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = GateOp.or := by
    rw [hgate]
    exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact topAnd x1 hOut hlt hAO hEval hand
  · exact topOr x1 hOut hlt hAO hEval har
