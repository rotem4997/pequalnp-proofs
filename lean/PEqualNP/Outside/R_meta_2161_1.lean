import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2161_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x3 : ℕ) ≠ 0 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (∃ (x4 : Fin x1.gates.length), (x4 : ℕ) = 1 ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x3 : ℕ) ≠ 0 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → ¬ (∃ (x4 : Fin x1.gates.length), (x4 : ℕ) = 1 ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro x1 hfan hnot hwire hfun
  obtain ⟨i, hi, huniq⟩ := hnot
  by_cases hi0 : (i : ℕ) = 0
  · have hpos : 0 < x1.gates.length := by simpa [hi0] using i.isLt
    have hi0' : i = ⟨0, hpos⟩ := Fin.ext hi0
    subst i
    cases hgs : x1.gates with
    | nil =>
      rw [hgs] at hpos
      simp at hpos
    | cons g gs =>
      have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        simpa [List.get_eq_getElem, hgs] using hi
      have keep : ∀ (rest : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
          10 ≤ w.length →
          (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD 9 false =
            w.getD 9 false := by
        intro rest
        induction rest with
        | nil => intro w hw; rfl
        | cons g' rest ih =>
          intro w hw
          rw [List.foldl_cons, ih]
          · rw [List.getD_append _ _ _ _ (by omega)]
          · simp only [List.length_append, List.length_singleton]
            omega
      have hfirst (x : Fin (9 : ℕ) → Bool) :
          (x1.wires (List.ofFn x)).getD 9 false =
            g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) := by
        change (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
          (List.ofFn x)).getD 9 false = _
        rw [hgs]
        change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
          (List.ofFn x ++ [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)])).getD 9 false = _
        rw [keep gs _ (by
          simp only [List.length_append, List.length_singleton, List.length_ofFn]
          omega)]
        rw [List.getD_append_right _ _ _ _ (by
          simp only [List.length_ofFn]
          omega)]
        simp
      let z : Fin (9 : ℕ) → Bool := fun _ => false
      have hz : (!((g.inputs.map fun j => (List.ofFn z).getD j false).headD false)) = false := by
        have hz := hwire z
        rw [hfirst z, hop] at hz
        have heval (l : List Bool) :
            PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.not l =
              !(l.headD false) := rfl
        rw [heval] at hz
        dsimp only [z] at hz
        simp only [Bool.false_or] at hz
        exact hz
      cases hinputs : g.inputs with
      | nil => simp [hinputs] at hz
      | cons j js =>
        simp only [hinputs, List.map_cons, List.headD_cons] at hz
        by_cases hj : j < 9
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at hz
          interval_cases j <;> simp [z] at hz
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)] at hz
          simp at hz
  · by_cases hsecond : ∃ j : Fin x1.gates.length,
        (j : ℕ) = 1 ∧ (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and
    · exact h1 x1 hfan ⟨i, hi0, hi, huniq⟩ hsecond hwire hfun
    · exact h2 x1 hfan ⟨i, hi0, hi, huniq⟩ hsecond hwire hfun
