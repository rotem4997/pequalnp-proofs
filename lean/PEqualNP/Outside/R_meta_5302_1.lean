import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5302_1
    (hAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) → ((10 : ℕ) ≤ x1.output ∧ (x1.gates[x1.output - (10 : ℕ)]?).map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op) = some PEqualNP.CircuitLowerBounds.GateOp.and) → (15 : ℕ) ≤ (List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [(1 : ℕ) + (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x1.gates).getD x1.output (0 : ℕ))
    (hOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) → ((10 : ℕ) ≤ x1.output ∧ (x1.gates[x1.output - (10 : ℕ)]?).map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op) = some PEqualNP.CircuitLowerBounds.GateOp.or) → (15 : ℕ) ≤ (List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [(1 : ℕ) + (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x1.gates).getD x1.output (0 : ℕ))
    (hNot : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) → ((10 : ℕ) ≤ x1.output ∧ (x1.gates[x1.output - (10 : ℕ)]?).map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op) = some PEqualNP.CircuitLowerBounds.GateOp.not) → (15 : ℕ) ≤ (List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [(1 : ℕ) + (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x1.gates).getD x1.output (0 : ℕ)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) → (15 : ℕ) ≤ (List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [(1 : ℕ) + (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x1.gates).getD x1.output (0 : ℕ) := by

  intro x1 hFan hOne hEval
  have wireLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons]
      rw [ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have wireGet : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false =
        w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) i
        (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append w [g.op.eval (g.inputs.map fun j => w.getD j false)] false i hi
  by_cases hIn : x1.output < 10
  · exfalso
    have lowFalse (k : ℕ) (hk : x1.output = k) (x : Fin (9 : ℕ) → Bool)
        (hbit : (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD k false = true)
        (hfun : ([(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) = false) : False := by
      have hEv := hEval x
      have evalEq : x1.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) =
          (x1.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))])).getD x1.output false := rfl
      have wiresEq : x1.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) =
          x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) := rfl
      rw [evalEq, wiresEq] at hEv
      have hinp : k < (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).length := by
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
        omega
      rw [hk] at hEv
      rw [wireGet x1.gates (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) k hinp] at hEv
      rw [hbit, hfun] at hEv
      exact Bool.false_ne_true hEv.symm
    interval_cases x1.output
    · exact lowFalse 0 rfl (fun i => decide ((i : ℕ) = 0)) (by decide) (by decide)
    · exact lowFalse 1 rfl (fun i => decide ((i : ℕ) = 1)) (by decide) (by decide)
    · exact lowFalse 2 rfl (fun i => decide ((i : ℕ) = 2)) (by decide) (by decide)
    · exact lowFalse 3 rfl (fun i => decide ((i : ℕ) = 3)) (by decide) (by decide)
    · exact lowFalse 4 rfl (fun i => decide ((i : ℕ) = 4)) (by decide) (by decide)
    · exact lowFalse 5 rfl (fun i => decide ((i : ℕ) = 5)) (by decide) (by decide)
    · exact lowFalse 6 rfl (fun i => decide ((i : ℕ) = 6)) (by decide) (by decide)
    · exact lowFalse 7 rfl (fun i => decide ((i : ℕ) = 7)) (by decide) (by decide)
    · exact lowFalse 8 rfl (fun i => decide ((i : ℕ) = 8)) (by decide) (by decide)
    · exact lowFalse 9 rfl (fun i => decide ((i : ℕ) = 9)) (by decide) (by decide)
  · by_cases hGate : x1.output < 10 + x1.gates.length
    · have h10 : (10 : ℕ) ≤ x1.output := by omega
      have hidx : x1.output - 10 < x1.gates.length := by omega
      have hmap : (x1.gates[x1.output - 10]?).map (fun g => g.op) =
          some (x1.gates[x1.output - 10]).op := by
        rw [getElem?_pos (c := x1.gates) (i := x1.output - 10) hidx]
        rfl
      have hg : x1.gates[x1.output - 10] ∈ x1.gates := List.mem_of_getElem rfl
      have hmem : x1.gates[x1.output - 10].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          x1.gates[x1.output - 10].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          x1.gates[x1.output - 10].op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        have hin := (hFan _ hg).1
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hin
      rcases hmem with hand | hor | hnot
      · exact hAnd x1 hFan hOne hEval ⟨h10, hmap.trans (congrArg some hand)⟩
      · exact hOr x1 hFan hOne hEval ⟨h10, hmap.trans (congrArg some hor)⟩
      · exact hNot x1 hFan hOne hEval ⟨h10, hmap.trans (congrArg some hnot)⟩
    · exfalso
      let x : Fin (9 : ℕ) → Bool := fun i => decide ((i : ℕ) = 0 ∨ (i : ℕ) = 1)
      have hfun : ([(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) = true := by
        decide
      have hEv := hEval x
      have evalEq : x1.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) =
          (x1.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))])).getD x1.output false := rfl
      have wiresEq : x1.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) =
          x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) := rfl
      rw [evalEq, wiresEq] at hEv
      have hlen : (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))])).length =
          (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).length + x1.gates.length :=
        wireLen _ _
      have hinp : (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).length = 10 := by
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
      rw [List.getD_eq_default _ _ (by rw [hlen, hinp]; omega)] at hEv
      rw [hfun] at hEv
      exact Bool.false_ne_true hEv

