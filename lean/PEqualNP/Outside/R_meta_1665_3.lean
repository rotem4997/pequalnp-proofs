import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_1665_3
  (intercept : ∀ C : Circuit,
    let tail := (C.gates.drop 1).map fun g =>
      Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs)
    let reads := fun (g : Gate) => [0,9].any fun i => g.inputs.contains i
    let readers := (tail.filter reads).length
    let cascade := ∃ (pre : List Gate) (g : Gate) (post : List Gate), tail = pre ++ g :: post ∧
      ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧
      ∃ h : Gate, h ∈ post ∧ reads h = false ∧ 10 + pre.length ∈ h.inputs
    FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
    C.size ≤ 15 → (3 ≤ readers ∨ 2 ≤ readers ∧ cascade) →
    (∃ y z : Fin 8 → Bool, circuitFun 9 C (Fin.cons false y) ≠ circuitFun 9 C (Fin.cons false z)) →
    HasCircuitSize 8 (fun y : Fin 8 → Bool => circuitFun 9 C (Fin.cons false y)) 11)
  (cofactor :
    let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => F (Fin.cons false y)) 11)
  (few :
    let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit,
    let tail := (C.gates.drop 1).map fun g =>
      Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs)
    let reads := fun (g : Gate) => [0,9].any fun i => g.inputs.contains i
    let readers := (tail.filter reads).length
    FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
    circuitFun 9 C = F → C.size ≤ 15 → readers ≤ 1 → False)
  (two :
    let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit,
    let tail := (C.gates.drop 1).map fun g =>
      Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs)
    let reads := fun (g : Gate) => [0,9].any fun i => g.inputs.contains i
    let readers := (tail.filter reads).length
    let cascade := ∃ (pre : List Gate) (g : Gate) (post : List Gate), tail = pre ++ g :: post ∧
      ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧
      ∃ h : Gate, h ∈ post ∧ reads h = false ∧ 10 + pre.length ∈ h.inputs
    FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
    circuitFun 9 C = F → C.size ≤ 15 → readers = 2 → ¬ cascade → False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  classical
  intro C hFan hHead hFun
  let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let tail := (C.gates.drop 1).map fun g =>
      Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs)
  let reads := fun (g : Gate) => [0,9].any fun i => g.inputs.contains i
  let readers := (tail.filter reads).length
  let cascade := ∃ (pre : List Gate) (g : Gate) (post : List Gate), tail = pre ++ g :: post ∧
      ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧
      ∃ h : Gate, h ∈ post ∧ reads h = false ∧ 10 + pre.length ∈ h.inputs
  by_contra! hbound
  have hSize : C.size ≤ 15 := by omega
  by_cases hFew : readers ≤ 1
  · exact few C hFan hHead hFun hSize hFew
  by_cases hBad : 3 ≤ readers ∨ 2 ≤ readers ∧ cascade
  · let zero : Fin 8 → Bool := fun _ => false
    let edge : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have hZero : F (Fin.cons false zero) = false := by decide
    have hEdge : F (Fin.cons false edge) = true := by decide
    have distinct : circuitFun 9 C (Fin.cons false zero) ≠ circuitFun 9 C (Fin.cons false edge) := by
      intro h
      have hz := congrFun hFun (Fin.cons false zero)
      have he := congrFun hFun (Fin.cons false edge)
      change circuitFun 9 C (Fin.cons false zero) = F (Fin.cons false zero) at hz
      change circuitFun 9 C (Fin.cons false edge) = F (Fin.cons false edge) at he
      rw [hZero] at hz
      rw [hEdge] at he
      exact Bool.false_ne_true (hz.symm.trans (h.trans he))
    have restricted := intercept C hFan hHead hSize hBad ⟨zero, edge, distinct⟩
    have eq : (fun y : Fin 8 → Bool => circuitFun 9 C (Fin.cons false y)) =
        (fun y : Fin 8 → Bool => F (Fin.cons false y)) := by
      funext y
      exact congrFun hFun (Fin.cons false y)
    rw [eq] at restricted
    exact cofactor restricted
  have hNotMany : ¬ 3 ≤ readers := fun h => hBad (Or.inl h)
  have hTwo : readers = 2 := by omega
  have hNoCascade : ¬ cascade := fun h => hBad (Or.inr ⟨by omega, h⟩)
  exact two C hFan hHead hFun hSize hTwo hNoCascade
