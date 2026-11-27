import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4137_1
    (hDelete : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) =
        ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      13 ≤ D.gates.countP PEqualNP.MetaComplexity.SingleLevel.notNot)
    (hExtend : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
      C.gates.countP (fun g => !PEqualNP.MetaComplexity.SingleLevel.notNot g) ≤ 4 →
      (∀ y : Fin 9 → Bool, C.eval [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] =
        ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      ∃ z : Fin 8 → Bool, C.eval (true :: false :: List.ofFn z) ≠
        (z 2 || z 3 || ([(0,1), (1,6), (6,4), (4,7), (7,5), (5,0)] : List (Fin 8 × Fin 8)).any (fun e => z e.1 && z e.2))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hfan hsize
  classical
  by_contra! hcorrect
  let base (y : Fin 9 → Bool) : List Bool :=
    [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8]
  let graph (y : Fin 9 → Bool) : Bool :=
    ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8),
      (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)
  have hbase (y : Fin 9 → Bool) : C.eval (base y) = graph y := by
    let x : Fin 10 → Bool := ![false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8]
    have eqv := hcorrect x (by rfl)
    change C.eval (base y) = _ at eqv
    rw [eqv]
    change (false && y 4 || y 4 && y 0 || y 0 && y 1 || y 1 && y 6 ||
      y 6 && false || false && y 7 || y 4 && y 3 || y 0 && y 5 || y 1 && y 2 ||
      y 6 && y 8 || y 7 && y 5 || y 5 && y 8 || y 8 && y 3 || y 3 && y 2 ||
      y 2 && y 7) = _
    change _ = (y 0 && y 1 || (y 1 && y 2 || (y 2 && y 3 || (y 3 && y 4 ||
      (y 4 && y 0 || (y 0 && y 5 || (y 1 && y 6 || (y 2 && y 7 ||
      (y 3 && y 8 || (y 5 && y 7 || (y 6 && y 8 || (y 8 && y 5 || false))))))))))))
    simp only [Bool.false_and, Bool.false_or,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  -- The missing wire is just past the end of the smaller circuit, including at its output.
  let wire (w : ℕ) : ℕ := if w < 10 then
    [9 + C.gates.length, 4, 0, 1, 6, 7, 3, 5, 2, 8].getD w 0 else w - 1
  let relabel (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map wire⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map relabel, wire C.output⟩
  have hD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hmem
    change g ∈ C.gates.map relabel at hmem
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
    simpa only [relabel, List.length_map] using hfan original horiginal
  have readWire (y : Fin 9 → Bool) (tail : List Bool) (ht : tail.length ≤ C.gates.length)
      (w : ℕ) : (base y ++ tail).getD w false = (List.ofFn y ++ tail).getD (wire w) false := by
    by_cases hw : w < 10
    · rw [List.getD_append (base y) tail false w (by simpa [base] using hw)]
      by_cases hz : w = 0
      · subst w
        change false = (List.ofFn y ++ tail).getD (9 + C.gates.length) false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl
      · have hs : wire w < 9 := by
          interval_cases w <;> first | contradiction | exact of_decide_eq_true rfl
        rw [List.getD_append (List.ofFn y) tail false (wire w) (by simpa using hs)]
        interval_cases w <;> first | contradiction | rfl
    · have hw' : 10 ≤ w := by omega
      rw [show wire w = w - 1 by simp [wire, hw]]
      rw [List.getD_append_right (base y) tail false w (by simpa [base] using hw'),
          List.getD_append_right (List.ofFn y) tail false (w-1) (by simp; omega)]
      simp [base, Nat.sub_sub]
  let step (ws : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have run (y : Fin 9 → Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (tail : List Bool)
      (bound : tail.length + gs.length ≤ C.gates.length) :
      ∃ vals : List Bool, vals.length = tail.length + gs.length ∧
        gs.foldl step (base y ++ tail) = base y ++ vals ∧
        (gs.map relabel).foldl step (List.ofFn y ++ tail) = List.ofFn y ++ vals := by
    induction gs generalizing tail with
    | nil => exact ⟨tail, by simp, rfl, rfl⟩
    | cons g gs ih =>
      simp only [List.length_cons] at bound ⊢
      let v := g.op.eval (g.inputs.map fun i => (base y ++ tail).getD i false)
      have same : (relabel g).op.eval ((relabel g).inputs.map
          (fun i => (List.ofFn y ++ tail).getD i false)) = v := by
        change g.op.eval ((g.inputs.map wire).map _) = g.op.eval _
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i _
        exact (readWire y tail (by omega) i).symm
      obtain ⟨vals, hlen, ho, hd⟩ := ih (tail ++ [v]) (by simp; omega)
      refine ⟨vals, by simp at hlen; omega, ?_, ?_⟩
      · simpa only [List.foldl_cons, step, ← List.append_assoc, v] using ho
      · simp only [List.map_cons, List.foldl_cons, step, same]
        simpa only [← List.append_assoc] using hd
  have agree (y : Fin 9 → Bool) : D.eval (List.ofFn y) = graph y := by
    obtain ⟨vals, hlen, ho, hd⟩ := run y C.gates [] (by simp)
    simp only [List.append_nil, List.length_nil, Nat.zero_add] at hlen ho hd
    rw [← hbase y]
    change ((C.gates.map relabel).foldl step (List.ofFn y)).getD (wire C.output) false =
      (C.gates.foldl step (base y)).getD C.output false
    rw [ho, hd]
    exact (readWire y vals (by omega) C.output).symm
  have binary := hDelete D hD agree
  let isNot (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
    !PEqualNP.MetaComplexity.SingleLevel.notNot g
  have count (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      (gs.map relabel).countP PEqualNP.MetaComplexity.SingleLevel.notNot +
      gs.countP isNot = gs.length := by
    rw [List.countP_map]
    have neg : (fun g => decide (¬ PEqualNP.MetaComplexity.SingleLevel.notNot g = true)) = isNot := by
      funext g
      change decide (¬ PEqualNP.MetaComplexity.SingleLevel.notNot g = true) =
        !PEqualNP.MetaComplexity.SingleLevel.notNot g
      cases PEqualNP.MetaComplexity.SingleLevel.notNot g <;> rfl
    have total := List.length_eq_countP_add_countP (l := gs) PEqualNP.MetaComplexity.SingleLevel.notNot
    rw [neg] at total
    exact total.symm
  change 13 ≤ (C.gates.map relabel).countP _ at binary
  change C.gates.length ≤ 17 at hsize
  have ct := count C.gates
  have hn : C.gates.countP isNot ≤ 4 := by omega
  obtain ⟨z, hz⟩ := hExtend C hfan hsize hn hbase
  let x : Fin 10 → Bool := ![true, false, z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7]
  have eqv := hcorrect x (by rfl)
  apply hz
  change C.eval (List.ofFn x) = _
  rw [eqv]
  change (true && false || false && z 0 || z 0 && z 1 || z 1 && z 2 ||
    z 2 && true || true && z 3 || false && z 4 || z 0 && z 5 ||
    z 1 && z 6 || z 2 && z 7 || z 3 && z 5 || z 5 && z 7 ||
    z 7 && z 4 || z 4 && z 6 || z 6 && z 3) =
    (z 2 || z 3 || (z 0 && z 1 || (z 1 && z 6 || (z 6 && z 4 ||
      (z 4 && z 7 || (z 7 && z 5 || (z 5 && z 0 || false)))))))
  cases z 2 <;> cases z 3 <;>
    simp only [Bool.false_and, Bool.false_or, Bool.or_false, Bool.true_and,
      Bool.and_true, Bool.true_or, Bool.or_true, Bool.and_comm, Bool.or_assoc,
      Bool.or_left_comm, Bool.or_comm]
