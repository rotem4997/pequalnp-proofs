import Mathlib.Data.List.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3392_529
    (binaryBound : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      13 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (monotoneFrontier : ∀ b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ C : Circuit,
      Monotone2 C → C.size ≤ 13 → ∃ row : Fin 29,
        let mask := ([3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321, 42, 50, 69, 104, 116, 138, 200, 201, 208, 261, 276, 385, 402] : List Nat).getD row.val 0
        let x : Fin 9 → Bool := fun i => mask.testBit i.val
        C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) ≠ decide (row.val < 16))
    (oneInverter : ∀ b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ C : Circuit,
      FanInTwo C → C.size = 13 →
      C.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) = 12 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro b hb C fan budget
  classical
  by_contra noWitness
  have correct (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) :=
    Classical.not_not.mp (fun wrong => noWitness ⟨x, wrong⟩)
  let first : Gate := ⟨.not, [0]⟩
  let second : Gate := ⟨.or, [4, b.val]⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  have dfan : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | h
    · simp [first]
    rcases List.mem_cons.mp h with rfl | h
    · simp [second]
    exact fan g h
  have dcorrect (x : Fin 9 → Bool) : D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    let bits := List.ofFn x
    have read0 : bits.getD 0 false = x 0 := by
      dsimp only [bits]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have read (j : Fin 9) : (bits ++ [!x 0]).getD j.val false = x j := by
      have hj : j.val < bits.length := by simp [bits]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj]
      exact List.getElem_ofFn hj
    have h4 := read (4 : Fin 9)
    change (bits ++ [!x 0]).getD 4 false = x 4 at h4
    let gate1 := first.op.eval (first.inputs.map fun j => bits.getD j false)
    have e1 : gate1 = !x 0 := by
      change (!bits.getD 0 false) = !x 0
      rw [read0]
    change C.eval ((bits ++ [gate1]) ++ [second.op.eval
      (second.inputs.map fun j => (bits ++ [gate1]).getD j false)]) = _
    rw [e1]
    change C.eval ((bits ++ [!x 0]) ++ [(bits ++ [!x 0]).getD 4 false ||
      ((bits ++ [!x 0]).getD b.val false || false)]) = _
    rw [Bool.or_false,h4,read b]
    exact correct x
  let binary (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  have count := binaryBound D dfan dcorrect
  change 13 ≤ (first :: second :: C.gates).countP binary at count
  have hn : binary first = false := rfl
  have ho : binary second = true := rfl
  simp [List.countP_cons, hn, ho] at count
  change C.gates.length ≤ 13 at budget
  have upper := List.countP_le_length (p := binary) (l := C.gates)
  by_cases allBinary : C.gates.countP binary = C.gates.length
  · have mono : Monotone2 C := by
      intro g hg
      obtain ⟨op, arity⟩ := fan g hg
      refine ⟨?_, arity⟩
      rcases op with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have keep := List.countP_eq_length.mp allBinary g hg
        change g.op = .not at h
        simp [binary, h] at keep
    obtain ⟨row, wrong⟩ := monotoneFrontier b hb C mono budget
    let mask := fun r : Fin 29 => ([3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321, 42, 50, 69, 104, 116, 138, 200, 201, 208, 261, 276, 385, 402] : List Nat).getD r.val 0
    let assignment := fun (r : Fin 29) (i : Fin 9) => (mask r).testBit i.val
    have answers : ∀ r : Fin 29, (let x := assignment r; ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) = decide (r.val < 16) := by
      decide +kernel
    exact wrong ((correct (assignment row)).trans (answers row))
  · have exactSize : C.size = 13 := by change C.gates.length = 13; omega
    have exactBinary : C.gates.countP binary = 12 := by omega
    obtain ⟨x, wrong⟩ := oneInverter b hb C fan exactSize exactBinary
    exact wrong (correct x)
