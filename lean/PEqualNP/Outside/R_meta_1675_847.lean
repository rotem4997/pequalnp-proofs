import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize the first gate and the output, then solve the fixed-slot populations.
theorem PEqualNP.Outside.R_meta_1675_847 :
    (∀ C : Circuit, FanInTwo C → C.size ≤ 15 →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      9 ≤ C.output → C.output < 9 + C.gates.length →
      ∃ D : Circuit, D.gates.length = 15 ∧ D.output = 23 ∧ D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
        (∀ (j : ℕ) (hj : j < D.gates.length),
          let g := D.gates[j]
          let fit := fun a : ℕ => a < 9 + j ∨ a = 24
          let rank := fun a : ℕ => if a < 9 then a else if a = 24 then 9 else a + 1
          g = ⟨.and, []⟩ ∨ (∃ a, fit a ∧ g = ⟨.not, [a]⟩) ∨
            ∃ a b, fit a ∧ fit b ∧ rank a ≤ rank b ∧
              (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)) ∧ circuitFun 9 D = circuitFun 9 C) →
    (∀ D : Circuit, D.gates.length = 15 ∧ D.output = 23 ∧ D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
        (∀ (j : ℕ) (hj : j < D.gates.length),
          let g := D.gates[j]
          let fit := fun a : ℕ => a < 9 + j ∨ a = 24
          let rank := fun a : ℕ => if a < 9 then a else if a = 24 then 9 else a + 1
          g = ⟨.and, []⟩ ∨ (∃ a, fit a ∧ g = ⟨.not, [a]⟩) ∨
            ∃ a b, fit a ∧ fit b ∧ rank a ≤ rank b ∧
              (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)) →
      (D.gates.countP fun g => g.op.eval [false]) = 0 →
      circuitFun 9 D ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ D : Circuit, D.gates.length = 15 ∧ D.output = 23 ∧ D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
        (∀ (j : ℕ) (hj : j < D.gates.length),
          let g := D.gates[j]
          let fit := fun a : ℕ => a < 9 + j ∨ a = 24
          let rank := fun a : ℕ => if a < 9 then a else if a = 24 then 9 else a + 1
          g = ⟨.and, []⟩ ∨ (∃ a, fit a ∧ g = ⟨.not, [a]⟩) ∨
            ∃ a b, fit a ∧ fit b ∧ rank a ≤ rank b ∧
              (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)) →
      (D.gates.countP fun g => g.op.eval [false]) = 1 →
      circuitFun 9 D ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ D : Circuit, D.gates.length = 15 ∧ D.output = 23 ∧ D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
        (∀ (j : ℕ) (hj : j < D.gates.length),
          let g := D.gates[j]
          let fit := fun a : ℕ => a < 9 + j ∨ a = 24
          let rank := fun a : ℕ => if a < 9 then a else if a = 24 then 9 else a + 1
          g = ⟨.and, []⟩ ∨ (∃ a, fit a ∧ g = ⟨.not, [a]⟩) ∨
            ∃ a b, fit a ∧ fit b ∧ rank a ≤ rank b ∧
              (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)) →
      2 ≤ (D.gates.countP fun g => g.op.eval [false]) →
      circuitFun 9 D ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  classical
  intro normalize monotone one many C fan anchor correct
  by_contra hsize
  have small : C.size ≤ 15 := by omega
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih]; simp [step]; omega
  have read (gs : List Gate) (w : List Bool) (i : ℕ) (before : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ before
  have lower : 9 ≤ C.output := by
    by_contra h
    have lt : C.output < 9 := by omega
    let z : Fin 9 := ⟨C.output, lt⟩
    let y : Fin 9 → Bool := fun v => decide (v = z)
    have one : (List.ofFn y).getD C.output false = true := by
      rw [List.getD_eq_getElem _ _ (by simpa using lt), List.getElem_ofFn]
      simp [y, z]
    have zero : (fun z : Fin 9 => (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun v => decide (v = z))) z = false := by
      have hzero : ∀ w : Fin 9, (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun v => decide (v = w)) = false := by decide
      exact hzero z
    have out := congrFun correct y
    change (C.gates.foldl step (List.ofFn y)).getD C.output false = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) y at out
    rw [read _ _ _ (by simpa using lt), one] at out
    exact Bool.noConfusion (out.trans zero)
  have upper : C.output < 9 + C.gates.length := by
    by_contra h
    let y : Fin 9 → Bool := fun _ => true
    have out := congrFun correct y
    change (C.gates.foldl step (List.ofFn y)).getD C.output false = true at out
    rw [List.getD_eq_default _ _ (by simpa [len] using Nat.le_of_not_gt h)] at out
    exact Bool.noConfusion out
  obtain ⟨D, lenD, outD, first, slots, equal⟩ := normalize C fan small anchor lower upper
  have shape := And.intro lenD (And.intro outD (And.intro first slots))
  have normalized := equal.trans correct
  let count := D.gates.countP fun g => g.op.eval [false]
  by_cases zero : count = 0
  · exact monotone D shape zero normalized
  by_cases single : count = 1
  · exact one D shape single normalized
  have two : 2 ≤ count := by omega
  exact many D shape two normalized
