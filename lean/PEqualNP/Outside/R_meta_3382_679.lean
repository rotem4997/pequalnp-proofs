import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_3382_679
    (masked : ∀ (C D : Circuit) (a b : ℕ) (v : Fin 7) (x y : Fin 7 → Bool),
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) C.gates D.gates →
      (∀ j ≠ v, x j = y j) →
      (∀ g ∈ C.gates, v.val ∈ g.inputs →
        g.op = .or ∧ ∃ j : Fin 7, j ≠ v ∧ j.val ∈ g.inputs ∧ x j = true) →
      C.output ≠ v.val →
      (D.wires (true :: List.ofFn x)).getD (C.output+1) false =
        (D.wires (true :: List.ofFn y)).getD (C.output+1) false)
    (unmasked :
      let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,36] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
      ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → C.size = 11 → circuitFun 7 C = f →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) C.gates D.gates →
      (∀ x, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (f x || x 2)) →
      (∀ x : Fin 7 → Bool, x 2 = false → f x = false →
        ¬ (∀ g ∈ C.gates, (2 : ℕ) ∈ g.inputs →
          g.op = .or ∧ ∃ j : Fin 7, j ≠ 2 ∧ j.val ∈ g.inputs ∧ x j = true)) →
      (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length < 2) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fan size base edits modified
  classical
  have out : C.output ≠ 2 := by
    intro eq
    let t : Fin 7 → Bool := fun i => decide (i = 2)
    have bad := congrFun base t
    change (C.wires (List.ofFn t)).getD C.output false = false at bad
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (step w g)]
        · exact List.getD_append _ _ _ _ hi
        · simp only [step,List.length_append,List.length_singleton]
          omega
    change (C.gates.foldl step (List.ofFn t)).getD C.output false = false at bad
    rw [eq, keep _ _ _ (by simp)] at bad
    change true = false at bad
    exact Bool.noConfusion bad
  apply unmasked C D a b fan size base edits modified
  intro x zero negative readers
  let y := Function.update x (2 : Fin 7) true
  have agree (j : Fin 7) (hj : j ≠ 2) : x j = y j :=
    (Function.update_of_ne hj true x).symm
  have same := masked C D a b 2 x y edits agree readers out
  change f x = false at negative
  rw [modified, modified, negative, zero] at same
  have yes : y 2 = true := Function.update_self _ _ _
  rw [yes] at same
  simp at same
