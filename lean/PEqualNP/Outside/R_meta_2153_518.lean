import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2153_518
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 10 → (B.eval (w ++ [false]) != p) = C.eval w)
    (signedBound : ∀ (B : BinaryCircuit) (p : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 4, false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ B.size) :∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C fan first computes second
  let target := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4]
  let step := fun (w : List Bool) (a : Gate) =>
    w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
  have keep (s : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (s.foldl step w).getD i false = w.getD i false := by
    induction s generalizing w with
    | nil => rfl
    | cons a rest ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]
        omega
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil => cases second
  | cons g rest =>
    cases rest with
    | nil => cases second
    | cons h gs =>
      let D : Circuit := ⟨h::gs,o⟩
      have tailFan : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
      have front (x : Fin 9 → Bool) :
          step (List.ofFn x) g = row x := by
        have e := first x
        change ((h::gs).foldl step (step (List.ofFn x) g)).getD 9 false = _ at e
        rw [keep _ _ _ (by simp [step])] at e
        have rd : (step (List.ofFn x) g).getD 9 false =
            g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
          change (List.ofFn x ++ [_]).getD 9 false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp
        rw [rd] at e
        change List.ofFn x ++ [_] = List.ofFn x ++ [_]
        rw [e]
      have correct (x : Fin 9 → Bool) : D.eval (row x) = target x := by
        have e := congrFun computes x
        change ((h::gs).foldl step (step (List.ofFn x) g)).getD o false = target x at e
        rw [front x] at e
        exact e
      have hasNot : 1 ≤ notCount D := by
        have hop : h.op = GateOp.not := Option.some.inj second
        let pred : Gate → Bool := fun a =>
          @decide (a.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
        change 0 < (D.gates.filter pred).length
        rw [← List.countP_eq_length_filter]
        exact List.countP_pos_iff.mpr ⟨h,by simp [D],by simp [pred,hop]⟩
      obtain ⟨B,p,shape,cost,replay⟩ := compile D tailFan
      have bound := signedBound B p shape (fun x => by
        change (B.eval (row x ++ [false]) != p) = target x
        exact (replay (row x) (by simp [row])).trans (correct x))
      have tailBound : 15 ≤ D.size := by omega
      exact Nat.succ_le_succ tailBound