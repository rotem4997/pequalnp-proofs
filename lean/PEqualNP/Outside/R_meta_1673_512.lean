import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_1673_512
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 10 → (B.eval (w ++ [false]) != p) = C.eval w)
    (signedBound : ∀ (B : BinaryCircuit) (p : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 1, false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ B.size)
    (monotoneBound : ∀ C : Circuit, Monotone2 C →
      (∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 1]) = true) →
      (∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 1]) = false) →
      15 ≤ C.size) :∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  let target := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 1]
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
  | nil =>
    have h := first (fun _ => true)
    change false = true at h
    exact Bool.noConfusion h
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    have tailFan : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have front (x : Fin 9 → Bool) :
        step (List.ofFn x) g = row x := by
      have h := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [keep _ _ _ (by simp [step])] at h
      have hread : (step (List.ofFn x) g).getD 9 false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
        change (List.ofFn x ++ [_]).getD 9 false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      rw [hread] at h
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      rw [h]
    have correct (x : Fin 9 → Bool) : D.eval (row x) = target x := by
      have e := congrFun computes x
      change (gs.foldl step (step (List.ofFn x) g)).getD o false = target x at e
      rw [front x] at e
      exact e
    by_cases hzero : notCount D = 0
    · have monotone : Monotone2 D := by
        intro a ha
        have hno : a.op ≠ GateOp.not := by
          intro e
          have hm : a ∈ D.gates.filter (fun v : Gate =>
              @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) :=
            List.mem_filter.mpr ⟨ha, by simp [e]⟩
          have hnil : D.gates.filter (fun v : Gate =>
              @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) = [] :=
            List.eq_nil_of_length_eq_zero hzero
          rw [hnil] at hm
          exact List.not_mem_nil hm
        have hf := tailFan a ha
        rcases hf.1 with h | h | h
        · exact ⟨Or.inl h,hf.2⟩
        · exact ⟨Or.inr h,hf.2⟩
        · exact (hno h).elim
      have bound := monotoneBound D monotone (by
        intro m hm
        change D.eval (row (fun i => m.testBit i.val)) = true
        rw [correct]
        have tests : ∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ),
            target (fun i => m.testBit i.val) = true := by decide +kernel
        exact tests m hm) (by
        intro m hm
        change D.eval (row (fun i => m.testBit i.val)) = false
        rw [correct]
        have tests : ∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ),
            target (fun i => m.testBit i.val) = false := by decide +kernel
        exact tests m hm)
      exact Nat.succ_le_succ bound
    · obtain ⟨B,p,shape,cost,replay⟩ := compile D tailFan
      have bound := signedBound B p shape (fun x => by
        change (B.eval (row x ++ [false]) != p) = target x
        exact (replay (row x) (by simp [row])).trans (correct x))
      have tailBound : 15 ≤ D.size := by omega
      exact Nat.succ_le_succ tailBound
