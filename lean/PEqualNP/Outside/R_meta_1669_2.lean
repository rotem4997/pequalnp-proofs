import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1669_2
    (h_full : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
          (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
          (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
          (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (h_slice : ∀ g : (Fin 9 → Bool) → Bool,
      (∀ x : Fin 9 → Bool, (x 0 && x 3) = false → g x =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 g 13)
    (h_restrict : ∀ f : (Fin 10 → Bool) → Bool,
      PEqualNP.MetaComplexity.HasCircuitSize 10 f 14 →
      (∃ x y : Fin 9 → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false)) →
      PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x => f (Fin.snoc x false)) 13 ∨
        ((∀ x : Fin 9 → Bool, f (Fin.snoc x false) = f (Fin.snoc x true)) ∧
          PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x => f (Fin.snoc x false)) 14)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  by_contra! small
  let target (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
          (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
          (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
          (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    contradiction
  | cons a tail =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail,out⟩
    let f := PEqualNP.MetaComplexity.circuitFun 10 D
    have suffix (x : Fin 9 → Bool) : f (Fin.snoc x (x 0 && x 3)) = target x := by
      have h := first x
      change (tail.foldl step (step (List.ofFn x) a)).getD 9 false = _ at h
      rw [keep tail _ 9 (by simp [step])] at h
      simp only [step,List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ 9),
        List.length_ofFn,Nat.sub_self] at h
      have val : a.op.eval (a.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 3) := h
      have truth := congrFun computes x
      change (tail.foldl step (List.ofFn x ++ [_])).getD out false = target x at truth
      change (tail.foldl step (List.ofFn (Fin.snoc x (x 0 && x 3)))).getD out false = _
      have snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
          List.ofFn (Fin.snoc y b : Fin (n+1) → Bool) = List.ofFn y ++ [b] := by
        rw [List.ofFn_succ']
        simp
      rw [snoc]
      simpa only [val] using truth
    have bounded : PEqualNP.MetaComplexity.HasCircuitSize 10 f 14 := by
      refine ⟨D,(fun g hg => fan g (List.mem_cons_of_mem _ hg)),?_,fun _ => rfl⟩
      change tail.length ≤ 14
      change (a :: tail).length < 16 at small
      simp only [List.length_cons] at small
      omega
    have slice (x : Fin 9 → Bool) (off : (x 0 && x 3) = false) :
        f (Fin.snoc x false) = target x := by simpa only [off] using suffix x
    let zero : Fin 9 → Bool := fun _ => false
    let edge : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have varies : f (Fin.snoc zero false) ≠ f (Fin.snoc edge false) := by
      rw [slice zero rfl,slice edge (by decide)]
      decide
    rcases h_restrict f bounded ⟨zero,edge,varies⟩ with smaller | ⟨ignore,full⟩
    · exact h_slice _ slice smaller
    · have agree (x : Fin 9 → Bool) : f (Fin.snoc x false) = target x := by
        have e := suffix x
        cases b : (x 0 && x 3) <;> rw [b] at e
        · exact e
        · exact (ignore x).trans e
      rw [show (fun x => f (Fin.snoc x false)) = target from funext agree] at full
      exact h_full full
