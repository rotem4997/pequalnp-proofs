import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_18509_1
    (sparse : ∀ (C : Circuit) (k : Fin 12), FanInTwo C →
      (∀ g ∈ C.gates, g.op ≠ .not) → C.size ≤ 17 →
      ∃ x : Fin 10 → Bool, (List.ofFn x).count true ≤ 4 ∧
        let W := List.ofFn x ++ [x 0 && x 2]
        let U := W ++ [!W.getD k.val false]
        C.eval U ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (shorter : ∀ (A B : Circuit) (k : Fin 12) (v : Fin (13 + A.size)),
      FanInTwo A → FanInTwo B → (∀ g ∈ A.gates, g.op ≠ .not) →
      A.size + B.size ≤ 16 →
      ∃ x : Fin 10 → Bool,
        let W := List.ofFn x ++ [x 0 && x 2]
        let U := W ++ [!W.getD k.val false]
        let P := A.wires U
        B.eval (P ++ [!P.getD v false]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  have canonical : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) := by
    intro C k legal size
    by_cases none : ∀ g ∈ C.gates, g.op ≠ .not
    · obtain ⟨x, _, hx⟩ := sparse C k legal none size
      exact ⟨x, hx⟩
    · have split (gs : List Gate) (bad : ¬ ∀ g ∈ gs, g.op ≠ .not) :
          ∃ pre ins post, gs = pre ++ ⟨.not, ins⟩ :: post ∧ ∀ g ∈ pre, g.op ≠ .not := by
        induction gs with
        | nil => simp at bad
        | cons g gs ih =>
          by_cases hg : g.op = .not
          · obtain ⟨op, args⟩ := g
            change op = .not at hg
            subst op
            exact ⟨[], args, gs, rfl, by simp⟩
          · have rest : ¬ ∀ a ∈ gs, a.op ≠ .not := by
              intro good
              exact bad (fun a mem => (List.mem_cons.mp mem).elim (fun e => e ▸ hg) (good a))
            obtain ⟨pre, ins, post, eq, hp⟩ := ih rest
            exact ⟨g :: pre, ins, post, by simp [eq], fun a mem =>
              (List.mem_cons.mp mem).elim (fun e => e ▸ hg) (hp a)⟩
      obtain ⟨pre, ins, post, eq, hp⟩ := split C.gates none
      let A : Circuit := ⟨pre, 0⟩
      let B : Circuit := ⟨post, C.output⟩
      have la : FanInTwo A := by
        intro g h
        exact legal g (eq ▸ List.mem_append_left _ h)
      have lb : FanInTwo B := by
        intro g h
        exact legal g (eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h))
      have cap : A.size + B.size ≤ 16 := by
        change pre.length + post.length ≤ 16
        change C.gates.length ≤ 17 at size
        rw [eq,List.length_append,List.length_cons] at size
        omega
      let capWire := 12 + pre.length
      let v : Fin (13 + A.size) := ⟨min (ins.headD capWire) capWire, by
        change min _ (12 + pre.length) < 13 + pre.length
        omega⟩
      obtain ⟨x, hx⟩ := shorter A B k v la lb hp cap
      refine ⟨x, ?_⟩
      let W := List.ofFn x ++ [x 0 && x 2]
      let U := W ++ [!W.getD k.val false]
      let step := fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have lengths (gs : List Gate) (z : List Bool) : (gs.foldl step z).length = z.length + gs.length := by
        induction gs generalizing z with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [step]
          omega
      have width : (A.wires U).length = 12 + pre.length := by
        change (pre.foldl step U).length = _
        rw [lengths]
        simp [U,W]
      have read : (ins.map fun i => (A.wires U).getD i false).headD false = (A.wires U).getD v false := by
        cases ins with
        | nil =>
          change false = (A.wires U).getD (min (12 + pre.length) (12 + pre.length)) false
          rw [min_self]
          rw [List.getD_eq_default _ _ (by omega)]
        | cons i rest =>
          change (A.wires U).getD i false = (A.wires U).getD (min i (12 + pre.length)) false
          by_cases bound : i ≤ 12 + pre.length
          · rw [min_eq_left bound]
          · rw [min_eq_right (le_of_lt (Nat.lt_of_not_ge bound)),
                List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have same : C.eval U = B.eval (A.wires U ++ [!(A.wires U).getD v false]) := by
        unfold Circuit.eval Circuit.wires
        rw [eq,List.foldl_append,List.foldl_cons]
        change (post.foldl step (A.wires U ++ [!((ins.map fun i => (A.wires U).getD i false).headD false)])).getD C.output false =
          (post.foldl step (A.wires U ++ [!(A.wires U).getD v false])).getD C.output false
        rw [read]
      exact fun equal => hx (same.symm.trans equal)
  intro C fan small _
  let n := 11
  let rename (i : ℕ) := if i < n then i else i + 1
  let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
  have legal : FanInTwo D := by
    rintro g hg
    obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan old mem).1,by simpa [mapGate] using (fan old mem).2⟩
  have size : D.size = C.size := List.length_map _
  have align (L : List Bool) (hL : L.length = n) (z : Bool) (tail : List Bool) (i : ℕ) :
      (L ++ z :: tail).getD (rename i) false = (L ++ tail).getD i false := by
    by_cases hi : i < n
    · have before : i < L.length := by omega
      rw [show rename i = i by simp [rename,hi],
        List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ before]
    · have beyond : L.length ≤ i := by omega
      rw [show rename i = i+1 by simp [rename,hi],
        List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ beyond]
      rw [show i + 1 - L.length = (i - L.length) + 1 by omega]
      rfl
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run (L : List Bool) (hL : L.length = n) (z : Bool) (gs : List Gate)
      (tail : List Bool) : ∃ final : List Bool,
      ((gs.map mapGate).foldl step (L ++ z :: tail)) = L ++ z :: final ∧
      (gs.foldl step (L ++ tail)) = L ++ final := by
    induction gs generalizing tail with
    | nil => exact ⟨tail,rfl,rfl⟩
    | cons g gs ih =>
      let out := g.op.eval (g.inputs.map fun i => (L ++ tail).getD i false)
      have val : (mapGate g).op.eval ((mapGate g).inputs.map
          fun i => (L ++ z :: tail).getD i false) = out := by
        simp only [mapGate,List.map_map,Function.comp_def,align L hL z tail,out]
      obtain ⟨final,left,right⟩ := ih (tail ++ [out])
      refine ⟨final,?_,?_⟩
      · simp only [List.map_cons,List.foldl_cons]
        change (gs.map mapGate).foldl step ((L ++ z :: tail) ++ [_]) = _
        rw [val,List.append_assoc]
        exact left
      · simp only [List.foldl_cons]
        change gs.foldl step ((L ++ tail) ++ [out]) = _
        rw [List.append_assoc]
        exact right
  have simulation (L : List Bool) (hL : L.length = n) (z : Bool) :
      D.eval (L ++ [z]) = C.eval L := by
    obtain ⟨final,large,small⟩ := run L hL z C.gates []
    simp only [List.append_nil] at small
    change ((C.gates.map mapGate).foldl step (L ++ [z])).getD (rename C.output) false =
      (C.gates.foldl step L).getD C.output false
    rw [large,small,align L hL]
  obtain ⟨x,bad⟩ := canonical D 10 legal (by omega)
  let L := List.ofFn x ++ [x 0 && x 2]
  have len : L.length = n := by simp [L,n]
  refine ⟨x,?_⟩
  intro good
  apply bad
  exact (simulation L len (!L.getD 10 false)).trans good
