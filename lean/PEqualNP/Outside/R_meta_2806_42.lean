import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A raw companion cannot mask the changed input: for every companion we give both
-- a false and a true companion value on pairs for which the graph distinguishes the input.
-- The unresolved cases are genuine negation and a reader with another computed input.
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_2806_42
    (andLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (negated : let f := (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)
      ∀ (v : Fin 9) (C : Circuit), v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 6]).set v.val (!x v)) ≠ f x)
    (binary : let f := (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)
      ∀ (v : Fin 9) (C : Circuit) (cut i : ℕ) (disj : Bool),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ i → i < cut → cut ≤ 10 + C.size →
        (∀ g ∈ C.gates.take (cut - 10), v.val ∉ g.inputs) →
        (∀ x, let y := Function.update x v false
          f y ≠ f (Function.update x v true) →
            (C.wires (List.ofFn y ++ [y 0 || y 6])).getD i false = !disj) →
        ∃ x : Fin 9 → Bool, let xs := List.ofFn x ++ [x 0 || x 6]
          let b := (C.wires xs).getD i false
          C.eval (xs.set v.val (if disj then x v || b else x v && b)) ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 ≤ (10 : ℕ) + x4.size →               x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not →                 x6.inputs.length ≤ (2 : ℕ) →                   ↑x3 ∈ x6.inputs →                     (∀ x16 ∈ List.take (x5 - (10 : ℕ)) x4.gates, ↑x3 ∉ x16.inputs) →                       ∃ (x17 : Fin (9 : ℕ) → Bool),                         have x18 : List Bool := x2 x17;                         x4.eval (x18.set (↑x3) (x6.op.eval (List.map (fun (x19 : ℕ) => if x19 < x5 then (x4.wires x18).getD x19 Bool.false else Bool.false) x6.inputs))) ≠ x1 x17 := by
  let target (x : Fin 9 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]
  let raw (x : Fin 9 → Bool) (i : ℕ) : Bool :=
    if h : i < 9 then x ⟨i,h⟩ else if i = 9 then x 0 || x 6 else false
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let before (C : Circuit) (cut : ℕ) (x : Fin 9 → Bool) (i : ℕ) : Bool :=
    if i < cut then (C.wires (row x)).getD i false else false
  let rebuilt (C : Circuit) (cut : ℕ) (g : Gate) (x : Fin 9 → Bool) : Bool :=
    g.op.eval (g.inputs.map (before C cut x))
  let AgreeExcept (v : ℕ) (a b : List Bool) : Prop :=
    a.length = b.length ∧ ∀ i, i ≠ v → a.getD i false = b.getD i false
  have rowRead (x : Fin 9 → Bool) (i : ℕ) : (row x).getD i false = raw x i := by
    unfold row raw
    by_cases inside : i < 9
    · rw [dite_eq_left inside, List.getD_append _ _ _ _ (by simpa using inside),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using inside), List.getElem_ofFn]
    · rw [dite_eq_right inside, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      by_cases last : i = 9
      · subst i
        rfl
      · rw [ite_eq_right last]
        exact List.getD_eq_default _ _ (by simp; omega)
  have rowsAgree (x : Fin 9 → Bool) (v : Fin 9) (h0 : v ≠ 0) (h6 : v ≠ 6) :
      AgreeExcept v.val (row (Function.update x v false)) (row (Function.update x v true)) := by
    refine ⟨by simp [row], ?_⟩
    intro i unused
    rw [rowRead, rowRead]
    unfold raw
    split
    · next bound =>
        have ne : (⟨i,bound⟩ : Fin 9) ≠ v := fun e => unused (congrArg Fin.val e)
        simp [Function.update_of_ne ne]
    · simp [Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm h6)]
  have updatedRaw (x : Fin 9 → Bool) (v : Fin 9) (h0 : v ≠ 0) (h6 : v ≠ 6)
      (i : ℕ) (ne : i ≠ v.val) (b : Bool) : raw (Function.update x v b) i = raw x i := by
    unfold raw
    split
    · next bound =>
        have different : (⟨i,bound⟩ : Fin 9) ≠ v := fun e => ne (congrArg Fin.val e)
        exact Function.update_of_ne different _ _
    · simp [Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm h6)]
  have startRaw (C : Circuit) (cut i : ℕ) (x : Fin 9 → Bool) (lo : 10 ≤ cut) (hi : i < 10) :
      before C cut x i = raw x i := by
    unfold before
    rw [ite_eq_left (by omega : i < cut)]
    change (C.gates.foldl step (row x)).getD i false = raw x i
    have preserves (gs : List Gate) (w : List Bool) (n : ℕ) (hn : n < w.length) :
        (gs.foldl step w).getD n false = w.getD n false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hn
    rw [preserves _ _ _ (by simpa [row] using hi), rowRead]
  have beforeVariable (C : Circuit) (cut : ℕ) (x : Fin 9 → Bool) (v : Fin 9) (lo : 10 ≤ cut) :
      before C cut x v.val = x v := by
    rw [startRaw C cut v.val x lo (by have := v.isLt; omega)]
    unfold raw
    rw [dite_eq_left v.isLt]
  have mergeRows (v : ℕ) (a b : List Bool) (agree : AgreeExcept v a b) (value : Bool) :
      a.set v value = b.set v value := by
    apply List.ext_getElem (by simpa only [List.length_set] using agree.1)
    intro i iA iB
    by_cases equal : i = v
    · subst i
      simp
    · have same := agree.2 i equal
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_set] using iA),
        List.getD_eq_getElem _ _ (by simpa only [List.length_set] using iB)] at same
      simpa [List.getElem_set_ne (Ne.symm equal)] using same
  have getDRunLength (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have foldAgree (v : ℕ) (gs : List Gate) (avoid : ∀ g ∈ gs, v ∉ g.inputs)
      (a b : List Bool) (same : AgreeExcept v a b) :
      AgreeExcept v (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact same
    | cons g gs ih =>
      have operands : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) := by
        apply List.map_congr_left
        intro i used
        exact same.2 i (fun eq => avoid g (by simp) (eq ▸ used))
      apply ih (fun h used => avoid h (by simp [used]))
      unfold step
      rw [operands]
      refine ⟨by simp [same.1], ?_⟩
      intro i different
      by_cases ready : i < a.length
      · rw [List.getD_append _ _ _ _ ready, List.getD_append _ _ _ _ (same.1 ▸ ready)]
        exact same.2 i different
      · have past : a.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ past, List.getD_append_right _ _ _ _ (same.1 ▸ past), same.1]
  have beforeAgrees (C : Circuit) (cut : ℕ) (x : Fin 9 → Bool) (v : Fin 9)
      (h0 : v ≠ 0) (h6 : v ≠ 6) (lo : 10 ≤ cut) (hi : cut ≤ 10 + C.size)
      (avoid : ∀ g ∈ C.gates.take (cut-10), v.val ∉ g.inputs) (i : ℕ) (other : i ≠ v.val) :
      before C cut (Function.update x v false) i = before C cut (Function.update x v true) i := by
    unfold before
    by_cases early : i < cut
    · rw [ite_eq_left early, ite_eq_left early]
      let gs := C.gates.take (cut-10)
      let tail := C.gates.drop (cut-10)
      have length (y : Fin 9 → Bool) : (gs.foldl step (row y)).length = cut := by
        have bound : cut-10 ≤ C.gates.length := by change cut ≤ 10 + C.gates.length at hi; omega
        rw [getDRunLength]
        simp [gs, row, Nat.min_eq_left bound]
        omega
      have same := foldAgree v.val gs avoid _ _ (rowsAgree x v h0 h6)
      have split : gs ++ tail = C.gates := List.take_append_drop _ _
      change (C.gates.foldl step (row _)).getD i false = (C.gates.foldl step (row _)).getD i false
      rw [← split, List.foldl_append, List.foldl_append,
        preserve tail _ _ (by rw [length]; exact early), preserve tail _ _ (by rw [length]; exact early)]
      exact same.2 i other
    · simp [early]
  have replacementDifferent (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9)
      (h0 : v ≠ 0) (h6 : v ≠ 6) (x : Fin 9 → Bool)
      (correct : ∀ x, C.eval ((row x).set v.val (rebuilt C cut g x)) = target x)
      (sensitive : target (Function.update x v false) ≠ target (Function.update x v true)) :
      rebuilt C cut g (Function.update x v false) ≠ rebuilt C cut g (Function.update x v true) := by
    intro equal
    have data := mergeRows v.val _ _ (rowsAgree x v h0 h6) (rebuilt C cut g (Function.update x v true))
    have output := congrArg C.eval data
    rw [← equal, correct, equal, correct] at output
    exact sensitive output
  let testAssignment (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

  -- For every companion wire and either desired value, use a pair of rows
  -- that differ only at the reconstructed input and give different answers.
  let samples (b : Bool) : Fin 9 → Fin 10 → ℕ :=
    if b then
      ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 0, 4, 9, 20, 36, 64, 129, 257, 1],
        ![9, 2, 0, 8, 18, 34, 72, 128, 258, 9],
        ![5, 18, 4, 0, 16, 36, 68, 144, 256, 5],
        ![1, 10, 5, 8, 0, 40, 65, 129, 257, 1],
        ![1, 130, 5, 9, 144, 0, 65, 128, 256, 1],
        ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![5, 34, 4, 40, 20, 32, 68, 0, 260, 5],
        ![9, 10, 36, 8, 48, 32, 64, 136, 0, 64]]
    else
      ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![4, 0, 1, 1, 1, 1, 1, 1, 1, 4],
        ![2, 8, 0, 2, 2, 2, 2, 2, 2, 2],
        ![4, 4, 16, 0, 4, 4, 4, 4, 4, 4],
        ![8, 1, 1, 1, 0, 1, 1, 1, 1, 8],
        ![128, 1, 1, 1, 1, 0, 1, 1, 1, 128],
        ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![4, 4, 32, 4, 4, 4, 4, 0, 4, 4],
        ![8, 8, 8, 32, 8, 8, 8, 8, 0, 8]]
  have sensitiveRows : ∀ (b : Bool) (v : Fin 9) (i : Fin 10),
      v ≠ 0 → v ≠ 6 → i.val ≠ v.val →
      let x := testAssignment (samples b v i)
      raw x i.val = b ∧ target (Function.update x v false) ≠ target (Function.update x v true) := by
    decide +kernel
  have rawAndCollapses (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9) (i : Fin 10)
      (h0 : v ≠ 0) (h6 : v ≠ 6) (different : i.val ≠ v.val) (lo : 10 ≤ cut)
      (computed : ∀ x, rebuilt C cut g x = (x v && before C cut x i.val))
      (correct : ∀ x, C.eval ((row x).set v.val (rebuilt C cut g x)) = target x) : False := by
    let x := testAssignment (samples false v i)
    obtain ⟨companion, sensitive⟩ := sensitiveRows false v i h0 h6 different
    have distinguish := replacementDifferent C cut g v h0 h6 x correct sensitive
    have parked (b : Bool) : before C cut (Function.update x v b) i.val = false := by
      rw [startRaw C cut i.val _ lo i.isLt, updatedRaw x v h0 h6 i.val different, companion]
    apply distinguish
    rw [computed, computed, parked false, parked true]
    simp
  have rawOrCollapses (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9) (i : Fin 10)
      (h0 : v ≠ 0) (h6 : v ≠ 6) (different : i.val ≠ v.val) (lo : 10 ≤ cut)
      (computed : ∀ x, rebuilt C cut g x = (x v || before C cut x i.val))
      (correct : ∀ x, C.eval ((row x).set v.val (rebuilt C cut g x)) = target x) : False := by
    let x := testAssignment (samples true v i)
    obtain ⟨companion, sensitive⟩ := sensitiveRows true v i h0 h6 different
    have distinguish := replacementDifferent C cut g v h0 h6 x correct sensitive
    have parked (b : Bool) : before C cut (Function.update x v b) i.val = true := by
      rw [startRaw C cut i.val _ lo i.isLt, updatedRaw x v h0 h6 i.val different, companion]
    apply distinguish
    rw [computed, computed, parked false, parked true]
    simp
  have someSensitive (v : Fin 9) (h0 : v ≠ 0) (h6 : v ≠ 6) :
      ∃ x, target (Function.update x v false) ≠ target (Function.update x v true) := by
    have different : (9 : Fin 10).val ≠ v.val := by have := v.isLt; omega
    exact ⟨_, (sensitiveRows false v 9 h0 h6 different).2⟩
  have argumentShape (xs : List ℕ) (v : ℕ) (short : xs.length ≤ 2) (read : v ∈ xs) :
      xs = [v] ∨ ∃ i, xs = [v,i] ∨ xs = [i,v] := by
    cases xs with
    | nil => simp at read
    | cons a tail =>
      cases tail with
      | nil => exact Or.inl (congrArg (fun i => [i]) (List.mem_singleton.mp read).symm)
      | cons b tail =>
        have length : tail.length = 0 := by simp only [List.length_cons] at short; omega
        have eq := List.length_eq_zero_iff.mp length
        subst tail
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at read
        rcases read with rfl | rfl
        · exact Or.inr ⟨b, Or.inl rfl⟩
        · exact Or.inr ⟨a, Or.inr rfl⟩
  have unaryGate (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9)
      (lo : 10 ≤ cut) (op : g.op = .and ∨ g.op = .or) (args : g.inputs = [v.val]) :
      ∀ x, rebuilt C cut g x = x v := by
    intro x
    rcases op with tag | tag
    · simp only [rebuilt, tag, args, List.map_cons, List.map_nil]
      change (before C cut x v.val && true) = x v
      rw [Bool.and_true, beforeVariable C cut x v lo]
    · simp only [rebuilt, tag, args, List.map_cons, List.map_nil]
      change (before C cut x v.val || false) = x v
      rw [Bool.or_false, beforeVariable C cut x v lo]
  have binaryAnd (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9) (i : ℕ)
      (lo : 10 ≤ cut) (tag : g.op = .and) (args : g.inputs = [v.val,i] ∨ g.inputs = [i,v.val]) :
      ∀ x, rebuilt C cut g x = (x v && before C cut x i) := by
    intro x
    rcases args with shape | shape
    · simp only [rebuilt, tag, shape, List.map_cons, List.map_nil]
      change (before C cut x v.val && (before C cut x i && true)) = _
      rw [Bool.and_true, beforeVariable C cut x v lo]
    · simp only [rebuilt, tag, shape, List.map_cons, List.map_nil]
      change (before C cut x i && (before C cut x v.val && true)) = _
      rw [Bool.and_true, beforeVariable C cut x v lo, Bool.and_comm]
  have binaryOr (C : Circuit) (cut : ℕ) (g : Gate) (v : Fin 9) (i : ℕ)
      (lo : 10 ≤ cut) (tag : g.op = .or) (args : g.inputs = [v.val,i] ∨ g.inputs = [i,v.val]) :
      ∀ x, rebuilt C cut g x = (x v || before C cut x i) := by
    intro x
    rcases args with shape | shape
    · simp only [rebuilt, tag, shape, List.map_cons, List.map_nil]
      change (before C cut x v.val || (before C cut x i || false)) = _
      rw [Bool.or_false, beforeVariable C cut x v lo]
    · simp only [rebuilt, tag, shape, List.map_cons, List.map_nil]
      change (before C cut x i || (before C cut x v.val || false)) = _
      rw [Bool.or_false, beforeVariable C cut x v lo, Bool.or_comm]
  have setOwn (x : Fin 9 → Bool) (v : Fin 9) : (row x).set v.val (x v) = row x := by
    have room : v.val < (row x).length := by have := v.isLt; simp [row]; omega
    have found : (row x)[v.val] = x v := by
      rw [← List.getD_eq_getElem _ false room, rowRead]
      unfold raw
      rw [dite_eq_left v.isLt]
    rw [← found, List.set_getElem_self room]
  have seededCircuit (C : Circuit) (good : FanInTwo C)
      (allRows : ∀ x, C.eval (row x) = target x) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 1 ∧ circuitFun 9 D = target := by
    let D : Circuit := ⟨⟨.or,[0,6]⟩ :: C.gates,C.output⟩
    have fan : FanInTwo D := by
      intro g seen
      rcases List.mem_cons.mp seen with rfl | other
      · simp
      · exact good g other
    refine ⟨D,fan,rfl,?_⟩
    funext x
    have init : step (List.ofFn x) ⟨.or,[0,6]⟩ = row x := by
      change List.ofFn x ++ [x 0 || (x 6 || false)] = row x
      simp [row]
    change (C.gates.foldl step (step (List.ofFn x) ⟨.or,[0,6]⟩)).getD C.output false = target x
    rw [init]
    exact allRows x
  have generalBound (f : (Fin 9 → Bool) → Bool)
      (lower : ∀ c : Circuit, FanInTwo c →
        (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
        circuitFun 9 c = f → 16 ≤ c.size)
      (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = f) :
      15 ≤ c.size := by
    let shiftWire (i : ℕ) : ℕ := if i < 9 then i else i + 1
    let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shiftWire⟩
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let Relation (old new : List Bool) : Prop :=
      9 ≤ old.length ∧ new.length = old.length + 1 ∧
        ∀ i, new.getD (shiftWire i) false = old.getD i false
    have relateInitial (x : Fin 9 → Bool) (value : Bool) :
        Relation (List.ofFn x) (List.ofFn x ++ [value]) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i
      by_cases inside : i < 9
      · simp only [shiftWire, ite_eq_left inside]
        exact List.getD_append _ _ _ _ (by simpa using inside)
      · simp only [shiftWire, ite_eq_right inside]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have relateAppend (old new : List Bool) (value : Bool) (r : Relation old new) :
        Relation (old ++ [value]) (new ++ [value]) := by
      obtain ⟨width, length, same⟩ := r
      refine ⟨by simp; omega, by simp [length], ?_⟩
      intro i
      by_cases oldInput : i < old.length
      · have newInput : shiftWire i < new.length := by
          unfold shiftWire
          split <;> omega
        rw [List.getD_append _ _ _ _ newInput, List.getD_append _ _ _ _ oldInput]
        exact same i
      · have past : old.length ≤ i := by omega
        have shift : shiftWire i = i + 1 := ite_eq_right (by omega)
        have npast : new.length ≤ shiftWire i := by omega
        rw [List.getD_append_right _ _ _ _ npast, List.getD_append_right _ _ _ _ past, shift, length]
        congr 1
        omega
    have relateFold (gs : List Gate) (old new : List Bool) (r : Relation old new) :
        Relation (gs.foldl step old) ((gs.map shiftGate).foldl step new) := by
      induction gs generalizing old new with
      | nil => exact r
      | cons g rest ih =>
        have inputs : ((g.inputs.map shiftWire).map fun i => new.getD i false) =
            (g.inputs.map fun i => old.getD i false) := by
          rw [List.map_map]
          exact List.map_congr_left fun i _ => r.2.2 i
        apply ih (step old g) (step new (shiftGate g))
        unfold step
        change Relation (old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)])
          (new ++ [g.op.eval ((g.inputs.map shiftWire).map fun i => new.getD i false)])
        rw [inputs]
        exact relateAppend old new _ r
    have preserveInitial (gs : List Gate) (wires : List Bool) (i : ℕ) (h : i < wires.length) :
        (gs.foldl step wires).getD i false = wires.getD i false := by
      induction gs generalizing wires with
      | nil => rfl
      | cons gate rest ih =>
        rw [List.foldl_cons, ih (step wires gate) (by simp [step]; omega)]
        unfold step
        exact List.getD_append _ _ _ _ h
    let prefixed (c : Circuit) : Circuit :=
      ⟨⟨.and, [4, 6]⟩ :: c.gates.map shiftGate, shiftWire c.output⟩
    have prefixIsAnd (c : Circuit) (x : Fin 9 → Bool) :
        ((prefixed c).wires (List.ofFn x)).getD 9 false = (x 4 && x 6) := by
      change ((c.gates.map shiftGate).foldl step (step (List.ofFn x) ⟨.and,[4,6]⟩)).getD 9 false = _
      rw [preserveInitial _ _ _ (by simp [step])]
      change (x 4 && (x 6 && true)) = (x 4 && x 6)
      simp
    have prefixComputes (c : Circuit) (x : Fin 9 → Bool) :
        circuitFun 9 (prefixed c) x = circuitFun 9 c x := by
      change ((c.gates.map shiftGate).foldl step (step (List.ofFn x) ⟨.and,[4,6]⟩)).getD (shiftWire c.output) false = _
      exact (relateFold c.gates _ _ (relateInitial x _)).2.2 c.output
    have minimumFromPrefix (f : (Fin 9 → Bool) → Bool)
        (lower : ∀ c : Circuit, FanInTwo c →
          (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
          circuitFun 9 c = f → 16 ≤ c.size)
        (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = f) :
        15 ≤ c.size := by
      have paddedFanIn : FanInTwo (prefixed c) := by
        intro g inside
        rcases List.mem_cons.mp inside with equal | inTail
        · subst g
          simp
        · obtain ⟨source, member, rfl⟩ := List.mem_map.mp inTail
          simpa [shiftGate] using fanin source member
      have paddedComputes : circuitFun 9 (prefixed c) = f := by
        ext x
        rw [prefixComputes, computes]
      have bound := lower (prefixed c) paddedFanIn (prefixIsAnd c) paddedComputes
      change 16 ≤ (Gate.mk .and [4,6] :: c.gates.map shiftGate).length at bound
      simp at bound
      change 15 ≤ c.gates.length
      omega
    exact minimumFromPrefix f lower c fanin computes
  let original := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  change ∀ (v : Fin 9) (C : Circuit) (cut : ℕ) (g : Gate),
    v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ cut → cut ≤ 10 + C.size →
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) → g.inputs.length ≤ 2 → v.val ∈ g.inputs →
    (∀ h ∈ C.gates.take (cut-10), v.val ∉ h.inputs) →
    ∃ x : Fin 9 → Bool, C.eval ((row x).set v.val (rebuilt C cut g x)) ≠ original x
  intro v C cut g h0 h6 fan small lo hi tag short reads prior
  by_contra! allEqual
  have table : original = target := by decide +kernel
  have correct (x : Fin 9 → Bool) :
      C.eval ((row x).set v.val (rebuilt C cut g x)) = target x :=
    (allEqual x).trans (congrFun table x)
  have unchanged (same : ∀ x, rebuilt C cut g x = x v) : False := by
    have allRows (x : Fin 9 → Bool) : C.eval (row x) = target x := by
      have eq := correct x
      rw [same x, setOwn x v] at eq
      exact eq
    obtain ⟨D, good, size, computes⟩ := seededCircuit C fan allRows
    have base : ∀ A : Circuit, FanInTwo A →
        (∀ x : Fin 9 → Bool, (A.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
        circuitFun 9 A = target → 16 ≤ A.size := by
      intro A goodA leading computesA
      exact andLower A goodA leading (computesA.trans table.symm)
    have bound := generalBound target base D good computes
    omega
  have computedOther (i : ℕ) (d : Bool) (afterRaw : 10 ≤ i) (early : i < cut)
      (shape : ∀ x, rebuilt C cut g x =
        if d then (x v || before C cut x i) else (x v && before C cut x i)) :
      False := by
    have permissive (x : Fin 9 → Bool)
        (sensitive : target (Function.update x v false) ≠ target (Function.update x v true)) :
        before C cut (Function.update x v false) i = !d := by
      have stays := beforeAgrees C cut x v h0 h6 lo hi prior i (by have := v.isLt; omega)
      have differs := replacementDifferent C cut g v h0 h6 x correct sensitive
      cases d <;> cases state : before C cut (Function.update x v false) i <;> first
      | rfl
      | exfalso
        apply differs
        rw [shape, shape, ← stays, state]
        simp
    obtain ⟨x, violates⟩ := binary v C cut i d h0 h6 fan small afterRaw early hi prior
      (fun y sensitive => by simpa only [before, ite_eq_left early] using permissive y sensitive)
    apply violates
    have eq := correct x
    rw [shape x] at eq
    simpa only [before, ite_eq_left early] using eq
  rcases tag with andTag | orTag | notTag
  · rcases argumentShape g.inputs v.val short reads with unary | ⟨i, args⟩
    · exact unchanged (unaryGate C cut g v lo (Or.inl andTag) unary)
    have formula := binaryAnd C cut g v i lo andTag args
    by_cases duplicate : i = v.val
    · apply unchanged
      intro x
      rw [formula, duplicate, beforeVariable C cut x v lo, Bool.and_self]
    by_cases isRaw : i < 10
    · exact rawAndCollapses C cut g v ⟨i,isRaw⟩ h0 h6 duplicate lo formula correct
    by_cases early : i < cut
    · exact computedOther i false (by omega) early (by simpa using formula)
    obtain ⟨x, sensitive⟩ := someSensitive v h0 h6
    have discriminate := replacementDifferent C cut g v h0 h6 x correct sensitive
    apply discriminate
    simp only [formula, before, ite_eq_right early, Bool.and_false]
  · rcases argumentShape g.inputs v.val short reads with unary | ⟨i, args⟩
    · exact unchanged (unaryGate C cut g v lo (Or.inr orTag) unary)
    have formula := binaryOr C cut g v i lo orTag args
    by_cases duplicate : i = v.val
    · apply unchanged
      intro x
      rw [formula, duplicate, beforeVariable C cut x v lo, Bool.or_self]
    by_cases isRaw : i < 10
    · exact rawOrCollapses C cut g v ⟨i,isRaw⟩ h0 h6 duplicate lo formula correct
    by_cases early : i < cut
    · exact computedOther i true (by omega) early (by simpa using formula)
    apply unchanged
    intro x
    simp only [formula, before, ite_eq_right early, Bool.or_false]
  · cases args : g.inputs with
    | nil => simp [args] at reads
    | cons i rest =>
      have formula (x : Fin 9 → Bool) : rebuilt C cut g x = !(before C cut x i) := by
        simp only [rebuilt, notTag, args, List.map_cons]
        rfl
      by_cases atInput : i = v.val
      · obtain ⟨x, violates⟩ := negated v C h0 h6 fan small
        apply violates
        have eq := correct x
        rw [formula, atInput, beforeVariable C cut x v lo] at eq
        exact eq
      · obtain ⟨x, sensitive⟩ := someSensitive v h0 h6
        apply replacementDifferent C cut g v h0 h6 x correct sensitive
        rw [formula, formula, beforeAgrees C cut x v h0 h6 lo hi prior i atInput]
