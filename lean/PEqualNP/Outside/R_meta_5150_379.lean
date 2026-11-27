import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5150_379
    (coarse : ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      15 ≤ C.size ∧ 13 + PEqualNP.NotBracket.notCount C ≤ C.size)
    (zeroNot : ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      C.size = 15 → PEqualNP.NotBracket.notCount C = 0 → False)
    (oneNot : ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      C.size = 15 → PEqualNP.NotBracket.notCount C = 1 → False)
    (twoNot : ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2)) →
      C.size = 15 → PEqualNP.NotBracket.notCount C = 2 → False) :
    ∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by



  let oldToBase (v i : Fin 10) : Fin 10 :=
    (![![9,7,5,8,6,4,2,0,3,1],
        ![6,9,7,5,8,1,4,2,0,3],
        ![8,6,9,7,5,3,1,4,2,0],
        ![5,8,6,9,7,0,3,1,4,2],
        ![7,5,8,6,9,2,0,3,1,4],
        ![4,0,1,2,3,9,5,6,7,8],
        ![3,4,0,1,2,8,9,5,6,7],
        ![2,3,4,0,1,7,8,9,5,6],
        ![1,2,3,4,0,6,7,8,9,5],
        ![0,1,2,3,4,5,6,7,8,9]] : Fin 10 → Fin 10 → Fin 10) v i

  let extend (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
    (List.ofFn x).getD (oldToBase v i).val false

  let edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

  let baseEdge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  have deleted (v : Fin 10) : oldToBase v v = 9 := by
    fin_cases v <;> decide

  have extend_deleted (v : Fin 10) (x : Fin 9 → Bool) : extend v x v = false := by
    unfold extend
    rw [deleted]
    apply List.getD_eq_default
    simp

  have edge_extend (v : Fin 10) (x : Fin 9 → Bool) : edge (extend v x) = baseEdge x := by
    suffices ∀ a b c d e f g h i : Bool,
        edge (extend v ![a,b,c,d,e,f,g,h,i]) = baseEdge ![a,b,c,d,e,f,g,h,i] by
      have hx : (![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] : Fin 9 → Bool) = x := by
        funext j
        fin_cases j <;> rfl
      simpa only [hx] using this (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    intro a b c d e f g h i
    fin_cases v <;> simp [edge, baseEdge, extend, oldToBase, List.getD_eq_getElem?_getD] <;> ac_rfl

  let wire (v : Fin 10) (sentinel i : ℕ) : ℕ :=
    if h : i < 10 then
      let j := (oldToBase v ⟨i, h⟩).val
      if j < 9 then j else sentinel
    else i - 1

  let mappedGate (v : Fin 10) (sentinel : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wire v sentinel)⟩

  let stepWire (xs : List Bool) (g : Gate) : List Bool :=
    xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

  have getD_snoc (xs : List Bool) (b : Bool) (i : ℕ) :
      (xs ++ [b]).getD i false = if i = xs.length then b else xs.getD i false := by
    by_cases h₁ : i < xs.length
    · rw [if_neg (Nat.ne_of_lt h₁)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h₁]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      by_cases h₂ : i = xs.length
      · simp [h₂]
      · rw [if_neg h₂]
        have hz : 1 ≤ i - xs.length := by omega
        have hdefault := List.getD_eq_default false (l := xs) (n := i) (by omega)
        rw [hdefault]
        cases hi : i - xs.length <;> simp_all

  have wire_new (v : Fin 10) (limit i : ℕ) (hi : 10 ≤ i) :
      wire v limit i = i - 1 := by simp [wire, Nat.not_lt.mpr hi]

  have binding (v : Fin 10) (limit : ℕ) (xs ys : List Bool) (gs : List Gate)
      (hmin : 10 ≤ xs.length) (hlen : xs.length = ys.length + 1)
      (hlimit : ys.length + gs.length ≤ limit)
      (hrel : ∀ i, xs.getD i false = ys.getD (wire v limit i) false) :
      ∀ i, (gs.foldl stepWire xs).getD i false =
        ((gs.map (mappedGate v limit)).foldl stepWire ys).getD (wire v limit i) false := by
    induction gs generalizing xs ys with
    | nil => exact hrel
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hv : g.op.eval (g.inputs.map fun i => xs.getD i false) =
          (mappedGate v limit g).op.eval ((mappedGate v limit g).inputs.map fun i => ys.getD i false) := by
        simp only [mappedGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hrel i
      apply ih
      · simp [stepWire]; omega
      · simp [stepWire, hlen]
      · simp [stepWire] at *; omega
      · intro i
        unfold stepWire
        rw [getD_snoc, getD_snoc, hv, hrel i]
        have he : i = xs.length ↔ wire v limit i = ys.length := by
          by_cases hi : i < 10
          · have hx : i ≠ xs.length := by omega
            have hlo : ys.length < limit := by
              simp only [List.length_cons] at hlimit
              omega
            have hy : wire v limit i ≠ ys.length := by
              unfold wire
              rw [dite_eq_left hi]
              dsimp only
              split <;> omega
            simp only [hx, hy]
          · rw [wire_new v limit i (by omega)]
            omega
        simp only [he]

  have input_binding (v : Fin 10) (limit : ℕ) (x : Fin 9 → Bool) (hlimit : 9 ≤ limit) (i : ℕ) :
      (List.ofFn (extend v x)).getD i false = (List.ofFn x).getD (wire v limit i) false := by
    by_cases hi : i < 10
    · simp only [wire, dif_pos hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi,
        Option.getD_some, extend]
      split
      · rfl
      · have hj : 9 ≤ (oldToBase v ⟨i, hi⟩).val := by omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Nat.not_lt.mpr hj, Nat.not_lt.mpr hlimit]
    · rw [wire_new v limit i (by omega)]
      have hj : ¬ i - 1 < 9 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, hj]

  let restrictCircuit (v : Fin 10) (C : Circuit) : Circuit :=
    ⟨C.gates.map (mappedGate v (10 + C.size)), wire v (10 + C.size) C.output⟩

  have restrict_eval (v : Fin 10) (C : Circuit) (x : Fin 9 → Bool) :
      (restrictCircuit v C).eval (List.ofFn x) = C.eval (List.ofFn (extend v x)) := by
    exact (binding v (10 + C.size) (List.ofFn (extend v x)) (List.ofFn x) C.gates
      (by simp) (by simp) (by delta Circuit.size; simp) (input_binding v _ x (by omega)) C.output).symm

  have restrict_fan (v : Fin 10) (C : Circuit) (h : FanInTwo C) : FanInTwo (restrictCircuit v C) := by
    intro g hg
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
    simpa [mappedGate] using h old hold

  let complement (C : Circuit) : Circuit :=
    ⟨C.gates ++ [⟨.not, [C.output]⟩], 9 + C.size⟩

  have complement_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (complement C) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h g hg
    · obtain rfl := List.mem_singleton.mp hg
      simp

  have fold_length (gs : List Gate) (xs : List Bool) :
      (gs.foldl stepWire xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega

  have complement_eval (C : Circuit) (x : Fin 9 → Bool) :
      (complement C).eval (List.ofFn x) = !(C.eval (List.ofFn x)) := by
    unfold complement Circuit.eval Circuit.wires
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (((C.gates.foldl stepWire (List.ofFn x)) ++
      [!(C.gates.foldl stepWire (List.ofFn x)).getD C.output false]).getD (9 + C.size) false) = _
    rw [getD_snoc, fold_length]
    delta Circuit.size
    simp
    rfl

  intro v C sign legal budget
  change ∃ x : Fin 10 → Bool, x v = false ∧
    (if sign = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) ≠ edge x
  by_contra! noWitness
  let D := if sign = true then complement (restrictCircuit v C) else restrictCircuit v C
  have fanD : FanInTwo D := by
    cases sign
    · simpa [D] using restrict_fan v C legal
    · simpa [D] using complement_fan (restrictCircuit v C) (restrict_fan v C legal)
  have sizeD : D.size ≤ 15 := by
    cases sign <;> delta Circuit.size at budget ⊢ <;>
      simpa [D, complement, restrictCircuit] using budget
  have correctD : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = baseEdge x := by
    intro x
    have agrees := noWitness (extend v x) (extend_deleted v x)
    rw [edge_extend v x] at agrees
    cases sign
    · change (restrictCircuit v C).eval (List.ofFn x) = _
      rw [restrict_eval]
      exact agrees
    · change (complement (restrictCircuit v C)).eval (List.ofFn x) = _
      rw [complement_eval, restrict_eval]
      exact agrees
  have graphD : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => y e.1 && y e.2) := by
    intro y
    simpa [baseEdge, Bool.or_assoc] using correctD y
  obtain ⟨floor, hnots⟩ := coarse D fanD graphD
  have exactSize : D.size = 15 := by omega
  have fewNot : PEqualNP.NotBracket.notCount D ≤ 2 := by omega
  interval_cases hc : PEqualNP.NotBracket.notCount D
  · exact zeroNot D fanD graphD exactSize hc
  · exact oneNot D fanD graphD exactSize hc
  · exact twoNot D fanD graphD exactSize hc
