import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first premise has the statement of L_meta_2048.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2948_717
    (forbidTwo : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → (2 : ℕ) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
    (monotoneTail : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), Monotone2 x1 → x1.size = (13 : ℕ) → ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)), !(x5 (0 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)))]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (0 : ℕ) < x1.size → x1.size ≤ (13 : ℕ) → ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)), !(x5 (0 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)))]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C hfan _ hsize
  by_cases needed : C.size < 13 ∨ ∃ g ∈ C.gates, g.op = .not
  · by_contra hbad
    let f (x : Fin 9 → Bool) : Bool :=
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
      x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    let pin (x : Fin 9 → Bool) := x 0 && x 2
    let input (x : Fin 9 → Bool) := List.ofFn x ++ [pin x, !(pin x)]
    have computes (x : Fin 9 → Bool) : C.eval (input x) = f x :=
      Classical.byContradiction (fun hne => hbad ⟨x, hne⟩)
    let first : Gate := ⟨.and, [0, 2]⟩
    let second : Gate := ⟨.not, [9]⟩
    let padding := List.replicate (13 - C.size) (⟨.not, []⟩ : Gate)
    let D : Circuit := ⟨first :: second :: (C.gates ++ padding), C.output⟩
    have fanD : FanInTwo D := by
      intro g hg
      change g ∈ first :: second :: (C.gates ++ padding) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inl rfl, by decide⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan g hg
      · have heq : g = (⟨.not, []⟩ : Gate) := (List.mem_replicate.mp hg).2
        subst g
        exact ⟨Or.inr (Or.inr rfl), by decide⟩
    have sizeD : D.size = 15 := by
      change (first :: second :: (C.gates ++ padding)).length = 15
      simp only [padding, List.length_cons, List.length_append, List.length_replicate]
      change C.gates.length ≤ 13 at hsize
      change C.gates.length + (13 - C.gates.length) + 1 + 1 = 15
      omega
    let isNot (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op
    have notCount : 2 ≤ D.gates.countP isNot := by
      change 2 ≤ (first :: second :: (C.gates ++ padding)).countP isNot
      rw [List.countP_cons, List.countP_cons, List.countP_append]
      have padCount : padding.countP isNot = 13 - C.size := by
        change (List.replicate (13 - C.size) (⟨.not, []⟩ : Gate)).countP isNot = _
        rw [List.countP_replicate]
        rfl
      change 2 ≤ C.gates.countP isNot + padding.countP isNot + 1 + 0
      rw [padCount]
      rcases needed with spare | ⟨g, hg, hn⟩
      · omega
      · have positive : 0 < C.gates.countP isNot :=
          List.countP_pos_iff.mpr ⟨g, hg, by
            change GateOp.rec false false true (fun _ => false) false g.op = true
            rw [hn]⟩
        omega
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have lengthFold (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (step w g)]
        · exact List.getD_append _ _ _ _ hi
        · simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
    have firstStep (x : Fin 9 → Bool) :
        step (List.ofFn x) first = List.ofFn x ++ [pin x] := by
      have read (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have read0 : (List.ofFn x).getD 0 false = x 0 := read 0
      have read2 : (List.ofFn x).getD 2 false = x 2 := read 2
      change List.ofFn x ++ [[(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false].all id] = _
      rw [read0, read2]
      simp only [pin, List.all_cons, List.all_nil, id, Bool.and_true]
    have pinRead (x : Fin 9 → Bool) :
        (List.ofFn x ++ [pin x]).getD 9 false = pin x := by
      rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
      rfl
    have secondStep (x : Fin 9 → Bool) :
        step (List.ofFn x ++ [pin x]) second = input x := by
      change (List.ofFn x ++ [pin x]) ++ [!((List.ofFn x ++ [pin x]).getD 9 false)] = _
      rw [pinRead, List.append_assoc]
      rfl
    have firstWire (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = pin x := by
      change (((second :: (C.gates ++ padding)).foldl step (step (List.ofFn x) first))).getD 9 false = _
      rw [firstStep, preserve, pinRead]
      simp
    have wires (x : Fin 9 → Bool) :
        D.wires (List.ofFn x) = padding.foldl step (C.wires (input x)) := by
      change (C.gates ++ padding).foldl step (step (step (List.ofFn x) first) second) =
        padding.foldl step (C.gates.foldl step (input x))
      rw [firstStep, secondStep, List.foldl_append]
    have wireLength (x : Fin 9 → Bool) : (C.wires (input x)).length = 11 + C.size := by
      change (C.gates.foldl step (input x)).length = 11 + C.gates.length
      rw [lengthFold]
      simp [input]
    have valid : C.output < 11 + C.size := by
      by_contra! h
      have top := computes (fun _ => true)
      change (C.wires (input (fun _ => true))).getD C.output false = true at top
      rw [List.getD_eq_default _ _ (by rwa [wireLength])] at top
      contradiction
    apply forbidTwo D fanD firstWire sizeD notCount
    funext x
    change (D.wires (List.ofFn x)).getD C.output false = f x
    rw [wires, preserve]
    · exact computes x
    · rwa [wireLength]
  · have full : C.size = 13 := by
      have h := fun hlt : C.size < 13 => needed (Or.inl hlt)
      omega
    apply monotoneTail C _ full
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    rcases hop with ha | ho | hn
    · exact ⟨Or.inl ha, hlen⟩
    · exact ⟨Or.inr ho, hlen⟩
    · exact False.elim (needed (Or.inr ⟨g, hg, hn⟩))
