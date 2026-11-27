import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- Join the two circuit segments across the selected negation.
-- The second OR has either at most two raw inputs in its support or support of the form {0,4,a}.
-- In the first case the joined circuit already has a negation, so the monotone case drops out.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3410_31
    (mask : ∀ ins : List ℕ, ins.length ≤ 2 →
      ∃ T : Finset (Fin 9), (T.card ≤ 2 ∨ ∃ a : Fin 9, T = {0,4,a}) ∧
        ∀ x : Fin 9 → Bool,
          GateOp.or.eval (ins.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
            decide (∃ a ∈ T, x a = true))
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.size - notCount C)
    (signedBound : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card ≤ 2 →
      1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size)
    (triple : ∀ (D : Circuit) (a : Fin 9), FanInTwo D →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) =
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 14 ≤ D.size) :
  ∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x2.size + x3.size ≤ (12 : ℕ) →           x2.output ≤ (24 : ℕ) →             x3.output ≤ (24 : ℕ) →               (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) →                 ∃ (x11 : Fin (9 : ℕ) → Bool),                   have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))];                   have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]);                   x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by

  intro pins P Q hlen mono fanQ cost _ _ _
  by_contra! correct
  let negGate : Gate := ⟨.not,[P.output]⟩
  let D : Circuit := ⟨P.gates ++ negGate :: Q.gates, Q.output⟩
  have legal : FanInTwo D := by
    intro g hg
    change g ∈ P.gates ++ negGate :: Q.gates at hg
    rcases List.mem_append.mp hg with hp | hq
    · obtain ⟨op, arity⟩ := mono g hp
      exact ⟨(show g.op = .and ∨ g.op = .or ∨ g.op = .not from
        (show g.op = .and ∨ g.op = .or from op).elim Or.inl (fun h => Or.inr (Or.inl h))),arity⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inr (Or.inr rfl),by change 1 ≤ 2; decide⟩
      · exact fanQ g hq
  have sizeD : D.size = P.size + Q.size + 1 := by
    change (P.gates ++ negGate :: Q.gates).length = P.gates.length + Q.gates.length + 1
    simp only [List.length_append,List.length_cons]
    omega
  have positive : 1 ≤ notCount D := by
    let isNot := fun (g : Gate) => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
    change 1 ≤ ((P.gates ++ negGate :: Q.gates).filter isNot).length
    have h : isNot negGate = true := by rfl
    simp only [List.filter_append,List.filter_cons_of_pos h,List.length_append,List.length_cons]
    omega
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have join (w : List Bool) : D.eval w =
      Q.eval (P.wires w ++ [!(P.wires w).getD P.output false]) := by
    change ((P.gates ++ negGate :: Q.gates).foldl step w).getD Q.output false = _
    rw [List.foldl_append]
    rfl
  let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let F (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
    List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  obtain ⟨T,classification,fromMask⟩ := mask (pins.map Fin.val) (by simpa only [List.length_map] using hlen)
  have computes (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T, x a = true)]) = F x := by
    have hx := not_ne_iff.mp (correct x)
    change Q.eval (P.wires (row x ++ [GateOp.or.eval (pins.map fun i => (row x).getD i.val false)]) ++
      [!(P.wires (row x ++ [GateOp.or.eval (pins.map fun i => (row x).getD i.val false)])).getD P.output false]) = _ at hx
    rw [← join] at hx
    have hm := fromMask x
    change GateOp.or.eval ((pins.map Fin.val).map fun i => (row x).getD i false) = _ at hm
    simp only [List.map_map,Function.comp_def] at hm
    rw [hm] at hx
    simpa only [row,F,List.append_assoc,List.singleton_append,List.any_cons,List.any_nil,Bool.or_assoc,Bool.or_false] using hx
  have lower : 14 ≤ D.size := by
    rcases classification with hs | ⟨a,rfl⟩
    · by_cases low : notCount D ≤ 2
      · exact signedBound D T legal hs positive low computes
      · let first : Gate := ⟨.or, [0,4]⟩
        let second : Gate := ⟨.or, T.toList.map Fin.val⟩
        let full : Circuit := ⟨first :: second :: D.gates, D.output⟩
        have legalD : FanInTwo full := by
          intro g hg
          change g ∈ first :: second :: D.gates at hg
          simp only [List.mem_cons] at hg
          rcases hg with rfl | rfl | hg
          · simp [first]
          · exact ⟨by simp [second], by simpa [second] using hs⟩
          · exact legal g hg
        have value (x : Fin 9 → Bool) :
            full.eval (List.ofFn x) = D.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) := by
          let step := fun (w : List Bool) (g : Gate) =>
            w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
          have firstValue : step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
            change List.ofFn x ++ [([(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false].any id)] = _
            simp [List.getD_eq_getElem?_getD]
          have read (i : Fin 9) : (List.ofFn x ++ [x 0 || x 4]).getD i.val false = x i := by
            have lt : i.val < (List.ofFn x).length := by simp
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left lt]
            rw [List.getElem?_eq_getElem lt, List.getElem_ofFn]
            rfl
          have secondValue :
              step (List.ofFn x ++ [x 0 || x 4]) second =
                List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)] := by
            have mapEq :
                (T.toList.map Fin.val).map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
                  T.toList.map x := by
              rw [List.map_map]
              apply List.map_congr_left
              intro i _
              exact read i
            have eq : (T.toList.map x).any id = decide (∃ a ∈ T, x a = true) := by
              apply Bool.eq_iff_iff.mpr
              simp [List.any_eq_true]
            change (List.ofFn x ++ [x 0 || x 4]) ++ [((T.toList.map Fin.val).map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)).any id] = _
            rw [mapEq]
            simpa [List.append_assoc] using
              congrArg (fun b => List.ofFn x ++ [x 0 || x 4, b]) eq
          change (D.gates.foldl step (step (step (List.ofFn x) first) second)).getD D.output false =
            (D.gates.foldl step _).getD D.output false
          rw [firstValue, secondValue]
        have post := binaryBound full legalD (fun x => (value x).trans (computes x))
        have size : full.size = D.size + 2 := by
          change (first :: second :: D.gates).length = D.gates.length + 2
          simp
        have nots : notCount full = notCount D := by
          change (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))
            (first :: second :: D.gates)).length = _
          change _ = (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) D.gates).length
          simp [first, second]
        rw [size, nots] at post
        omega
    · apply triple D a legal
      intro x
      have h : decide (∃ b ∈ ({0,4,a} : Finset (Fin 9)), x b = true) =
          ((x 0 || x 4) || x a) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_insert, Finset.mem_singleton]
        aesop
      simpa only [h] using computes x
  omega
