import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A raw pair i, j is represented by 10 * i + j. The graph symmetry that swaps
-- 0 with 2, 3 with 5, and 4 with 7 preserves the first OR and reduces the cases.
theorem PEqualNP.Outside.R_meta_3022_731
    (short : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (rawPair : ∀ (i j : Fin 9), i.val * 10 + j.val ∈
      ([1, 3, 4, 5, 6, 7, 8, 13, 14, 16, 18, 34, 35, 36, 37, 38, 46, 47, 48, 68] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, x i || x j]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (triple : ∀ i : Fin 9, i.val ∈ ([1, 3, 4, 6, 8] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 2, (x 0 || x 2) || x i]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins pinCount D fan size
  let target (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  have wLen (x : Fin 9 → Bool) : (w x).length = 10 := by simp [w]
  have raw (x : Fin 9 → Bool) (i : Fin 9) : (w x).getD i.val false = x i := by
    rw [List.getD_append (List.ofFn x) [x 0 || x 2] false i.val (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have first (x : Fin 9 → Bool) : (w x).getD 9 false = (x 0 || x 2) := by
    change (List.ofFn x ++ [x 0 || x 2]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have zero (x : Fin 9 → Bool) : (w x).getD 10 false = false :=
    List.getD_eq_default _ _ (by simp [wLen])
  let mapGate (rename : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let renameCircuit (rename : ℕ → ℕ) : Circuit :=
    ⟨D.gates.map (mapGate rename), rename D.output⟩
  have renamedFan (rename : ℕ → ℕ) : FanInTwo (renameCircuit rename) := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using fan k hk
  let step (values : List Bool) (g : Gate) :=
    values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]
  have simulate (rename : ℕ → ℕ) (left right : List Bool) (limit : ℕ)
      (read : ∀ ys : List Bool, ys.length ≤ limit → ∀ i : ℕ,
        (left ++ ys).getD (rename i) false = (right ++ ys).getD i false)
      (gs : List Gate) (ys : List Bool) (n : gs.length + ys.length ≤ limit) :
      ∃ zs : List Bool, zs.length ≤ limit ∧
        (gs.map (mapGate rename)).foldl step (left ++ ys) = left ++ zs ∧
        gs.foldl step (right ++ ys) = right ++ zs := by
    induction gs generalizing ys with
    | nil => exact ⟨ys, by simpa using n, rfl, rfl⟩
    | cons g gs ih =>
      let value := g.op.eval (g.inputs.map fun i => (right ++ ys).getD i false)
      have values : (g.inputs.map fun i => (left ++ ys).getD (rename i) false) =
          (g.inputs.map fun i => (right ++ ys).getD i false) :=
        List.map_congr_left (fun i _ => read ys (by omega) i)
      have evalEq : step (left ++ ys) (mapGate rename g) = left ++ (ys ++ [value]) := by
        simp only [mapGate, step, List.map_map, Function.comp_def, values, value, List.append_assoc]
      have bound : gs.length + (ys ++ [value]).length ≤ limit := by
        simp only [List.length_cons, List.length_append, List.length_nil] at n ⊢
        omega
      have next : step (right ++ ys) g = right ++ (ys ++ [value]) :=
        List.append_assoc _ _ _
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, evalEq, next]
      exact ih (ys ++ [value]) bound
  have discard (b : (Fin 9 → Bool) → Bool) (j : ℕ) (hj : j ≤ 10)
      (valueEq : ∀ x, b x = (w x).getD j false) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [b x]) ≠ target x := by
    by_contra! agrees
    let rename (i : ℕ) :=
      if i = 10 then if j < 10 then j else 10 + D.size
      else if i < 10 then i else i - 1
    let gate : Gate := ⟨.or, [0, 2]⟩
    let E : Circuit := ⟨gate :: D.gates.map (mapGate rename), rename D.output⟩
    have valid : FanInTwo E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [gate]
      · exact renamedFan rename g hg
    have small : E.size ≤ 14 := by
      change (gate :: D.gates.map (mapGate rename)).length ≤ 14
      change D.gates.length ≤ 13 at size
      simpa only [List.length_cons, List.length_map] using Nat.succ_le_succ size
    apply short
    refine ⟨E, valid, small, fun x => ?_⟩
    have read (ys : List Bool) (n : ys.length ≤ D.size) (i : ℕ) :
        (w x ++ ys).getD (rename i) false = (w x ++ [b x] ++ ys).getD i false := by
      by_cases heq : i = 10
      · subst i
        rw [List.getD_append (w x ++ [b x]) ys false 10 (by simp [wLen]),
          List.getD_append_right (w x) [b x] false 10 (by simp [wLen])]
        simp only [wLen, Nat.sub_self, List.getD_cons_zero, rename, ite_true]
        by_cases present : j < 10
        · rw [ite_eq_left present, List.getD_append _ _ _ _ (by simpa only [wLen] using present)]
          exact (valueEq x).symm
        · rw [ite_eq_right present, List.getD_eq_default _ _ (by simp [wLen]; omega)]
          have eq : j = 10 := by omega
          exact ((valueEq x).trans (by rw [eq]; exact zero x)).symm
      · by_cases early : i < 10
        · simp only [rename, ite_eq_right heq, ite_eq_left early]
          rw [List.getD_append (w x) ys false i (by simpa only [wLen] using early),
            List.getD_append (w x ++ [b x]) ys false i (by simp [wLen]; omega),
            List.getD_append (w x) [b x] false i (by simpa only [wLen] using early)]
        · simp only [rename, ite_eq_right heq, ite_eq_right early]
          rw [List.getD_append_right (w x) ys false (i - 1) (by simp [wLen]; omega),
            List.getD_append_right (w x ++ [b x]) ys false i (by simp [wLen]; omega)]
          simp only [List.length_append, List.length_singleton, wLen]
          congr 1
    have firstGate : step (List.ofFn x) gate = w x := by
      change List.ofFn x ++ [((List.ofFn x).getD 0 false ||
        ((List.ofFn x).getD 2 false || false))] = w x
      simp [w, List.getD_eq_getElem?_getD]
    obtain ⟨zs, zn, left, right⟩ :=
      simulate rename (w x) (w x ++ [b x]) D.size read D.gates [] le_rfl
    simp only [List.append_nil] at left right
    have sem : E.eval (List.ofFn x) = D.eval (w x ++ [b x]) := by
      change ((D.gates.map (mapGate rename)).foldl step (step (List.ofFn x) gate)).getD
        (rename D.output) false = (D.gates.foldl step (w x ++ [b x])).getD D.output false
      rw [firstGate, left, right]
      exact read zs zn D.output
    rw [sem, agrees x]
    simp [target, List.any_cons, Bool.or_assoc, Fin.ofNat]
  let mirror : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
  have m0 : mirror 0 = 2 := rfl
  have m2 : mirror 2 = 0 := rfl
  have mirrorTarget : ∀ x : Fin 9 → Bool, target (fun i => x (mirror i)) = target x := by
    decide +kernel
  let mirrorIndex (i : ℕ) := if hi : i < 9 then (mirror ⟨i, hi⟩).val else i
  let M := renameCircuit mirrorIndex
  have mirrorSize : M.size ≤ 13 := by
    change (D.gates.map (mapGate mirrorIndex)).length ≤ 13
    rw [List.length_map]
    exact size
  have mirrorEval (x : Fin 9 → Bool) (b : Bool) :
      M.eval (w x ++ [b]) = D.eval (w (fun i => x (mirror i)) ++ [b]) := by
    let y : Fin 9 → Bool := fun i => x (mirror i)
    have read (ys : List Bool) (i : ℕ) :
        (List.ofFn x ++ ys).getD (mirrorIndex i) false = (List.ofFn y ++ ys).getD i false := by
      by_cases hi : i < 9
      · have hmi : (mirror ⟨i, hi⟩).val < 9 := (mirror ⟨i, hi⟩).isLt
        rw [show mirrorIndex i = (mirror ⟨i, hi⟩).val by simp only [mirrorIndex, dite_eq_left hi],
          List.getD_append (List.ofFn x) ys false _ (by simpa only [List.length_ofFn] using hmi),
          List.getD_append (List.ofFn y) ys false _ (by simpa only [List.length_ofFn] using hi),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hmi),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem_ofFn, y]
      · have hn : 9 ≤ i := by omega
        rw [show mirrorIndex i = i by simp only [mirrorIndex, dite_eq_right hi],
          List.getD_append_right (List.ofFn x) ys false i (by simpa only [List.length_ofFn] using hn),
          List.getD_append_right (List.ofFn y) ys false i (by simpa only [List.length_ofFn] using hn)]
        simp only [List.length_ofFn]
    let initial := [x 0 || x 2, b]
    have wx : w x ++ [b] = List.ofFn x ++ initial := List.append_assoc _ _ _
    have wy : w y ++ [b] = List.ofFn y ++ initial := by
      simp only [w, y, m0, m2, Bool.or_comm (x 2) (x 0), List.append_assoc, initial]
      rfl
    obtain ⟨ys, _, left, right⟩ :=
      simulate mirrorIndex (List.ofFn x) (List.ofFn y) (D.size + 2)
        (fun ys _ i => read ys i) D.gates initial le_rfl
    change ((D.gates.map (mapGate mirrorIndex)).foldl step (w x ++ [b])).getD
      (mirrorIndex D.output) false = (D.gates.foldl step (w y ++ [b])).getD D.output false
    rw [wx, wy, left, right]
    exact read ys D.output
  have transport (b c : (Fin 9 → Bool) → Bool)
      (equiv : ∀ x : Fin 9 → Bool, c x = b (fun i => x (mirror i)))
      (smaller : ∃ x : Fin 9 → Bool, M.eval (w x ++ [c x]) ≠ target x) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [b x]) ≠ target x := by
    obtain ⟨x, hx⟩ := smaller
    refine ⟨fun i => x (mirror i), ?_⟩
    rw [mirrorTarget]
    rwa [mirrorEval, equiv x] at hx
  let pairRep (i j : Fin 9) : Prop := i.val * 10 + j.val ∈
    ([1, 3, 4, 5, 6, 7, 8, 13, 14, 16, 18, 34, 35, 36, 37, 38, 46, 47, 48, 68] : List ℕ)
  let tripleRep (i : Fin 9) : Prop := i.val ∈ ([1, 3, 4, 6, 8] : List ℕ)
  have pairsCovered : ∀ (i j : Fin 9), i < j → ¬(i = 0 ∧ j = 2) →
      pairRep i j ∨ pairRep (mirror i) (mirror j) ∨ pairRep (mirror j) (mirror i) := by
    decide +kernel
  have triplesCovered : ∀ i : Fin 9, i ≠ 0 → i ≠ 2 → tripleRep i ∨ tripleRep (mirror i) := by
    decide +kernel
  have copy (i : Fin 11) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [(w x).getD i.val false]) ≠ target x :=
    discard _ i.val (by omega) (fun _ => rfl)
  have copyFirst : ∃ x : Fin 9 → Bool, D.eval (w x ++ [x 0 || x 2]) ≠ target x := by
    simpa only [show (9 : Fin 11).val = 9 by rfl, first] using copy (9 : Fin 11)
  have constant : ∃ x : Fin 9 → Bool, D.eval (w x ++ [false]) ≠ target x := by
    simpa only [show (10 : Fin 11).val = 10 by rfl, zero] using copy (10 : Fin 11)
  have sortedPair (i j : Fin 9) (order : i < j) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [x i || x j]) ≠ target x := by
    by_cases special : i = 0 ∧ j = 2
    · rcases special with ⟨rfl, rfl⟩
      exact copyFirst
    · rcases pairsCovered i j order special with h | h | h
      · simpa only [w, List.append_assoc, List.cons_append, List.nil_append, target] using
          rawPair i j h D fan size
      · refine transport (fun x => x i || x j) (fun x => x (mirror i) || x (mirror j))
          (fun _ => rfl) ?_
        simpa only [w, List.append_assoc, List.cons_append, List.nil_append, target] using
          rawPair (mirror i) (mirror j) h M (renamedFan _) mirrorSize
      · refine transport (fun x => x i || x j) (fun x => x (mirror j) || x (mirror i))
          (fun _ => Bool.or_comm _ _) ?_
        simpa only [w, List.append_assoc, List.cons_append, List.nil_append, target] using
          rawPair (mirror j) (mirror i) h M (renamedFan _) mirrorSize
  have rawOr (i j : Fin 9) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [x i || x j]) ≠ target x := by
    rcases lt_trichotomy i j with smaller | rfl | larger
    · exact sortedPair i j smaller
    · simpa only [Bool.or_self] using discard (fun x => x i) i.val (by omega) (fun x => (raw x i).symm)
    · simpa only [Bool.or_comm] using sortedPair j i larger
  have linked (i : Fin 9) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [(x 0 || x 2) || x i]) ≠ target x := by
    by_cases h0 : i = 0
    · subst i
      exact copyFirst.imp fun x hx => by
        simpa only [Bool.or_assoc, Bool.or_comm (x 2) (x 0), Bool.or_self_left] using hx
    · by_cases h2 : i = 2
      · subst i
        simpa only [Bool.or_assoc, Bool.or_self] using copyFirst
      · rcases triplesCovered i h0 h2 with h | h
        · simpa only [w, List.append_assoc, List.cons_append, List.nil_append, target] using
            triple i h D fan size
        · refine transport (fun x => (x 0 || x 2) || x i)
            (fun x => (x 0 || x 2) || x (mirror i)) ?_ ?_
          · intro x
            simp only [m0, m2, Bool.or_comm (x 2) (x 0)]
          · simpa only [w, List.append_assoc, List.cons_append, List.nil_append, target] using
              triple (mirror i) h M (renamedFan _) mirrorSize
  have mixed (i : Fin 9) (j : Fin 11) :
      ∃ x : Fin 9 → Bool, D.eval (w x ++ [x i || (w x).getD j.val false]) ≠ target x := by
    by_cases hj : j.val < 9
    · exact (rawOr i ⟨j.val, hj⟩).imp fun x h => by simpa only [raw x ⟨j.val, hj⟩] using h
    · by_cases h9 : j.val = 9
      · simpa only [h9, first, Bool.or_comm] using linked i
      · have h10 : j.val = 10 := by omega
        simpa only [h10, zero, Bool.or_false] using
          discard (fun x => x i) i.val (by omega) (fun x => (raw x i).symm)
  have either (i j : Fin 11) :
      ∃ x : Fin 9 → Bool,
        D.eval (w x ++ [(w x).getD i.val false || (w x).getD j.val false]) ≠ target x := by
    by_cases hi : i.val < 9
    · exact (mixed ⟨i.val, hi⟩ j).imp fun x h => by simpa only [raw x ⟨i.val, hi⟩] using h
    · by_cases hj : j.val < 9
      · exact (mixed ⟨j.val, hj⟩ i).imp fun x h => by simpa only [raw x ⟨j.val, hj⟩, Bool.or_comm] using h
      · have ii : i.val = 9 ∨ i.val = 10 := by omega
        have jj : j.val = 9 ∨ j.val = 10 := by omega
        rcases ii with hi9 | hi10 <;> rcases jj with hj9 | hj10
        · simpa only [hi9, hj9, first, Bool.or_self] using copyFirst
        · simpa only [hi9, hj10, first, zero, Bool.or_false] using copyFirst
        · simpa only [hi10, hj9, first, zero, Bool.false_or] using copyFirst
        · simpa only [hi10, hj10, zero, Bool.false_or] using constant
  change ∃ x : Fin 9 → Bool,
    D.eval (w x ++ [GateOp.or.eval (pins.map fun i => (w x).getD i.val false)]) ≠ target x
  rcases pins with _ | ⟨i, _ | ⟨j, rest⟩⟩
  · exact constant
  · change ∃ x : Fin 9 → Bool, D.eval (w x ++ [(w x).getD i.val false || false]) ≠ target x
    simpa only [Bool.or_false] using copy i
  · have empty : rest = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at pinCount
      omega
    subst rest
    change ∃ x : Fin 9 → Bool,
      D.eval (w x ++ [(w x).getD i.val false || ((w x).getD j.val false || false)]) ≠ target x
    simpa only [Bool.or_false] using either i j
