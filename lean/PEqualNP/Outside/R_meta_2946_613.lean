import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2946_613
    (noRead :
      ∀ (i : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, (x 0 && x 2) = false →
          C.eval (List.ofFn x ++ [false, !x i]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        ∀ g ∈ C.gates, (9 : ℕ) ∉ g.inputs)
    (fullLower :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → x2.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro i C fan _ size
  by_contra h
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have correct (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [x 0 && x 2, !x i]) = target x := by
    by_contra different
    exact h ⟨x, different⟩
  have unread : ∀ g ∈ C.gates, (9 : ℕ) ∉ g.inputs :=
    noRead i C fan size (fun x hx => by simpa only [hx] using correct x)

  let val (g : Gate) (w : List Bool) :=
    g.op.eval (g.inputs.map fun a => w.getD a false)
  let step (w : List Bool) (g : Gate) := w ++ [val g w]
  have keep (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
      (gs.foldl step w).getD a false = w.getD a false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hstep : a < (step w g).length := by
        simpa only [step, List.length_append, List.length_singleton] using Nat.lt_succ_of_lt ha
      rw [List.foldl_cons, ih _ hstep]
      exact List.getD_append _ _ _ _ ha
  have output_ne : C.output ≠ 9 := by
    intro eq
    let row (a : Fin 9) : Bool := decide (a = 0 ∨ a = 1)
    have good := correct row
    have edge : target row = true := by decide
    have z : (row 0 && row 2) = false := by decide
    change (C.gates.foldl step (List.ofFn row ++ [row 0 && row 2, !row i])).getD
      C.output false = target row at good
    rw [eq, keep _ _ _ (by simp), z, edge] at good
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn] at good
    contradiction

  let shift (a : ℕ) := if a < 9 then a else a - 1
  let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shift⟩
  -- The suffix may be shorter than the requested index. Both reads then return false.
  have readShift (u t : List Bool) (b : Bool) (hu : u.length = 9)
      (a : ℕ) (ha : a ≠ 9) :
      (u ++ t).getD (shift a) false = (u ++ [b] ++ t).getD a false := by
    by_cases early : a < 9
    · have low : a < u.length := hu.symm ▸ early
      have low' : a < (u ++ [b]).length := by
        simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt low
      simp only [shift, ite_eq_left early]
      rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ low',
        List.getD_append _ _ _ _ low]
    · have high : 9 < a := Nat.lt_of_le_of_ne (Nat.le_of_not_gt early) ha.symm
      have high' : (u ++ [b]).length ≤ a := by
        simpa only [List.length_append, List.length_singleton, hu] using Nat.succ_le_of_lt high
      have shifted : u.length ≤ a - 1 := by
        rw [hu]
        exact Nat.le_sub_of_add_le high
      simp only [shift, ite_eq_right early]
      rw [List.getD_append_right _ _ _ _ shifted, List.getD_append_right _ _ _ _ high']
      congr 1
      simp only [List.length_append, List.length_singleton, Nat.sub_sub, Nat.add_comm 1 u.length]
  have runShift (gs : List Gate) (u t : List Bool) (b : Bool) (hu : u.length = 9)
      (hgs : ∀ g ∈ gs, (9 : ℕ) ∉ g.inputs) :
      ∃ s : List Bool, (gs.map shiftGate).foldl step (u ++ t) = u ++ s ∧
        gs.foldl step (u ++ [b] ++ t) = u ++ [b] ++ s := by
    induction gs generalizing t with
    | nil => exact ⟨t, rfl, rfl⟩
    | cons g gs ih =>
      have same : val (shiftGate g) (u ++ t) = val g (u ++ [b] ++ t) := by
        simp only [val, shiftGate, List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro a ha
        exact readShift u t b hu a (fun eq => hgs g (by simp) (eq ▸ ha))
      simp only [List.map_cons, List.foldl_cons, step, same, List.append_assoc]
      simpa only [List.append_assoc] using
        ih (t ++ [val g (u ++ [b] ++ t)]) (fun r hr => hgs r (by simp [hr]))

  let neg : Gate := ⟨.not, [i.val]⟩
  let D : Circuit := ⟨neg :: C.gates.map shiftGate, shift C.output⟩
  have dfan : FanInTwo D := by
    intro g hg
    change g ∈ neg :: C.gates.map shiftGate at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [neg]
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      simpa only [shiftGate, List.length_map] using fan r hr
  have dsize : D.size ≤ 14 := by
    change (neg :: C.gates.map shiftGate).length ≤ 14
    change C.gates.length ≤ 13 at size
    simpa only [List.length_cons, List.length_map] using Nat.succ_le_succ size
  apply fullLower D dfan dsize
  intro x
  have inputRead : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
    rfl
  have negValue : val neg (List.ofFn x) = !x i := by
    change (!((List.ofFn x).getD i.val false)) = (!x i)
    rw [inputRead]
  obtain ⟨s, ds, cs⟩ :=
    runShift C.gates (List.ofFn x) [!x i] (x 0 && x 2) (by simp) unread
  have old := correct x
  change (C.gates.foldl step (List.ofFn x ++ [x 0 && x 2, !x i])).getD
    C.output false = target x at old
  rw [show List.ofFn x ++ [x 0 && x 2, !x i] =
    List.ofFn x ++ [x 0 && x 2] ++ [!x i] by simp, cs] at old
  change ((neg :: C.gates.map shiftGate).foldl step (List.ofFn x)).getD
    (shift C.output) false = target x
  rw [List.foldl_cons, show step (List.ofFn x) neg = List.ofFn x ++ [!x i] by
    simp only [step, negValue], ds]
  exact (readShift (List.ofFn x) s (x 0 && x 2) (by simp) C.output output_ne).trans old
