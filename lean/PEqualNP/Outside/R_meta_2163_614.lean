import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2163_614
    (normalize : ∀ D : Circuit, FanInTwo D →
      D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) ≤ 12 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      ∃ E : Circuit, FanInTwo E ∧
        E.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) ≤ 12 ∧
        (∀ v ∈ ([0,1,2,4,7,8] : List ℕ), ∀ i j : Fin E.gates.length,
          v ∈ (E.gates.get i).inputs → v ∈ (E.gates.get j).inputs → i = j) ∧
        ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x))
    (bound : ∀ E : Circuit, FanInTwo E →
      E.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) ≤ 12 →
      (∀ v ∈ ([0,1,2,4,7,8] : List ℕ), ∀ i j : Fin E.gates.length,
        v ∈ (E.gates.get i).inputs → v ∈ (E.gates.get j).inputs → i = j) →
      ∃ x : Fin 9 → Bool, E.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  classical
  intro C fan two first agrees
  by_contra! small
  let paid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  obtain ⟨i, j, distinct, hi, hj, _⟩ := two
  have replace (gs : List Gate) (p : ℕ) (hp : p < gs.length) (hn : gs[p].op = .not) :
      (gs.set p ⟨.and, []⟩).countP paid = gs.countP paid + 1 := by
    simp [paid, List.countP_set hp, hn]
  let gs' := C.gates.set i.val ⟨.and, []⟩
  have hj' : j.val < gs'.length := by simpa [gs'] using j.isLt
  have incI := replace C.gates i.val i.isLt hi
  have incJ := replace gs' j.val hj' (by
    rw [show gs'[j.val] = C.gates[j.val] from List.getElem_set_ne (fun h => distinct (Fin.ext h)) hj']
    exact hj)
  have cap := List.countP_le_length (p := paid) (l := gs'.set j.val ⟨.and, []⟩)
  change gs'.countP paid = C.gates.countP paid + 1 at incI
  simp only [List.length_set] at cap
  have leng : gs'.length = C.size := List.length_set
  have total : C.gates.countP paid ≤ 13 := by omega
  let f : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) : ∃ tail, gs.foldl step w = w ++ tail := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨tail, eq⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun k => w.getD k false) :: tail, ?_⟩
      simp only [List.foldl_cons, eq, step, List.append_assoc, List.singleton_append]
  cases parts : C.gates with
  | nil => simpa [parts] using i.isLt
  | cons head tail =>
    have headValue (x : Fin 9 → Bool) :
        head.op.eval (head.inputs.map fun k => (List.ofFn x).getD k false) = (x 0 || x 2) := by
      obtain ⟨extra, eq⟩ := keep tail (step (List.ofFn x) head)
      have h := first x
      change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at h
      rw [parts, List.foldl_cons, eq, List.getD_append _ _ _ _ (by simp [step])] at h
      change (List.ofFn x ++ [_]).getD 9 false = _ at h
      rw [List.getD_append_right (List.ofFn x) _ false 9 (by simp)] at h
      simpa only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] using h
    have nonneg : head.op ≠ .not := by
      intro en
      have hx := headValue (fun _ => false)
      rw [en] at hx
      have rd (k : ℕ) : (List.ofFn (fun _ : Fin 9 => false)).getD k false = false := by
        by_cases hk : k < 9
        · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
        · exact List.getD_eq_default _ _ (by simp; omega)
      cases hargs : head.inputs with
      | nil => rw [hargs] at hx; contradiction
      | cons k ks =>
        rw [hargs] at hx
        change (!((List.ofFn (fun _ : Fin 9 => false)).getD k false)) = false at hx
        rw [rd] at hx
        contradiction
    have hp : paid head = true := by
      change (GateOp.rec true true false (fun _ => true) true head.op : Bool) = true
      cases hop : head.op <;> first | rfl | exact (nonneg hop).elim
    let D : Circuit := ⟨tail, C.output⟩
    have legal : FanInTwo D := by
      intro g hg
      apply fan g
      rw [parts]
      exact List.mem_cons_of_mem head hg
    have budget : D.gates.countP paid ≤ 12 := by
      rw [parts, List.countP_cons, hp, if_pos rfl] at total
      change tail.countP paid ≤ 12
      omega
    have same (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 2]) = f x := by
      have hx := congrFun agrees x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at hx
      rw [parts, List.foldl_cons] at hx
      change (tail.foldl step (List.ofFn x ++ [_])).getD C.output false = _ at hx
      rw [headValue] at hx
      exact hx
    obtain ⟨E, he, hb, hu, eq⟩ := normalize D legal budget same
    obtain ⟨x, diff⟩ := bound E he hb hu
    let y : Fin 10 → Bool := Fin.lastCases (x 0 || x 2) x
    have yl : List.ofFn y = List.ofFn x ++ [x 0 || x 2] := by
      rw [List.ofFn_succ_last]
      simp [y]
      rfl
    have back := eq y
    rw [yl] at back
    exact diff (back.trans (same x))
