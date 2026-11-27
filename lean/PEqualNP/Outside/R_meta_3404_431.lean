import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3404_431
    (firstBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 13 ≤ C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (covered : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Finset (Fin 9)), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    1 ≤ PEqualNP.NotBracket.notCount C →
    (s.card ≤ 1 ∨ s = {0,4} ∨ ∃ u v : Fin 9, u<v ∧ s={u,v} ∧ 10*u.val+v.val ∈ ([1,2,5,6,7,8,16,17,18,24,25,26,34,46,47,48,56,57,67,78] : List ℕ)) →
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ s, x i=true)]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False)
    (remaining : ∀ (u v : Fin 9), 10 * min u.val v.val + max u.val v.val ∈
        ([3,12,13,14,15,23,27,28,36] : List ℕ) →
      ∀ C : Circuit, FanInTwo C → C.size = 13 → PEqualNP.NotBracket.notCount C = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → (14 : ℕ) ≤ x1.size := by
  classical
  intro C s fan arity hasNot _ agrees
  by_contra! small
  let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let fire := fun (x : Fin 9 → Bool) => decide (∃ i ∈ s, x i=true)
  have correct (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4, fire x]) = f x := by
    rw [show C.eval (List.ofFn x ++ [x 0 || x 4, fire x]) = _ from agrees x]
    exact (by decide +kernel : ∀ x : Fin 9 → Bool, ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => x e.1 && x e.2) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) x
  let g : Gate := ⟨.or,s.toList.map Fin.val⟩
  let D : Circuit := ⟨g :: C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact ⟨by simp [g], by simpa [g] using arity⟩
    · exact fan a h
  let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have addGate (x : Fin 9 → Bool) :
      step (List.ofFn x ++ [x 0 || x 4]) g = List.ofFn x ++ [x 0 || x 4, fire x] := by
    let w := List.ofFn x ++ [x 0 || x 4]
    have read (i : Fin 9) : w.getD i.val false = x i := by
      change (List.ofFn x ++ [_]).getD i.val false = _
      rw [List.getD_append (List.ofFn x) _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
    have one : ((s.toList.map Fin.val).map (fun i => w.getD i false)).any id = fire x := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.map_map,Function.comp_def,read,List.any_map,id_eq,Function.id_comp,
        List.any_eq_true,Finset.mem_toList,fire,decide_eq_true_eq]
    change w ++ [((s.toList.map Fin.val).map (fun i => w.getD i false)).any id] = _
    rw [one]
    simp [w,List.append_assoc]
  have honest (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = f x := by
    change (C.gates.foldl step (step (List.ofFn x ++ [x 0 || x 4]) g)).getD _ false = _
    rw [addGate]
    exact correct x
  let paid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  have lb := firstBound D legal honest
  change 13 ≤ (g :: C.gates).countP paid at lb
  have pg : paid g = true := rfl
  rw [List.countP_cons,pg,if_pos rfl] at lb
  have accounting (E : Circuit) : E.gates.countP paid + PEqualNP.NotBracket.notCount E = E.size := by
    unfold PEqualNP.NotBracket.notCount Circuit.size
    induction E.gates with
    | nil => rfl
    | cons h gs ih =>
      dsimp only [paid] at ih
      cases h with | mk op ins => cases op <;> simp [paid,List.filter_cons] <;> omega
  have balance := accounting C
  have exactly : PEqualNP.NotBracket.notCount C = 1 := by omega
  have length : C.size = 13 := by omega
  let good : List ℕ := [1,2,5,6,7,8,16,17,18,24,25,26,34,46,47,48,56,57,67,78]
  let rest : List ℕ := [3,12,13,14,15,23,27,28,36]
  let rho : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let num := fun (a b : Fin 9) => 10 * min a.val b.val + max a.val b.val
  have blocked : ¬(s.card≤1 ∨ s={0,4} ∨ ∃ u v : Fin 9, u<v ∧ s={u,v} ∧ 10*u.val+v.val∈good) :=
    fun h => covered C s fan (by omega) hasNot h correct
  have ex : ∃ u v : Fin 9, u<v ∧ s={u,v} := by
    have two : s.card=2 := by by_contra h; exact blocked (Or.inl (by omega))
    obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp two
    rcases lt_or_gt_of_ne ne with lt | gt
    · exact ⟨a,b,lt,eq⟩
    · exact ⟨b,a,gt,eq.trans (Finset.pair_comm a b)⟩
  obtain ⟨u,v,lt,ss⟩ := ex
  have no04 : ¬ (u=0 ∧ v=4) := by
    rintro ⟨rfl,rfl⟩
    exact blocked (Or.inr (Or.inl ss))
  have notGood : 10*u.val+v.val ∉ good := fun h => blocked (Or.inr (Or.inr ⟨u,v,lt,ss,h⟩))
  have narrow : ∀ u v : Fin 9, u<v → ¬(u=0 ∧ v=4) → 10*u.val+v.val ∉ good →
      num u v ∈ rest ∨ num (rho u) (rho v) ∈ rest := by
    dsimp only [num,good,rest,rho]
    decide +kernel
  have pairEval (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) = f x := by
    have flag : fire x = (x u || x v) := by
      apply Bool.eq_iff_iff.mpr
      simp [fire,ss,Bool.or_eq_true]
    simpa only [flag] using correct x
  rcases narrow u v lt no04 notGood with yes | reflected
  · obtain ⟨x,h⟩ := remaining u v yes C fan length exactly
    exact h (pairEval x)
  let shift := fun (i : ℕ) => if h : i<9 then (rho ⟨i,h⟩).val else i
  let move := fun (g : Gate) => Gate.mk g.op (g.inputs.map shift)
  let E : Circuit := ⟨C.gates.map move,shift C.output⟩
  have reads (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
      (List.ofFn (fun k => x (rho k)) ++ tail).getD i false = (List.ofFn x ++ tail).getD (shift i) false := by
    by_cases h : i<9
    · simp only [shift,dif_pos h]
      have j := (rho ⟨i,h⟩).isLt
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j)]
      simp only [List.getElem_ofFn]
    · simp only [shift,dif_neg h]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega),
        List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega)]
      simp only [List.length_ofFn]
  have forward (x : Fin 9 → Bool) (gs : List Gate) (t : List Bool) : ∃ T,
      gs.foldl step (List.ofFn (fun k => x (rho k))++t) = List.ofFn (fun k => x (rho k))++T ∧
      (gs.map move).foldl step (List.ofFn x++t) = List.ofFn x++T := by
    induction gs generalizing t with
    | nil => exact ⟨t,rfl,rfl⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => x (rho k))++t).getD i false)
      have eq : (move g).op.eval ((move g).inputs.map fun i => (List.ofFn x++t).getD i false) = bit := by
        dsimp only [move,bit]
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i _
        exact (reads x t i).symm
      obtain ⟨T,hl,hr⟩ := ih (t++[bit])
      refine ⟨T,?_,?_⟩
      · simpa only [List.foldl_cons,step,bit,List.append_assoc] using hl
      · simpa only [List.map_cons,List.foldl_cons,step,eq,List.append_assoc] using hr
  have legalE : FanInTwo E := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [move] using fan a ha
  have lenE : E.size = 13 := by
    change (C.gates.map move).length = 13
    rw [List.length_map]
    exact length
  have negE : PEqualNP.NotBracket.notCount E = 1 := by
    have eq : E.gates.countP paid = C.gates.countP paid := by
      change (C.gates.map move).countP paid = _
      rw [List.countP_map]
      rfl
    have b := accounting E
    omega
  have fixed : ∀ x : Fin 9 → Bool, f (fun i => x (rho i)) = f x := by
    dsimp only [f,rho]
    decide +kernel
  obtain ⟨x,wrong⟩ := remaining (rho u) (rho v) reflected E legalE lenE negE
  let t := [x 0 || x 4, x (rho u) || x (rho v)]
  have h := pairEval (fun i => x (rho i))
  have old : C.eval (List.ofFn (fun k => x (rho k))++t) = f x := h.trans (fixed x)
  obtain ⟨T,hl,hr⟩ := forward x C.gates t
  apply wrong
  change ((C.gates.map move).foldl step (List.ofFn x++t)).getD (shift C.output) false = f x
  change (C.gates.foldl step _).getD C.output false = f x at old
  rw [hr,← reads x T C.output,←hl]
  exact old
