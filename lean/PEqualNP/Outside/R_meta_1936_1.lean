import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Token ten is false and token eleven is true. The latter pads a missing AND operand.
-- Conjugating the suffix relabels input wires but leaves gate wire numbers fixed.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem PEqualNP.Outside.R_meta_1936_1
  (literal : ∀ ab ∈ ([(0,0),(1,1),(2,2),(3,3),(4,4),(6,6),(9,9),(10,10),(11,11)] : List (Fin 12 × Fin 12)),
    ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      let t := fun i : Fin 12 => if i = 11 then true else w.getD i.val false
      D.eval (w ++ [t ab.1 && t ab.2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (positive : ∀ ab ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),(2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)] : List (Fin 12 × Fin 12)),
    ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      let t := fun i : Fin 12 => if i = 11 then true else w.getD i.val false
      D.eval (w ++ [t ab.1 && t ab.2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (negative : ∀ ab ∈ ([(1,9),(2,9),(3,9),(4,9),(6,9)] : List (Fin 12 × Fin 12)),
    ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      let t := fun i : Fin 12 => if i = 11 then true else w.getD i.val false
      D.eval (w ++ [t ab.1 && t ab.2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 0)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro pins hlen D hf hs
  let target := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let w := fun x : Fin 9 → Bool => List.ofFn x ++ [!x 0]
  let tok := fun (x : Fin 9 → Bool) (i : Fin 12) =>
    if i = 11 then true else (w x).getD i.val false
  let clip (i : ℕ) : Fin 12 := ⟨min i 10,by omega⟩
  have readClip (x : Fin 9 → Bool) (i : ℕ) : tok x (clip i) = (w x).getD i false := by
    have len : (w x).length = 10 := by simp [w]
    have ne : clip i ≠ 11 := fun h => by have := congrArg Fin.val h; change min i 10 = 11 at this; omega
    simp only [tok,if_neg ne,clip]
    by_cases hi : i ≤ 10
    · rw [Nat.min_eq_left hi]
    · rw [Nat.min_eq_right (by omega),List.getD_eq_default _ false (by omega),List.getD_eq_default _ false (by omega)]
  obtain ⟨a,b,hab⟩ : ∃ a b : Fin 12, ∀ x, GateOp.and.eval (pins.map fun i => (w x).getD i false) = (tok x a && tok x b) := by
    cases pins with
    | nil => exact ⟨11,11,by intro x; rfl⟩
    | cons i rest =>
      cases rest with
      | nil => exact ⟨clip i,11,by intro x; rw [readClip]; rfl⟩
      | cons j rest =>
        have he : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst rest
        exact ⟨clip i,clip j,by intro x; rw [readClip,readClip]; change (_ && (_ && true)) = _; simp⟩
  let maps : Fin 2 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
      ![0,5,8,3,4,1,7,6,2]]
  let table (x : Fin 9 → Bool) : Fin 12 → Bool := fun i =>
    if h : i.val < 9 then x ⟨i.val,h⟩ else if i = 9 then !x 0 else decide (i = 11)
  have tableOK (x : Fin 9 → Bool) (i : Fin 12) : tok x i = table x i := by fin_cases i <;> rfl
  let norm (i j : Fin 12) := if i = 10 ∨ j = 10 ∨ (min i j = 0 ∧ max i j = 9) then (10,10)
    else if max i j = 11 then (min i j,min i j) else (min i j,max i j)
  let ext (k : Fin 2) (i : Fin 12) : Fin 12 :=
    if h : i.val < 9 then ⟨(maps k ⟨i.val,h⟩).val,Nat.lt_trans (maps k ⟨i.val,h⟩).isLt (by decide : 9 < 12)⟩ else i
  have cert : ∀ i j, ∃ k, let p := norm (ext k i) (ext k j)
    p ∈ ([(0,0),(1,1),(2,2),(3,3),(4,4),(6,6),(9,9),(10,10),(11,11)] : List _) ∨ p ∈ [(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),(2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)] ∨ p ∈ [(1,9),(2,9),(3,9),(4,9),(6,9)] := by
    dsimp only [ext,norm,maps]
    decide +kernel
  have fix : ∀ k, maps k 0 = 0 := by dsimp only [maps]; decide +kernel
  have graph : ∀ k (x : Fin 9 → Bool), target (x ∘ maps k) = target x := by
    intro k x
    fin_cases k
    · rfl
    · change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  have literals (k) (i) (x : Fin 9 → Bool) : table (x ∘ maps k) i = table x (ext k i) := by
    by_cases h : i.val < 9
    · simp [table,ext,h,(maps k ⟨i.val,h⟩).isLt,Function.comp_def]
    · simp [table,ext,h,Function.comp_def,fix]
  have normalized (i j : Fin 12) (x : Fin 9 → Bool) :
      (table x i && table x j) = (table x (norm i j).1 && table x (norm i j).2) := by
    have sorted (u v : Fin 12) (h : u ≤ v) :
        (table x u && table x v) = (table x (norm u v).1 && table x (norm u v).2) := by
      have ten : table x 10 = false := rfl
      have eleven : table x 11 = true := rfl
      have cancel : (table x 0 && table x 9) = false := by change (x 0 && !(x 0)) = false; cases x 0 <;> rfl
      simp only [norm,min_eq_left h,max_eq_right h]
      split
      · rename_i cond
        rcases cond with rfl | rfl | ⟨rfl,rfl⟩ <;> simp [ten,cancel]
      · split
        · rename_i hv
          subst v
          simp [eleven]
        · rfl
    rcases le_total i j with h|h
    · exact sorted i j h
    · have comm : norm j i = norm i j := by simp [norm,min_comm,max_comm,or_left_comm,or_comm]
      rw [Bool.and_comm (table x i) (table x j),← comm]
      exact sorted j i h
  obtain ⟨k,hrep⟩ := cert a b
  let ab := norm (ext k a) (ext k b)
  let f (i : ℕ) := if h : i < 9 then (maps k ⟨i,h⟩).val else i
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
  let E : Circuit := ⟨D.gates.map rename,f D.output⟩
  have heFan : FanInTwo E := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    simpa [rename] using hf j hj
  have sizeE : E.size ≤ 13 := by
    change (D.gates.map rename).length ≤ 13
    rw [List.length_map]
    exact hs
  obtain ⟨x,bad⟩ : ∃ x, E.eval (w x ++ [tok x ab.1 && tok x ab.2]) ≠ target x := by
    rcases hrep with h|h|h
    · exact literal ab h E heFan sizeE
    · exact positive ab h E heFan sizeE
    · exact negative ab h E heFan sizeE
  refine ⟨x ∘ maps k, ?_⟩
  let y := x ∘ maps k
  have aux : GateOp.and.eval (pins.map fun i => (w y).getD i false) = (tok x ab.1 && tok x ab.2) := by
    rw [hab,tableOK,tableOK,literals,literals,normalized]
    simp only [tableOK,ab]
  let bval := tok x ab.1 && tok x ab.2
  have base (i : ℕ) : ((w y ++ [bval]).getD i false) = ((w x ++ [bval]).getD (f i) false) := by
    by_cases hi : i < 9
    · simp only [w,List.append_assoc]
      rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simp [f,hi])]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn, f,hi,dif_pos]
      simp [y,hi]
    · have len (z : Fin 9 → Bool) : (w z).length = 10 := by simp [w]
      simp only [f,dif_neg hi]
      by_cases e : i = 9
      · subst i
        simp [w,List.getD_eq_getElem?_getD,y,Function.comp_def,fix]
      · rw [List.getD_append_right _ _ false i (by rw [len]; omega),
          List.getD_append_right _ _ false i (by rw [len]; omega),len,len]
  have lift (gs : List Gate) (W V : List Bool) (lengths : W.length = V.length)
      (big : 9 ≤ W.length) (agreement : ∀ i, W.getD i false = V.getD (f i) false) :
      ∀ i, ((Circuit.mk gs 0).wires W).getD i false =
        ((Circuit.mk (gs.map rename) 0).wires V).getD (f i) false := by
    induction gs generalizing W V with
    | nil => exact agreement
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => W.getD i false)
      have eqv : (rename g).op.eval ((rename g).inputs.map fun i => V.getD i false) = v := by
        apply congrArg g.op.eval
        simp only [rename,List.map_map,Function.comp_def]
        exact List.map_congr_left (fun i _ => (agreement i).symm)
      change ∀ i, ((Circuit.mk gs 0).wires (W ++ [v])).getD i false =
        ((Circuit.mk (gs.map rename) 0).wires (V ++ [_])).getD (f i) false
      rw [eqv]
      apply ih
      · simp [lengths]
      · simp; omega
      · intro i
        by_cases h : i < W.length
        · have h' : f i < V.length := by
            dsimp only [f]
            split <;> rename_i e
            · have lt := (maps k ⟨i,e⟩).isLt
              omega
            · omega
          simpa only [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h'] using agreement i
        · rw [show f i = i by simp [f,show ¬i < 9 by omega],
              List.getD_append_right _ _ false i (by omega),
              List.getD_append_right _ _ false i (by omega),lengths]
  have same := lift D.gates (w y ++ [bval]) (w x ++ [bval]) (by simp [w]) (by simp [w]) base D.output
  change D.eval (w y ++ [GateOp.and.eval (pins.map fun i => (w y).getD i false)]) ≠ target y
  rw [aux,show target y = target x from graph k x]
  exact fun h => bad (same.symm.trans h)
