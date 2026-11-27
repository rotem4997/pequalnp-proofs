import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 3000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4936_1
    (monotoneCase : ∀ (C : Circuit) (b : Bool), FanInTwo C → C.size = 18 → C.output = 28 →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 11 + j.val ∨ i = 29) →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs = []) →
      let run := fun r : ℕ => C.eval ((List.ofFn fun i : Fin 10 => r.testBit i.val) ++
        [if b then r.testBit 0 && r.testBit 1 else r.testBit 0 || r.testBit 1])
      (∃ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), run r = false) ∨
      (∃ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), run r = true))
    (negationCase : ∀ (C : Circuit) (b : Bool), FanInTwo C → C.size = 18 → C.output = 28 →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 11 + j.val ∨ i = 29) →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1 ∧ 29 ∉ g.inputs) →
      (∃ g ∈ C.gates, g.op = GateOp.not ∧ g.inputs ≠ []) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 :
      ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool),
      x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 :
      Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 :
      Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 :
      ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8
      (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin
      (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ))
      && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 :
      Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 :
      ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  classical
  intro C b legal sizeBound _ _
  let f (x : Fin 10 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let input (x : Fin 10 → Bool) := List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]
  by_contra h
  have computes (x : Fin 10 → Bool) : C.eval (input x) = f x := by
    by_contra mismatch
    exact h ⟨x,mismatch⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lenRun (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih,List.length_cons]
      simp [step]
      omega
  have retain (gs : List Gate) (w : List Bool) (i : ℕ) (good : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g) (by simpa [step] using Nat.lt_succ_of_lt good)]
      exact List.getD_append _ _ _ _ good
  have inLength (x : Fin 10 → Bool) : (input x).length = 11 := by simp [input]
  have outputExists : C.output < 11 + C.gates.length := by
    by_contra! bad
    have hfull : (C.gates.foldl step (input (fun _ => true))).getD C.output false = true := computes _
    rw [List.getD_eq_default _ _ (by rw [lenRun,inLength]; exact bad)] at hfull
    exact Bool.false_ne_true hfull
  have lengthC : C.gates.length ≤ 18 := sizeBound
  have padded : ∃ D : Circuit, FanInTwo D ∧ D.size = 18 ∧ D.output = 28 ∧
      ∀ ws : List Bool, ws.length = 11 → D.eval ws = C.eval ws := by
    by_cases h28 : C.output = 28
    · have size18 : C.size = 18 := by change C.gates.length = 18; omega
      exact ⟨C,legal,size18,h28,fun _ _ => rfl⟩
    let base := C.gates.take 17
    let copy : Gate := ⟨GateOp.or,[C.output,C.output]⟩
    let extra := 18 - base.length
    let tail := List.replicate extra copy
    let D : Circuit := ⟨base ++ tail,28⟩
    have baseSmall : base.length ≤ 17 := by simp [base,List.length_take]
    have positive : 0 < extra := by dsimp [extra]; omega
    have count : base.length + extra = 18 := by dsimp [extra]; omega
    have use : C.output < 11 + base.length := by
      have baseLen : base.length = min 17 C.gates.length := by simp [base,List.length_take]
      omega
    have legalCopy : ∀ g ∈ tail, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have eq : g = copy := (List.mem_replicate.mp hg).2
      rw [eq]
      simp [copy]
    have legalD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hg|hg
      · exact legal _ (List.mem_of_mem_take hg)
      · exact legalCopy _ hg
    have sizeD : D.size = 18 := by
      change (base ++ tail).length = 18
      rw [List.length_append]
      simpa only [tail,List.length_replicate] using count
    have copyEval (ws : List Bool) : step ws copy = ws ++ [ws.getD C.output false] := by
      change ws ++ [GateOp.or.eval [ws.getD C.output false,ws.getD C.output false]] = _
      cases (ws.getD C.output false) <;> rfl
    have copies (k : ℕ) (ws : List Bool) (known : C.output < ws.length) :
        ((List.replicate k copy).foldl step ws) = ws ++ List.replicate k (ws.getD C.output false) := by
      induction k generalizing ws with
      | zero => simp
      | succ k ih =>
        rw [List.replicate_succ,List.foldl_cons,copyEval,ih _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ known, List.replicate_succ]
        simp only [List.append_assoc,List.singleton_append]
    refine ⟨D,legalD,sizeD,rfl,?_⟩
    intro ws hw
    let mid := base.foldl step ws
    have lm : mid.length = 11 + base.length := (lenRun base ws).trans (by rw [hw])
    have midKnown : C.output < mid.length := lm ▸ use
    have baseEval : mid.getD C.output false = C.eval ws := by
      have split : C.gates = base ++ C.gates.drop 17 := (List.take_append_drop _ _).symm
      change mid.getD C.output false = (C.gates.foldl step ws).getD C.output false
      rw [split,List.foldl_append]
      exact (retain _ _ _ midKnown).symm
    change ((base ++ tail).foldl step ws).getD 28 false = C.eval ws
    rw [List.foldl_append,copies extra mid midKnown,List.getD_append_right _ _ _ _ (by omega)]
    have less : 28 - mid.length < (List.replicate extra (mid.getD C.output false)).length := by simp; omega
    rw [List.getD_eq_getElem _ _ less,List.getElem_replicate]
    exact baseEval
  obtain ⟨D,dLegal,dSize,dOut,evalD⟩ := padded
  have lengthD : D.gates.length = 18 := dSize
  let cap (j i : ℕ) := if i < 11 + j then i else 29
  let read (j : ℕ) (g : Gate) := if g.op = GateOp.not then (g.inputs.take 1).filter (fun i => decide (i < 11 + j)) else g.inputs
  let fix (j : ℕ) (g : Gate) := (⟨g.op,(read j g).map (cap j)⟩ : Gate)
  let normal (gs : List Gate) (j : ℕ) := (gs.zipIdx j).map (fun p => fix p.2 p.1)
  let N : Circuit := ⟨normal D.gates 0,28⟩
  have hcap (j i : ℕ) : cap j i < 11 + j ∨ cap j i = 29 := by
    dsimp [cap]
    split <;> simp_all
  have shortRead (j : ℕ) (g : Gate) : (read j g).length ≤ g.inputs.length := by
    dsimp only [read]
    split
    · exact (List.length_filter_le _ _).trans (by simp)
    · exact le_rfl
  have notTake (l : List Bool) : GateOp.not.eval (l.take 1) = GateOp.not.eval l := by
    cases l <;> rfl
  have fixStep (g : Gate) (w : List Bool) (j : ℕ) (hLen : w.length = 11 + j) (hJ : j < 18) :
      step w (fix j g) = step w g := by
    have equal (i : ℕ) : w.getD (cap j i) false = w.getD i false := by
      by_cases small : i < 11 + j
      · simp only [cap,ite_eq_left small]
      · rw [show cap j i = 29 from ite_eq_right small]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have mapEq : ((read j g).map (cap j)).map (fun i => w.getD i false) = (read j g).map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => equal i)
    change w ++ [g.op.eval (((read j g).map (cap j)).map (fun i => w.getD i false))] =
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    rw [mapEq]
    by_cases hNot : g.op = GateOp.not
    · rw [hNot]
      change w ++ [GateOp.not.eval ((read j g).map (fun i => w.getD i false))] =
        w ++ [GateOp.not.eval (g.inputs.map fun i => w.getD i false)]
      rw [← notTake (g.inputs.map _),← List.map_take]
      rcases hv : g.inputs with _ | ⟨u,rest⟩
      · simp only [read,ite_eq_left hNot,hv,List.take_nil,List.filter_nil,List.map_nil]
      · by_cases near : u < 11 + j
        · simp [read,hNot,hv,near]
        · have absent : w.getD u false = false := List.getD_eq_default _ _ (by omega)
          simp [read,hNot,hv,near]
          change GateOp.not.eval [] = GateOp.not.eval [w.getD u false]
          rw [absent] <;> rfl
    · simp only [read,ite_eq_right hNot]
  have sameRun (gs : List Gate) (j : ℕ) (ws : List Bool) (hLen : ws.length = 11 + j)
      (budget : j + gs.length ≤ 18) : (normal gs j).foldl step ws = gs.foldl step ws := by
    induction gs generalizing j ws with
    | nil => rfl
    | cons g gs ih =>
      change (normal gs (j+1)).foldl step (step ws (fix j g)) = gs.foldl step (step ws g)
      have hj : j < 18 := by simp only [List.length_cons] at budget; omega
      rw [fixStep g ws j hLen hj]
      apply ih
      · simp [step,hLen,Nat.add_assoc]
      · simp only [List.length_cons] at budget
        omega
  have evalN (ws : List Bool) (hw : ws.length = 11) : N.eval ws = D.eval ws := by
    change ((normal D.gates 0).foldl step ws).getD 28 false = (D.gates.foldl step ws).getD D.output false
    rw [dOut,sameRun D.gates 0 ws (by simpa using hw) (by omega)]
  have goodN (x : Fin 10 → Bool) : N.eval (input x) = f x :=
    (evalN _ (inLength x)).trans ((evalD _ (inLength x)).trans (computes x))
  have members (g : Gate) (hg : g ∈ N.gates) : ∃ j t, j < 18 ∧ t ∈ D.gates ∧ g = fix j t := by
    obtain ⟨⟨t,j⟩,ht,eq⟩ := List.mem_map.mp hg
    obtain ⟨bound,he⟩ := List.mem_zipIdx' ht
    exact ⟨j,t,by omega,he ▸ List.getElem_mem bound,eq.symm⟩
  have legalN : FanInTwo N := by
    intro g hg
    obtain ⟨j,t,_,ht,rfl⟩ := members g hg
    refine ⟨(dLegal _ ht).1,?_⟩
    change ((read j t).map (cap j)).length ≤ 2
    rw [List.length_map]
    exact (shortRead j t).trans (dLegal _ ht).2
  have sizeN : N.size = 18 := by
    change (normal D.gates 0).length = 18
    simpa only [normal,List.length_map,List.length_zipIdx] using lengthD
  have unary (g : Gate) (hg : g ∈ N.gates) (ho : g.op = GateOp.not) : g.inputs.length ≤ 1 ∧ 29 ∉ g.inputs := by
    obtain ⟨j,t,jlt,_,rfl⟩ := members g hg
    change t.op = GateOp.not at ho
    have inputForm : (fix j t).inputs = ((t.inputs.take 1).filter (fun i => decide (i < 11 + j))).map (cap j) := by
      simp only [fix,read,ite_eq_left ho]
    rw [inputForm]
    refine ⟨?_,?_⟩
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    · intro h
      obtain ⟨u, hu, e⟩ := List.mem_map.mp h
      have earlier : u < 11 + j := of_decide_eq_true (List.mem_filter.mp hu).2
      change (if u < 11 + j then u else 29) = 29 at e
      rw [ite_eq_left earlier] at e
      omega
  have canonical (j : Fin N.gates.length) (i : ℕ) (hi : i ∈ (N.gates.get j).inputs) :
      i < 11 + j.val ∨ i = 29 := by
    have jl : j.val < (D.gates.zipIdx 0).length := by simpa only [N,normal,List.length_map] using j.isLt
    have orig : j.val < D.gates.length := by simpa using jl
    have access : N.gates.get j = fix j.val (D.gates.get ⟨j.val,orig⟩) := by
      change (normal D.gates 0)[j.val]'j.isLt = _
      simp only [normal,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
      rfl
    rw [access] at hi
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
    exact hcap j.val u
  by_cases hn : ∃ g ∈ N.gates, g.op = GateOp.not ∧ g.inputs ≠ []
  · obtain ⟨x,wrong⟩ := negationCase N b legalN sizeN rfl canonical unary hn
    exact wrong (goodN x)
  have onlyConst (g : Gate) (hg : g ∈ N.gates) (ho : g.op = GateOp.not) : g.inputs = [] := by
    by_contra nonempty
    exact hn ⟨g,hg,ho,nonempty⟩
  rcases monotoneCase N b legalN sizeN rfl canonical onlyConst with ⟨r,hr,off⟩|⟨r,hr,off⟩
  · have positiveRows : ∀ r : ℕ, r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ) →
        f (fun i => r.testBit i.val) = true := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have right := (goodN (fun i => r.testBit i.val)).trans (positiveRows r hr)
    change N.eval (input (fun i => r.testBit i.val)) = false at off
    rw [off] at right
    exact Bool.false_ne_true right
  · have negativeRows : ∀ r : ℕ, r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ) →
        f (fun i => r.testBit i.val) = false := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have right := (goodN (fun i => r.testBit i.val)).trans (negativeRows r hr)
    change N.eval (input (fun i => r.testBit i.val)) = true at off
    rw [off] at right
    exact Bool.noConfusion right
