import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2161_74 :
    (let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (pre post : List Gate) (q : Gate) (out : ℕ) (v : Fin 9),
      let C : Circuit := ⟨pre ++ q :: post,out⟩
      let d := circuitFun 9 (⟨pre ++ ⟨.or, []⟩ :: post,out⟩ : Circuit)
      let z : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y => Fin.insertNth v false y
      FanInTwo C → (∀ a ∈ pre ++ post, a.op ≠ .not) → q.op = .not → circuitFun 9 C = f →
      d ≠ f → d ∘ z = f ∘ z → HasCircuitSize 8 (f ∘ z) (C.size - 3)) →
    (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
      (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
    (let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ D : Circuit, FanInTwo D → (∀ a ∈ D.gates, a.op ≠ .not) →
      (⟨.or, []⟩ : Gate) ∈ D.gates → circuitFun 9 D = f → 16 ≤ D.size) →
    (let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ (pre post : List Gate) (q : Gate) (out : ℕ),
      let C : Circuit := ⟨pre ++ q :: post,out⟩
      let d := circuitFun 9 (⟨pre ++ ⟨.or, []⟩ :: post,out⟩ : Circuit)
      FanInTwo C → (∀ a ∈ pre ++ post, a.op ≠ .not) → q.op = .not → circuitFun 9 C = f →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
        (fun y : Fin 8 → Bool => d (Fin.insertNth v false y)) ≠
        (fun y : Fin 8 → Bool => f (Fin.insertNth v false y))) → 16 ≤ C.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size) := by
  intro compression prior positiveLower dispersed C hf hnot hfirst hgraph
  let f := fun x : Fin 9 → Bool =>
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have cofactorLower (v : Fin 9) (hv : v = 4 ∨ v = 6 ∨ v = 7) :
      ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => f (Fin.insertNth v false y)) 12 := by
    let t := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
      (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
    let p : Fin 8 → Fin 8 := if v = 6 then ![1,0,4,7,5,2,6,3] else if v = 7 then ![2,1,0,4,6,3,5,7] else id
    have iso (y : Fin 8 → Bool) : f (Fin.insertNth v false (y ∘ p)) = t y := by
      rcases hv with rfl | rfl | rfl
      all_goals simp only [f,List.any_cons,List.any_nil,Bool.or_false]
      · change ((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 3 && false) || ((false && y 0) || ((y 0 && y 4) || ((y 1 && y 5) || ((y 2 && y 6) || ((y 3 && y 7) || ((y 4 && y 6) || ((y 5 && y 7) || (y 7 && y 4)))))))))))) = _
        simp [t,Bool.or_assoc]
      · change ((y 1 && y 0) || ((y 0 && y 4) || ((y 4 && y 7) || ((y 7 && y 5) || ((y 5 && y 1) || ((y 1 && y 2) || ((y 0 && false) || ((y 4 && y 6) || ((y 7 && y 3) || ((y 2 && y 6) || ((false && y 3) || (y 3 && y 2)))))))))))) = _
        simp only [t,Bool.and_false,Bool.false_and,Bool.false_or,Bool.or_false]
        ac_rfl
      · change ((y 2 && y 1) || ((y 1 && y 0) || ((y 0 && y 4) || ((y 4 && y 6) || ((y 6 && y 2) || ((y 2 && y 3) || ((y 1 && y 5) || ((y 0 && false) || ((y 4 && y 7) || ((y 3 && false) || ((y 5 && y 7) || (y 7 && y 3)))))))))))) = _
        simp only [t,Bool.and_false,Bool.false_or,Bool.or_false]
        ac_rfl
    rintro ⟨E,hfan,hs,he⟩
    let idx (i : ℕ) := if h : i < 8 then (p ⟨i,h⟩).val else i
    let tr (g : Gate) : Gate := ⟨g.op,g.inputs.map idx⟩
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have snoc (w : List Bool) (b : Bool) (i : ℕ) :
        (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
      by_cases h : i < w.length
      · rw [List.getD_append _ _ _ _ h,if_pos h]
      · by_cases eq : i = w.length
        · subst i; simp
        · rw [if_neg h,if_neg eq,List.getD_eq_default _ _ (by simp; omega)]
    have sim (gs : List Gate) (w z : List Bool) (hl : w.length = z.length) (h8 : 8 ≤ z.length)
        (hh : ∀ i, w.getD i false = z.getD (idx i) false) :
        ∀ i, (gs.foldl step w).getD i false = ((gs.map tr).foldl step z).getD (idx i) false := by
      induction gs generalizing w z with
      | nil => exact hh
      | cons g gs ih =>
        apply ih (step w g) (step z (tr g)) (by simp [step,hl]) (by simp [step]; omega)
        intro i
        have hval : g.op.eval (g.inputs.map fun j => w.getD j false) =
            (tr g).op.eval ((tr g).inputs.map fun j => z.getD j false) := by
          simp only [tr,List.map_map,hh]; rfl
        have hlt : i < w.length ↔ idx i < z.length := by
          by_cases h : i < 8
          · have hp := (p ⟨i,h⟩).isLt
            simp only [idx,dif_pos h]; omega
          · simp only [idx,dif_neg h,hl]
        have heq : i = w.length ↔ idx i = z.length := by
          by_cases h : i < 8
          · have hp := (p ⟨i,h⟩).isLt
            simp only [idx,dif_pos h]; omega
          · simp only [idx,dif_neg h,hl]
        simp only [step,snoc,← hlt,← heq,hval]
        rw [hh]
    apply prior
    refine ⟨⟨E.gates.map tr,idx E.output⟩,?_,?_,?_⟩
    · intro g hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      simpa [tr] using hfan a ha
    · change (E.gates.map tr).length ≤ 12
      rw [List.length_map]
      exact hs
    · intro y
      have hstart (i : ℕ) : (List.ofFn (y ∘ p)).getD i false = (List.ofFn y).getD (idx i) false := by
        by_cases h : i < 8
        · have hk := (p ⟨i,h⟩).isLt
          rw [show idx i = (p ⟨i,h⟩).val from dif_pos h,
            List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using hk)]
          simp only [List.getElem_ofFn,Function.comp_apply]
        · rw [show idx i = i from dif_neg h,List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      exact (sim E.gates _ _ (by simp) (by simp) hstart E.output).symm.trans ((he _).trans (iso y))
  have he : circuitFun 9 C = f := by
    rw [hgraph]
    symm
    funext x
    simp only [f,List.any_cons,List.any_nil,Bool.or_false]
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 ||
      (x 6 && x 8 || x 8 && x 5))))))))))) = _
    simp only [Bool.or_assoc]
  obtain ⟨j,hq,hu⟩ := hnot
  let pre := C.gates.take j.val
  let post := C.gates.drop (j.val + 1)
  let q := C.gates.get j
  have shape : C.gates = pre ++ q :: post := by
    simp only [pre,q,post,List.get_eq_getElem,← List.drop_eq_getElem_cons j.isLt,List.take_append_drop]
  have noNot : ∀ a ∈ pre ++ post, a.op ≠ .not := by
    intro a ha hn
    obtain hp | hs := List.mem_append.mp ha
    · obtain ⟨k,hk,hka⟩ := List.mem_iff_getElem.mp hp
      have hk' : k < j.val := Nat.lt_of_lt_of_le hk (List.length_take_le _ _)
      have hkg : k < C.gates.length := Nat.lt_trans hk' j.isLt
      have hget : C.gates.get ⟨k,hkg⟩ = a := by
        simpa only [pre,List.getElem_take,List.get_eq_getElem] using hka
      exact hk'.ne (congrArg Fin.val (hu ⟨k,hkg⟩ (by rw [hget,hn])))
    · obtain ⟨k,hk,hka⟩ := List.mem_iff_getElem.mp hs
      have hkg : j.val + 1 + k < C.gates.length := by
        simp only [post,List.length_drop] at hk
        omega
      have hget : C.gates.get ⟨j.val + 1 + k,hkg⟩ = a := by
        simpa only [post,List.getElem_drop,List.get_eq_getElem] using hka
      have h := congrArg Fin.val (hu ⟨j.val + 1 + k,hkg⟩ (by rw [hget,hn]))
      change j.val + 1 + k = j.val at h
      omega
  have eqC : (⟨pre ++ q :: post,C.output⟩ : Circuit) = C := by cases C; simp only [← shape]
  let D : Circuit := ⟨pre ++ ⟨.or,[]⟩ :: post,C.output⟩
  let d := circuitFun 9 D
  have hf' : FanInTwo (⟨pre ++ q :: post,C.output⟩ : Circuit) := eqC.symm ▸ hf
  have he' : circuitFun 9 (⟨pre ++ q :: post,C.output⟩ : Circuit) = f := eqC.symm ▸ he
  by_cases hd : d = f
  · have hFan : FanInTwo D := by
      intro a ha
      change a ∈ pre ++ ⟨.or,[]⟩ :: post at ha
      rcases List.mem_append.mp ha with h | h
      · exact hf' a (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · simp
        · exact hf' a (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hpos : ∀ a ∈ D.gates, a.op ≠ .not := by
      intro a ha
      change a ∈ pre ++ ⟨.or,[]⟩ :: post at ha
      rcases List.mem_append.mp ha with h | h
      · exact noNot a (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · intro h; cases h
        · exact noNot a (List.mem_append_right _ h)
    have hzero : (⟨.or,[]⟩ : Gate) ∈ D.gates := List.mem_append_right _ (by simp)
    have hh := positiveLower D hFan hpos hzero hd
    have hsize : D.size = C.size := by unfold Circuit.size; rw [shape]; simp [D]
    exact hsize ▸ hh
  · let z (v : Fin 9) (y : Fin 8 → Bool) : Fin 9 → Bool := Fin.insertNth v false y
    by_cases hstar : ∃ v : Fin 9, (v = 4 ∨ v = 6 ∨ v = 7) ∧ d ∘ z v = f ∘ z v
    · obtain ⟨v,hv,hs⟩ := hstar
      obtain ⟨E,hE,hsize,hval⟩ := compression pre post q C.output v hf' noNot hq he' hd hs
      rw [eqC] at hsize
      by_contra! hsmall
      exact cofactorLower v hv ⟨E,hE,by omega,hval⟩
    · rw [← eqC]
      exact dispersed pre post q C.output hf' noNot hq he' (eqC.symm ▸ hfirst)
        (fun v hv hs => hstar ⟨v,hv,hs⟩)
