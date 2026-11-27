import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotPremium

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2909_1
  (order : ∀ (n : ℕ) (C : Circuit), FanInTwo C → AtMostOneNot C.gates →
    ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    let atBit := fun b => circuitFun n ⟨replaceByConst C.gates q.val b,C.output⟩
    (atBit true x ≠ circuitFun n C x → atBit false y = circuitFun n C y) ∧
    (atBit false y ≠ circuitFun n C y → atBit true x = circuitFun n C x))
  (cut : let F := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ P D : Circuit, Monotone2 P → Monotone2 D → P.size + D.size = 14 →
    (∀ x : Fin 9 → Bool, (P.wires (List.ofFn x)).getD 9 false = (x 0 && x 2)) →
    let H := fun (v : Bool) (x : Fin 9 → Bool) => D.eval (P.wires (List.ofFn x) ++ [v])
    ∀ e t : Fin 9 → Bool, F e = true → F t = false →
    H false e = false → H true t = true →
    circuitFun 9 P e = false → circuitFun 9 P t = true →
    (∀ x, (∀ j, x j = true → e j = true) → H true x = F x) →
    (∀ x, (∀ j, t j = true → x j = true) → H false x = F x) →
    ∃ x, H (!(circuitFun 9 P x)) x ≠ F x) :
  ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 2)) →
    C.size = 15 → AtMostOneNot C.gates →
    ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not →
    (∃ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ),
      circuitFun 9 ⟨replaceByConst C.gates q.val false, C.output⟩
        (fun j => m.testBit j.val) = false) →
    (∃ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
      circuitFun 9 ⟨replaceByConst C.gates q.val true, C.output⟩
        (fun j => m.testBit j.val) = true) →
    circuitFun 9 C ≠ fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
      (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5) := by
  intro C fan first size one q qnot missed spurious correct
  let i := q.val
  have hi : i < C.gates.length := q.isLt
  have hq : i ≠ 0 := by
    intro iz
    obtain ⟨gs, out⟩ := C
    cases gs with
    | nil => simp at hi
    | cons hd tl =>
      have eq0 : q = ⟨0,by simp⟩ := Fin.ext iz
      have e : hd.op = GateOp.not := by rw [eq0] at qnot; exact qnot
      let step (w : List Bool) (g : Gate) :=
        w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
      have keep (ls : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
          (ls.foldl step w).getD j false = w.getD j false := by
        induction ls generalizing w with
        | nil => rfl
        | cons a as ih =>
          rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hj
      have ha := first (fun _ => false)
      let w := List.ofFn (fun _ : Fin 9 => false)
      change (tl.foldl step (step w hd)).getD 9 false = false at ha
      have ew : w = List.replicate 9 false := by decide
      have get (j : Nat) : w.getD j false = false := by
        rw [ew]
        by_cases jlt : j < 9
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
                (show j < (List.replicate 9 false).length by simpa using jlt),
              List.getElem_replicate]
          rfl
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt jlt)]
      have actual : hd.op.eval (hd.inputs.map fun j => w.getD j false) = true := by
        rw [e]
        change (!(hd.inputs.map (fun j => w.getD j false)).headD false) = true
        simp only [get]
        cases hd.inputs <;> rfl
      have result := ha
      change (tl.foldl step (step w hd)).getD 9 false = false at result
      rw [keep tl (step w hd) 9 (by simp [step, w])] at result
      change (w ++ [hd.op.eval (hd.inputs.map fun j => w.getD j false)]).getD 9 false = false at result
      rw [actual, List.getD_append_right _ _ _ _ (by simp [w])] at result
      simp [w] at result

  let pre := C.gates.take i
  let post := C.gates.drop (i+1)
  let P : Circuit := ⟨pre,C.gates[i].inputs.headD (9+i)⟩
  let D : Circuit := ⟨post,C.output⟩
  have split : pre ++ C.gates[i] :: post = C.gates := by
    calc
      _ = (C.gates.take i ++ [C.gates[i]]) ++ C.gates.drop (i+1) := (List.append_assoc ..).symm
      _ = C.gates := by rw [List.take_append_getElem hi,List.take_append_drop]
  have good (j : Fin C.gates.length) (ne : j ≠ q) :
      (C.gates.get j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (C.gates.get j).inputs.length ≤ 2 := by
    have h := fan _ (List.getElem_mem j.isLt)
    have hn : (C.gates.get j).op ≠ GateOp.not := by
      intro hn
      obtain ⟨f,h⟩ := one
      obtain ⟨a,ha⟩ := h j hn
      obtain ⟨b,hb⟩ := h q qnot
      exact ne (ha.symm.trans ((congrArg f (Subsingleton.elim a b)).trans hb))
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h ⊢
    tauto
  have pmono : Monotone2 P := by
    intro g hg
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
    change j < (C.gates.take i).length at hj
    simp only [List.length_take] at hj
    have lt : j < C.gates.length := by omega
    have e : C.gates[j] = g := by simpa [P,pre] using eq
    rw [←e]
    exact good ⟨j,lt⟩ (fun he => by have := congrArg Fin.val he; change j = i at this; omega)
  have dmono : Monotone2 D := by
    intro g hg
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
    change j < (C.gates.drop (i+1)).length at hj
    simp only [List.length_drop] at hj
    have lt : i+1+j < C.gates.length := by omega
    have e : C.gates[i+1+j] = g := by simpa [D,post] using eq
    rw [←e]
    exact good ⟨_,lt⟩ (fun he => by have := congrArg Fin.val he; change i+1+j = i at this; omega)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have keep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  let W (x : Fin 9 → Bool) := P.wires (List.ofFn x)
  have plen (x : Fin 9 → Bool) : (W x).length = 9+i := by
    change (pre.foldl step (List.ofFn x)).length = _
    simp [len,pre,Nat.min_eq_left hi.le]
  have pfirst (x : Fin 9 → Bool) : (W x).getD 9 false = (x 0 && x 2) := by
    have h := first x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at h
    rw [←split,List.foldl_append] at h
    change ((C.gates[i] :: post).foldl step (W x)).getD 9 false = _ at h
    rwa [keep _ _ _ (by rw [plen]; omega)] at h
  let H (v : Bool) (x : Fin 9 → Bool) := D.eval (W x ++ [v])
  let A (v : Bool) := circuitFun 9 ⟨replaceByConst C.gates q.val v,C.output⟩
  have cl (v : Bool) (x : Fin 9 → Bool) : A v x = H v x := by
    change ((C.gates.set i (constGate v)).foldl step (List.ofFn x)).getD C.output false = _
    rw [List.set_eq_take_append_cons_drop,ite_eq_left hi,List.foldl_append,List.foldl_cons]
    cases v <;> rfl
  have source (x : Fin 9 → Bool) : circuitFun 9 C x = H (!(circuitFun 9 P x)) x := by
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
    rw [←split,List.foldl_append,List.foldl_cons]
    suffices ev : C.gates[i].op.eval (C.gates[i].inputs.map fun j => (W x).getD j false) =
        !(circuitFun 9 P x) by
      exact congrArg (fun v => H v x) ev
    change _ = !((W x).getD (C.gates[i].inputs.headD (9+i)) false)
    rw [show C.gates[i].op = GateOp.not from qnot]
    cases he : C.gates[i].inputs with
    | nil =>
      change (!false) = (!((W x).getD (9+i) false))
      rw [List.getD_eq_default _ false (show (W x).length ≤ 9+i by rw [plen])]
    | cons => rfl
  let F := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let row (m : ℕ) (j : Fin 9) := m.testBit j.val
  obtain ⟨em,emem,miss⟩ := missed
  obtain ⟨tm,tmem,spur⟩ := spurious
  let e := row em
  let t := row tm
  have fe : F e = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at emem
    rcases emem with h|h|h|h|h|h|h|h|h|h|h|h <;> subst em <;> decide
  have ft : F t = false := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at tmem
    rcases tmem with h|h|h|h|h|h|h|h|h|h|h|h <;> subst tm <;> decide
  have full (x : Fin 9 → Bool) : circuitFun 9 C x = F x := congrFun correct x
  change A false e = false at miss
  change A true t = true at spur
  have me : A false e ≠ circuitFun 9 C e := by rw [miss,full,fe]; decide
  have st : A true t ≠ circuitFun 9 C t := by rw [spur,full,ft]; decide
  have pe : circuitFun 9 P e = false := by
    cases he : circuitFun 9 P e
    · rfl
    · apply (me _).elim
      rw [source,he,cl]; rfl
  have pt : circuitFun 9 P t = true := by
    cases ht : circuitFun 9 P t
    · apply (st _).elim
      rw [source,ht,cl]; rfl
    · rfl
  have sizePD : P.size+D.size = 14 := by
    change (C.gates.take i).length + (C.gates.drop (i+1)).length = _
    change C.gates.length = 15 at size
    simp only [List.length_take,List.length_drop]; omega
  obtain ⟨x,hx⟩ := cut P D pmono dmono sizePD pfirst e t fe ft
    ((cl false e).symm.trans miss) ((cl true t).symm.trans spur) pe pt
    (fun x hx => (cl true x).symm.trans (((order 9 C fan one q qnot x e hx).2 me).trans (full x)))
    (fun x hx => (cl false x).symm.trans (((order 9 C fan one q qnot t x hx).1 st).trans (full x)))
  exact hx ((source x).symm.trans (full x))
