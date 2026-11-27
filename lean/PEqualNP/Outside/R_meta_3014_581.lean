import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_3014_581
    (search : let inputs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
      ∃ ops : List (Bool × ℕ × ℕ), ops.length = 26 ∧
        (∀ j : Fin ops.length, (ops.getD j.val (false,0,0)).2.1 < (ops.getD j.val (false,0,0)).2.2 ∧ (ops.getD j.val (false,0,0)).2.2 < 14+j.val) ∧
        (2097151 : BitVec 58) ∈ ops.foldl (fun (xs : List (BitVec 58)) (g : Bool × ℕ × ℕ) => xs ++ [if g.1 then (xs.getD g.2.1 0) &&& (xs.getD g.2.2 0) else (xs.getD g.2.1 0) ||| (xs.getD g.2.2 0)]) inputs)
    (cover : let inputs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
      let row := (fun (j : ℕ) (i : Fin 14) => (inputs.getD i.val 0).getLsbD j)
      ∀ z : Fin 14 → Bool, (∀ j : Fin 21, ¬row j.val ≤ z) →
        ∃ k : Fin 37, z ≤ row (21+k.val)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  let inputs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  let row := (fun (j : ℕ) (i : Fin 14) => (inputs.getD i.val 0).getLsbD j)
  let step := (fun (xs : List (BitVec 58)) (g : Bool × ℕ × ℕ) => xs ++ [if g.1 then (xs.getD g.2.1 0) &&& (xs.getD g.2.2 0) else (xs.getD g.2.1 0) ||| (xs.getD g.2.2 0)])
  let edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let goal := fun z : Fin 14 → Bool => decide (∃ p l : Fin 14, (p.val,l.val) ∈ edges ∧ z p = true ∧ z l = true)
  change ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 2 ≤ C.size ∧ C.size ≤ 26 ∧
    (∀ z, goal z = true → (∀ y ≤ z, goal y = true → y=z) → C.eval (List.ofFn z) = true) ∧
    ∀ z, goal z = false → (∀ y, z ≤ y → goal y = false → y=z) → C.eval (List.ofFn z) = false
  change ∃ ops : List (Bool × ℕ × ℕ), ops.length=26 ∧
    (∀ j : Fin ops.length, (ops.getD j.val (false,0,0)).2.1 < (ops.getD j.val (false,0,0)).2.2 ∧ (ops.getD j.val (false,0,0)).2.2 < 14+j.val) ∧
    (2097151 : BitVec 58) ∈ ops.foldl step inputs at search
  change ∀ z, (∀ j : Fin 21, ¬row j.val ≤ z) → ∃ k : Fin 37, z ≤ row (21+k.val) at cover
  obtain ⟨ops,sz,valid,found⟩ := search
  obtain ⟨out,hout,value⟩ := List.mem_iff_getElem.mp found
  let mk := fun g : Bool × ℕ × ℕ => (⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩ : Gate)
  let C : Circuit := ⟨ops.map mk,out⟩
  have gates (j : ℕ) (hj : j<ops.length) : gateAt C j = mk ops[j] := by
    change (ops.map mk).getD j ⟨.or,[]⟩ = _
    simp [List.getD,hj]
  have indices (j : ℕ) (h : j < ops.length) :
      (ops[j]'h).2.1 < (ops[j]'h).2.2 ∧ (ops[j]'h).2.2 < 14+j := by
    have hval := valid ⟨j,h⟩
    simpa only [List.getD_eq_getElem _ _ h] using hval
  have fan : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
      cases e : a.1 <;> simp [mk,e]
    · intro j hj i hi
      have h : j<ops.length := by simpa [C] using hj
      rw [gates j h] at hi
      have ha := indices j h
      simp only [mk,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
      simp [mk]
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    have h : j<ops.length := by simpa [C] using hj
    have ha := (indices j h).1.ne
    simpa [C,mk] using ha
  have eval (j : Fin 58) : C.eval (List.ofFn (row j.val)) = (2097151 : BitVec 58).getLsbD j.val := by
    let bit := fun x : BitVec 58 => x.getLsbD j.val
    have get (xs : List (BitVec 58)) (k : ℕ) :
        (xs.map bit).getD k false = bit (xs.getD k 0) := by
      induction xs generalizing k with
      | nil => simp [bit]
      | cons a xs ih => cases k with
        | zero => rfl
        | succ k => exact ih k
    let bs := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have andTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && (b && true)) := rfl
    have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || (b || false)) := rfl
    have fold (gs : List (Bool × ℕ × ℕ)) (xs : List (BitVec 58)) :
        (gs.map mk).foldl bs (xs.map bit) = (gs.foldl step xs).map bit := by
      induction gs generalizing xs with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons,List.foldl_cons]
        have one : bs (xs.map bit) (mk g) = (step xs g).map bit := by
          cases e : g.1 <;> simp only [bs,mk,step,e,ite_true,Bool.false_eq_true,ite_false,List.map_append,
            List.map_cons,List.map_nil,List.cons.injEq,List.append_cancel_left_eq,andTwo,orTwo,Bool.and_true,Bool.or_false,get,and_true]
          all_goals simp [bit]
        rw [one,ih]
    have init : ∀ j : Fin 58, inputs.map (fun t => t.getLsbD j.val) = List.ofFn (row j.val) := by decide +kernel
    change ((ops.map mk).foldl bs (List.ofFn (row j.val))).getD out false = _
    rw [← init j,fold ops inputs,get,List.getD_eq_getElem _ _ hout,value]
  have decoding : ∀ p l : Fin 14, (p.val,l.val) ∈ edges →
      ∃ j : Fin 21, ∀ i : Fin 14, row j.val i = decide (i=p ∨ i=l) := by decide +kernel
  have positive : ∀ j : Fin 21, goal (row j.val) = true := by decide +kernel
  have negative : ∀ k : Fin 37, goal (row (21+k.val)) = false := by decide +kernel
  have bitsA : ∀ j : Fin 21, (2097151 : BitVec 58).getLsbD j.val = true := by decide +kernel
  have bitsB : ∀ k : Fin 37, (2097151 : BitVec 58).getLsbD (21+k.val) = false := by decide +kernel
  have size : C.size=26 := by
    change (ops.map mk).length = 26
    simpa using sz
  refine ⟨C,fan,nd,by omega,by omega,?_,?_⟩
  · intro z h minimal
    obtain ⟨p,l,edge,hp,hl⟩ := of_decide_eq_true h
    obtain ⟨j,same⟩ := decoding p l edge
    have le : row j.val ≤ z := by
      intro i
      rw [same]
      by_cases e : i=p ∨ i=l
      · rcases e with rfl | rfl <;> simp [*]
      · simp [e]
    rw [← minimal _ le (positive j)]
    exact (eval ⟨j.val,by omega⟩).trans (bitsA j)
  · intro z h maximal
    have miss (j : Fin 21) : ¬row j.val ≤ z := by
      intro le
      obtain ⟨p,l,edge,hp,hl⟩ := of_decide_eq_true (positive j)
      have zp := le p
      have zl := le l
      rw [hp] at zp
      rw [hl] at zl
      have hit : goal z = true := decide_eq_true ⟨p,l,edge,le_antisymm (Bool.le_true _) zp,le_antisymm (Bool.le_true _) zl⟩
      rw [hit] at h
      contradiction
    obtain ⟨k,le⟩ := cover z miss
    rw [← maximal _ le (negative k)]
    exact (eval ⟨21+k.val,by omega⟩).trans (bitsB k)