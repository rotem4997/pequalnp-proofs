import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7103_728
    (nestedMeet : let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      ∀ C : Circuit, C.size ≤ 19 → TopForm.IsAO2 10 C → C.gates[0]? = some ⟨.or,[0,1]⟩ →
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = E.any fun e => x e.1 && x e.2) →
        (∀ i : Fin 10, ∃ g ∈ C.gates.tail, i.val ∈ g.inputs) →
        (∃ i j : ℕ, (gateAt C i).op = .and ∧
          (gateAt C j).op = .and ∧ InCone 10 C i j ∧
          (j = C.output-10 ∨ InCone 10 C j (C.output-10))) →
        (gateAt C (C.output-10)).op = .and →
        ∃ j : ℕ, 0 < j ∧ j < C.size ∧ ∃ a b : Fin 10, a ≠ b ∧
          (E.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = false ∧
          (fun x => BlindGate.wireValue C 10 x (10+j)) = fun x => x a && x b)
    (nestedJoin : let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      ∀ C : Circuit, C.size ≤ 19 → TopForm.IsAO2 10 C → C.gates[0]? = some ⟨.or,[0,1]⟩ →
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = E.any fun e => x e.1 && x e.2) →
        (∀ i : Fin 10, ∃ g ∈ C.gates.tail, i.val ∈ g.inputs) →
        (∃ i j : ℕ, (gateAt C i).op = .and ∧
          (gateAt C j).op = .and ∧ InCone 10 C i j ∧
          (j = C.output-10 ∨ InCone 10 C j (C.output-10))) →
        (gateAt C (C.output-10)).op = .or →
        ∃ j : ℕ, 0 < j ∧ j < C.size ∧ ∃ a b : Fin 10, a ≠ b ∧
          (E.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = false ∧
          (fun x => BlindGate.wireValue C 10 x (10+j)) = fun x => x a && x b)
    : (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → ¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  
  let Signal := (Fin 10 → Bool) → Bool
  
  let zero : Signal := fun _ => false
  
  let one : Signal := fun _ => true
  
  let good (A L : List Signal) : Prop :=
    ∀ j : Fin L.length,
      let W := zero :: one :: (A ++ L.take j.val)
      L.get j ∉ W ∧ ∃ u ∈ W, ∃ v ∈ W,
        (L.get j = fun x => u x && v x) ∨ (L.get j = fun x => u x || v x)
  
  let legal (width : ℕ) (gs : List Gate) : Prop :=
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ i k, g.inputs = [i,k] ∧ i ≠ k ∧ i < width+j ∧ k < width+j
  
  have evalAnd (s : List Bool) : GateOp.and.eval s = s.all id := rfl
  
  have evalOr (s : List Bool) : GateOp.or.eval s = s.any id := rfl
  
  have first (A : List Signal) (f : Signal)
      (fresh : f ∉ zero :: one :: A)
      (cl : ∃ u ∈ zero :: one :: A, ∃ v ∈ zero :: one :: A,
        (f = fun x => u x && v x) ∨ (f = fun x => u x || v x)) :
      ∃ a b : ℕ, a < A.length ∧ b < A.length ∧ a ≠ b ∧ ∃ op : GateOp,
        (op = .and ∨ op = .or) ∧ ∀ x : Fin 10 → Bool,
          f x = op.eval [((A.map fun s => s x).getD a false), ((A.map fun s => s x).getD b false)] := by
    obtain ⟨u, hu, v, hv, eq⟩ := cl
    have nu : u ∈ A := by
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | ok
      · rcases eq with eq | eq
        · have e : f = zero := by rw [eq]; funext x; simp [zero]
          exact (fresh (List.mem_cons.mpr (.inl e))).elim
        · have e : f = v := by simpa [zero] using eq
          exact (fresh (e ▸ hv)).elim
      · rcases eq with eq | eq
        · have e : f = v := by simpa [one] using eq
          exact (fresh (e ▸ hv)).elim
        · have e : f = one := by rw [eq]; funext x; simp [one]
          exact (fresh (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl e))))).elim
      · exact ok
    have nv : v ∈ A := by
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | ok
      · rcases eq with eq | eq
        · have e : f = zero := by rw [eq]; funext x; simp [zero]
          exact (fresh (List.mem_cons.mpr (.inl e))).elim
        · have e : f = u := by simpa [zero] using eq
          exact (fresh (e ▸ hu)).elim
      · rcases eq with eq | eq
        · have e : f = u := by simpa [one] using eq
          exact (fresh (e ▸ hu)).elim
        · have e : f = one := by rw [eq]; funext x; simp [one]
          exact (fresh (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl e))))).elim
      · exact ok
    have ne : u ≠ v := by
      intro same
      subst v
      have e : f = u := by rcases eq with h | h <;> simpa using h
      exact fresh (e ▸ hu)
    obtain ⟨a, ha⟩ := List.getElem?_of_mem nu
    obtain ⟨b, hb⟩ := List.getElem?_of_mem nv
    have an : a < A.length := by
      by_contra! h
      have ee : A[a]? = none := List.getElem?_eq_none h
      rw [ee] at ha
      contradiction
    have bn : b < A.length := by
      by_contra! h
      have ee : A[b]? = none := List.getElem?_eq_none h
      rw [ee] at hb
      contradiction
    have ab : a ≠ b := by
      intro eqab
      subst b
      exact ne (Option.some.inj (ha.symm.trans hb))
    refine ⟨a,b,an,bn,ab,?_⟩
    rcases eq with eq | eq
    · exact ⟨.and, Or.inl rfl, fun x => by simp [eq,ha,hb,evalAnd]⟩
    · exact ⟨.or, Or.inr rfl, fun x => by simp [eq,ha,hb,evalOr]⟩
  
  have realize (A L : List Signal) (h : good A L) :
      ∃ gs : List Gate, gs.length = L.length ∧ legal A.length gs ∧
        ∀ x : Fin 10 → Bool, (Circuit.mk gs 0).wires (A.map fun s => s x) =
          ((A ++ L).map fun s => s x) := by
    induction L generalizing A with
    | nil =>
      refine ⟨[], rfl, fun j g hg => by simp at hg, fun x => ?_⟩
      change (A.map fun s : Signal => s x) = ((A ++ []).map fun s : Signal => s x)
      simp
    | cons f L ih =>
      have head := h ⟨0, by simp⟩
      have fresh : f ∉ zero :: one :: A := by simpa using head.1
      have cl : ∃ u ∈ zero :: one :: A, ∃ v ∈ zero :: one :: A,
          (f = fun x => u x && v x) ∨ (f = fun x => u x || v x) := by simpa using head.2
      obtain ⟨a,b,abound,bbound,ne,op,hop,e⟩ := first A f fresh cl
      have htail : good (A ++ [f]) L := by
        intro j
        simpa [List.append_assoc] using h j.succ
      obtain ⟨gs,sz,goodgs,ev⟩ := ih (A ++ [f]) htail
      let gate : Gate := ⟨op,[a,b]⟩
      refine ⟨gate :: gs, by simp [sz], ?_, ?_⟩
      · intro j g hg
        cases j with
        | zero =>
          have eq : gate = g := by simpa using hg
          subst g
          exact ⟨hop,a,b,rfl,ne,by simpa using abound,by simpa using bbound⟩
        | succ j =>
          obtain ⟨opg,a',b',inputs,nodup,lt1,lt2⟩ := goodgs j g (by simpa using hg)
          exact ⟨opg,a',b',inputs,nodup,by simp at lt1; omega,by simp at lt2; omega⟩
      · intro x
        have first_val : gate.op.eval (gate.inputs.map fun i => (A.map fun s => s x).getD i false) = f x := by
          simpa [gate] using (e x).symm
        change (Circuit.mk gs 0).wires ((A.map fun s => s x) ++ [_]) = _
        rw [first_val]
        simpa [List.append_assoc] using ev x
  
  
  let edges : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  
  let target : Signal := fun x => edges.any fun e => x e.1 && x e.2
  
  let basis : List Signal := (List.ofFn fun i : Fin 10 => fun x => x i) ++ [fun x => x 0 || x 1]
  
  have ao_of_legal (n : ℕ) (C : Circuit) (hl : legal n C.gates) : TopForm.IsAO2 n C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.getElem?_of_mem hg
      exact (hl j g hj).1
    · intro j hj a ha
      have e : C.gates[j]? = some (gateAt C j) := by
        change C.gates[j]? = some (C.gates.getD j ⟨.or,[]⟩)
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      obtain ⟨_,l,r,inputs,_,hlt,hrt⟩ := hl j _ e
      rw [inputs] at ha
      simp only [List.mem_cons, List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj⟩ := List.getElem?_of_mem hg
      obtain ⟨_,a,b,inputs,_,_,_⟩ := hl j g hj
      rw [inputs]
      rfl
  
  have circuit (L : List Signal) (lg : L.length ≤ 18) (g : good basis L)
      (ban : ∀ w ∈ L, ∀ a b : Fin 10, a ≠ b →
        ¬ (edges.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = true →
        w ≠ (fun x => x a && x b))
      (hit : target ∈ L) :
      ∃ C : Circuit, C.size ≤ 19 ∧ TopForm.IsAO2 10 C ∧
        C.gates[0]? = some ⟨.or, [0,1]⟩ ∧ 11 ≤ C.output ∧ C.output < 10 + C.size ∧
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = target x) ∧
        (∀ j, 0 < j → j < C.size → ∀ a b : Fin 10, a ≠ b →
          ¬ (edges.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = true →
          (fun x => BlindGate.wireValue C 10 x (10+j)) ≠ (fun x => x a && x b)) := by
    obtain ⟨gs,gs_len,gs_legal,gs_eval⟩ := realize basis L g
    obtain ⟨j,hj⟩ := List.getElem?_of_mem hit
    have ht : j < L.length := by
      by_contra! contra
      rw [List.getElem?_eq_none contra] at hj
      contradiction
    let fixed : Gate := ⟨.or,[0,1]⟩
    let C : Circuit := ⟨fixed :: gs, 11+j⟩
    have bound : C.size = 1 + L.length := by
      change (fixed :: gs).length = 1 + L.length
      simp [gs_len]
      omega
    have legalC : legal 10 C.gates := by
      intro k w hw
      cases k with
      | zero =>
        have e : fixed = w := by simpa [C] using hw
        subst w
        exact ⟨Or.inr rfl,0,1,rfl,by decide,by decide,by decide⟩
      | succ k =>
        obtain ⟨op,a,b,inp,ne,a',b'⟩ := gs_legal k w (by simpa [C] using hw)
        simp [basis] at a' b'
        exact ⟨op,a,b,inp,ne,by omega,by omega⟩
    have allw (x : Fin 10 → Bool) : C.wires (List.ofFn x) = ((basis++L).map fun w => w x) := by
      have base (i : Fin 10 → Bool) : (basis.map fun w => w i) = List.ofFn i ++ [i 0 || i 1] := by
        simp [basis]
      have fixed_eval : fixed.op.eval (fixed.inputs.map fun i => (List.ofFn x).getD i false) =
          (x 0 || x 1) := by
        simp [fixed,evalOr,List.getD_eq_getElem?_getD]
      change (Circuit.mk gs 0).wires (List.ofFn x ++ [_]) = _
      rw [fixed_eval, ← base]
      exact gs_eval x
    have wire (x : Fin 10 → Bool) (k : ℕ) (w : Signal) (hk : L[k]? = some w) :
        BlindGate.wireValue C 10 x (11+k) = w x := by
      change (C.wires (List.ofFn x)).getD (11+k) false = w x
      rw [allw,List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_append_right (by simp [basis])]
      have offset : 11+k-basis.length=k := by simp [basis]
      rw [offset,hk]
      rfl
    have out_len : C.output < 10 + C.size := by
      change 11 + j < 10 + C.size
      omega
    refine ⟨C,by omega,ao_of_legal _ _ legalC,rfl,by simp [C],out_len,?_,?_⟩
    · intro x
      exact wire x j target hj
    · intro k hkpos hk a b hab nonedge eq
      let l := k-1
      have hkl : k = l+1 := by omega
      have len : l < L.length := by omega
      let w : Signal := L[l]
      have hw : L[l]? = some w := by simp [w,len]
      apply ban w (List.getElem_mem (l := L) len) a b hab nonedge
      funext x
      have e := wire x l w hw
      have index : 11+l = 10+k := by omega
      rw [index] at e
      exact e.symm.trans (congrFun eq x)
  
  have agree_if_unused (i : ℕ) (gs : List Gate)
      (avoid : ∀ g ∈ gs, i ∉ g.inputs) (a b : List Bool) (len : a.length = b.length)
      (rel : ∀ k, k ≠ i → a.getD k false = b.getD k false) :
      ∀ k, k ≠ i → ((Circuit.mk gs 0).wires a).getD k false =
        ((Circuit.mk gs 0).wires b).getD k false := by
    induction gs generalizing a b with
    | nil => exact rel
    | cons g gs ih =>
      have mp : (g.inputs.map fun k => a.getD k false) = (g.inputs.map fun k => b.getD k false) := by
        rw [List.map_congr_left]
        intro k h
        exact rel k (fun e => avoid g List.mem_cons_self (e ▸ h))
      let v := g.op.eval (g.inputs.map fun k => b.getD k false)
      change ∀ k, k ≠ i → ((Circuit.mk gs 0).wires (a ++ [_])).getD k false =
        ((Circuit.mk gs 0).wires (b ++ [v])).getD k false
      rw [mp]
      change ∀ k, k ≠ i → ((Circuit.mk gs 0).wires (a ++ [v])).getD k false = _
      apply ih (fun gate h => avoid gate (List.mem_cons_of_mem g h)) _ _ (by simp [len])
      intro j ne
      by_cases less : j < a.length
      · rw [List.getD_append _ _ _ _ less, List.getD_append _ _ _ _ (by omega)]
        exact rel j ne
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),len]
  
  let other (i : Fin 10) : Fin 10 := ![1,0,1,2,0,0,1,2,3,4] i
  
  let lo (i : Fin 10) (j : Fin 10) : Bool := decide (j = other i)
  
  let hi (i : Fin 10) (j : Fin 10) : Bool := lo i j || decide (j = i)
  
  have all_inputs_read (C : Circuit) (start : C.gates[0]? = some ⟨.or,[0,1]⟩)
      (out : 11 ≤ C.output) (eval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = target x) :
      ∀ i : Fin 10, ∃ g ∈ C.gates.tail, (i : ℕ) ∈ g.inputs := by
    have probe : ∀ i : Fin 10, target (lo i) = false ∧ target (hi i) = true ∧
        (lo i 0 || lo i 1) = (hi i 0 || hi i 1) := by decide +kernel
    intro i
    by_contra! avoid
    rcases C with ⟨gs,output⟩
    cases gs with
    | nil => simp at start
    | cons g gs =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at start
      subst g
      let a := List.ofFn (lo i) ++ [lo i 0 || lo i 1]
      let b := List.ofFn (hi i) ++ [hi i 0 || hi i 1]
      have al : a.length = 11 := by simp [a]
      have bl : b.length = 11 := by simp [b]
      have rel (k : ℕ) (ne : k ≠ (i : ℕ)) : a.getD k false = b.getD k false := by
        by_cases kl : k < 10
        · have red : ∀ x : Fin 10 → Bool, (List.ofFn x ++ [x 0 || x 1]).getD k false = x ⟨k,kl⟩ := by
            intro x
            rw [List.getD_append _ _ _ _ (by simpa using kl),List.getD_eq_getElem _ _ (by simpa using kl)]
            exact List.getElem_ofFn _
          change (List.ofFn (lo i) ++ [_]).getD k false = (List.ofFn (hi i) ++ [_]).getD k false
          rw [red,red]
          have dne : (⟨k,kl⟩ : Fin 10) ≠ i := fun e => ne (congrArg Fin.val e)
          simp [hi,dne]
        · change (List.ofFn (lo i) ++ [_]).getD k false = (List.ofFn (hi i) ++ [_]).getD k false
          rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
          simp [(probe i).2.2]
      have eq := agree_if_unused (i : ℕ) gs avoid a b (al.trans bl.symm) rel output
        (by have lt := i.isLt; change 11 ≤ output at out; omega)
      have fold (x : Fin 10 → Bool) :
          (Circuit.mk (⟨.or,[0,1]⟩ :: gs) output).eval (List.ofFn x) =
            ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 1])).getD output false := by
        change ((Circuit.mk gs 0).wires (List.ofFn x ++ [_])).getD output false = _
        simp [evalOr,List.getD_eq_getElem?_getD]
      rw [← fold (lo i), ← fold (hi i), eval,eval,(probe i).1,(probe i).2.1] at eq
      contradiction
  have flat (C : Circuit) (hAO : TopForm.IsAO2 10 C)
      (hOut : 11 ≤ C.output) (hSmall : C.output < 10 + C.size)
      (hVal : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = target x)
      (noNest : ¬∃ i j : ℕ, (gateAt C i).op = .and ∧
        (gateAt C j).op = .and ∧ InCone 10 C i j ∧
        (j = C.output-10 ∨ InCone 10 C j (C.output-10))) : 20 ≤ C.size := by
    let stepWire (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have wires_eq_foldl (C : Circuit) (x : List Bool) :
        C.wires x = C.gates.foldl stepWire x := rfl

    have foldl_length (gs : List Gate) (w : List Bool) :
        (gs.foldl stepWire w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [stepWire]
        omega

    have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
        rw [ih (stepWire w g) hlt]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

    have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
        (gs.foldl stepWire w).getD (w.length + j) false =
          (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
      induction gs generalizing w j with
      | nil => simp at hj
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepWire w g).length := by simp [stepWire]
          rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (stepWire w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp [stepWire, List.getD_eq_getElem?_getD]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]; exact getD_ge w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simpa using hj
          have key := ih (stepWire w g) j hj'
          have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key

    let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

    have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
      exact List.getD_eq_getElem _ _ hj

    have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
      rw [gateAt_eq hj]; exact List.getElem_mem hj

    have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
        val C x u = x.getD u false := by
      unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

    have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
        (hu : n + C.gates.length ≤ u) : val C x u = false := by
      unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

    have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
        (hj : j < C.gates.length) :
        val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          if i < n + j then val C x i else false) := by
      subst hx
      rw [gateAt_eq hj]
      exact foldl_getD_gate C.gates x j hj

    have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
        (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
        val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
      rw [val_gate hx hr, hop]
      change (((gateAt C r).inputs.map fun i =>
        if i < n + r then val C x i else false).any id = true) ↔ _
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      constructor
      · rintro ⟨i, hi, h⟩
        by_cases hlt : i < n + r
        · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
        · rw [if_neg hlt] at h; cases h
      · rintro ⟨i, hi, hlt, h⟩
        exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

    have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
        (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
        val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
      rw [val_gate hx hr, hop]
      change (((gateAt C r).inputs.map fun i =>
        if i < n + r then val C x i else false).all id = true) ↔ _
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have h' := h i hi
        by_cases hlt : i < n + r
        · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
        · rw [if_neg hlt] at h'; cases h'
      · intro h i hi
        rw [if_pos (h i hi).1]; exact (h i hi).2

    have biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
        (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
          ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
        (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
        A.card ≤ 1 ∨ B.card ≤ 1 := by
      by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
      obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
      exact h4 a b c d hac hbd
        ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

    have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
        val C (List.ofFn x) u.val = x u := by
      rw [val_input (n := n) (by simp) u.isLt]
      simp [List.getD_eq_getElem?_getD]

    let OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
      ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
        w' ∈ (gateAt C k).inputs ∧ w' < n + k

    have orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
        val C x w = true := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact hv
      | head hstep _ ih =>
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

    have or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
        ∀ w : ℕ, val C x w = true →
          ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
            (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hv
        by_cases hw : w < n
        · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
        · by_cases hlen : n + C.gates.length ≤ w
          · rw [val_ge hx hlen] at hv; cases hv
          · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
            have hk : k < C.gates.length := by omega
            by_cases hop : (gateAt C k).op = GateOp.or
            · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
              obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
              exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
            · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

    have pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
      exact decide_eq_true (Or.inl rfl)

    have pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
      exact decide_eq_true (Or.inr rfl)

    have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
      change decide (w = u ∨ w = v) = true ↔ w = u ∨ w = v
      simp only [decide_eq_true_eq]

    have graphFun_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
        graphFun G ∅ x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]

    have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
        graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
      rw [graphFun_empty]
      simp only [decide_eq_true_eq, pairInput_true]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (G.irrefl hab).elim
        · exact hab
        · exact hab.symm
        · exact (G.irrefl hab).elim
      · intro h
        exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

    have operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
        (hv : val C (List.ofFn (pairInput u v)) p = true) :
        (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
        (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
          Relation.ReflTransGen (OrStep n C) p (n + h) ∧
          val C (List.ofFn (pairInput u v)) (n + h) = true) := by
      obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
        (by simp) p hv
      rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
      · left
        refine ⟨⟨w', hlt⟩, ?_, hr⟩
        have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
        rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
        exact (pairInput_true u v _).mp h1.symm
      · right
        exact ⟨h, hh, hop, hr, hv'⟩

    have reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
        (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
        val C (List.ofFn x) p = true :=
      orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

    have side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
        (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
        (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
        (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
        (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
        (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
        (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
      apply hF
      apply hbel
      rw [val_and (n := n) (by simp) ha hop, hin]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
      · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

    have edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
        (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
        (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
        (u v : Fin n) (huv : F (pairInput u v) = true) :
        ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
          Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
          val C (List.ofFn (pairInput u v)) (n + a) = true := by
      rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
        ⟨t, _, hr⟩ | h
      · exfalso
        have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
        rw [hout] at h1
        exact G.irrefl (hF t t h1)
      · exact h

    have below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
        (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
        (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
        (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
      rw [← hout]
      exact orStep_up (n := n) (by simp) hr hv


    have coneStep_append (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
        coneStep n cs g = cs ++ [(g.inputs.filter fun w => decide (n ≤ w ∧ w < n + cs.length)).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])] := rfl

    have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [coneStep_append]
        omega

    have cones_char (n : ℕ) (gs : List Gate) :
        ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
          rw [cones_len]; simp
        have key : ∀ k, k < gs.length →
            (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
              (gs.foldl (coneStep n) []).getD k [] := by
          intro k hk
          simp only [coneStep_append, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨h, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)] at h3
            exact h3
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD]
          have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
            simp only [coneStep_append, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen]
          rw [e2, e1]
          simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
          constructor
          · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
            refine ⟨by simp, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            rw [key (w - n) (by omega)] at h3
            exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
            simp only [coneStep_append, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp; omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; simp at h0
          · rintro ⟨h0, _⟩
            simp at h0
            omega

    have inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
        InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
          (i = k ∨ InCone n C i k) := by
      have h := cones_char n C.gates i j
      delta InCone cones gateAt
      rw [h]
      constructor
      · rintro ⟨h0, w, hw, h1, h2, h3⟩
        refine ⟨h0, w - n, by omega, ?_, h3⟩
        have : n + (w - n) = w := by omega
        rw [this]
        exact hw
      · rintro ⟨h0, k, hk, hw, h3⟩
        refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
        have : n + k - n = k := by omega
        rw [this]
        exact h3

    have orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_rfl
      | head hstep _ ih =>
        obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
        omega

    have orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w') :
        ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro k h' h1 h2; left; omega
      | @head a c hstep hrest ih =>
        intro k h' h1 h2
        obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
        have hk : k0 = k := by omega
        subst hk
        have hle := orStep_le hrest
        obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
        subst hk1
        right
        rw [inCone_iff]
        exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

    have operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
        (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
        (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
      have hle := orStep_le hr
      obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
      rw [inCone_iff]
      exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩


    have orStep_append (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
        orStep n cs g = cs ++ [cs.length :: (@ite (List ℕ) (g.op = GateOp.or)
          (gateOpDecEq g.op GateOp.or)
          ((g.inputs.filter fun w => decide (n ≤ w ∧ w < n + cs.length)).flatMap
            (fun w => cs.getD (w - n) [])) [])] := rfl

    have orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
        (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
      induction gs generalizing cs with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [orStep_append]
        omega

    have orSets_char (n : ℕ) (gs : List Gate) :
        ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
          j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
            ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
              i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (orStep n) []).length = gs.length := by
          rw [orSets_len]; simp
        have key : ∀ k, k < gs.length →
            (orStep n (gs.foldl (orStep n) []) g).getD k [] =
              (gs.foldl (orStep n) []).getD k [] := by
          intro k hk
          simp only [orStep_append, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, h3⟩
            refine ⟨by simp; omega, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
            · exact Or.inl h3
            · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3⟩
            refine ⟨h, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD]
          rw [e1]
          by_cases hop : g.op = GateOp.or
          · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
                gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                  (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
              simp only [orStep_append, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by omega)]
              simp [hlen, hop]
            rw [e2]
            simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
            constructor
            · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
              · exact ⟨by simp, Or.inl h3⟩
              · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
                rw [key (w - n) (by omega)]
                exact h3
            · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
              · exact Or.inl h3
              · rw [key (w - n) (by omega)] at h3
                exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
          · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
              simp only [orStep_append, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by omega)]
              simp [hlen, hop]
            rw [e2]
            simp only [List.mem_singleton]
            constructor
            · intro h3
              exact ⟨by simp, Or.inl h3⟩
            · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
              · exact h3
              · exact (hop hop2).elim
        · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
            simp only [orStep_append, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp; omega)]
            rfl
          rw [e0]
          constructor
          · intro h0; simp at h0
          · rintro ⟨h0, _⟩
            simp at h0
            omega

    have orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
        OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
          ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
      have h := orSets_char n C.gates g k
      delta OrReaches orSets gateAt
      have e : n + k - n = k := by omega
      rw [e, h]
      constructor
      · rintro ⟨_, hk, h3⟩
        refine ⟨hk, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
      · rintro ⟨hk, h3⟩
        refine ⟨by omega, hk, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
        · exact Or.inl h3
        · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

    have reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
        (h : Relation.ReflTransGen (OrStep n C) w w2) :
        ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro g h1 hg
        subst h1
        exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
      | @head a c hstep hrest ih =>
        intro g h1 hg
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

    have orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
        ∀ w, OrReaches n C w g →
          Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro h
        have hnw : n ≤ w := h.1
        obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
        rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
        · exact ⟨Relation.ReflTransGen.refl, hk⟩
        · obtain ⟨hr2, hg⟩ := ih i hlt hr
          exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

    have mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
        (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
        Relation.ReflTransGen (OrStep n C) p u.val := by
      delta PEqualNP.TopForm.orIn at hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with h | ⟨k, hk, hr, hop, hin⟩
      · rw [h]
      · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

    have reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
        (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
        u ∈ PEqualNP.TopForm.orIn n C p := by
      delta PEqualNP.TopForm.orIn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
      · exact Or.inl h
      · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
        exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

    have cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
        (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
        (f : ℕ → Finset α)
        (hf : ∀ k, (g k).op = GateOp.or →
          ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
        (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
        (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
        (stops : Finset ℕ)
        (hstops : ∀ w, w ∈ stops ↔
          (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
          (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
        f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
      have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hk u hu
          by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
          · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
            · rwa [Nat.add_sub_cancel_left]
            · rwa [Nat.add_sub_cancel_left]
          · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
            have hor : (g k).op = GateOp.or := by
              by_contra h
              exact hs (Or.inr h)
            obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
            by_cases hwn : w < n
            · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
            · have hwk := hback k w hw
              have hweq : n + (w - n) = w := by omega
              have hwR : w - n ∈ R :=
                (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
              exact ih (w - n) (by omega) hwR (by rwa [hweq])
      have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
        intro k hk
        have h := (hR k).1 hk
        clear hk
        induction h with
        | refl => exact Finset.Subset.refl _
        | tail _ hbc ih =>
          intro u hu
          exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
      exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

    have cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
        (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
        (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
      classical
      refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
      intro u v huv
      obtain ⟨a, ha, h | h⟩ := hcov u v huv
      · left
        rw [Finset.mem_coe, ← h]
        exact Finset.mem_image_of_mem _ ha
      · right
        rw [Finset.mem_coe, ← h]
        exact Finset.mem_image_of_mem _ ha

    let TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
      ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

    have cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
        (hf2 : ∀ k, (g k).op = GateOp.or →
          ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
        (Z : Finset ℕ)
        (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
        (r : ℕ) (R : Finset ℕ)
        (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
        (stops : Finset ℕ)
        (hstops : ∀ w, w ∈ stops ↔
          (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
          (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
        (I : Finset ℕ)
        (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
        (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
      classical
      set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
      set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
        with hN
      set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
      set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
      set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
      have hE2I : E2 ⊆ I := by
        intro k hk
        simp only [hE2, hE, Finset.mem_filter] at hk
        obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
        apply hI k hkR hkZ hor
        obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
        simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
        exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
      have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0) := by
        intro k hk
        simp only [hE, Finset.mem_filter] at hk
        have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
          ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
        have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
          intro h1
          obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
          simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
          obtain ⟨u, hu⟩ := hw.2
          exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
        rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
        · omega
        · rw [if_pos (hne h0)]
          split_ifs <;> omega
      have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
        calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
              (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
          _ = E2.card + Ene.card := by
            rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
      have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
        have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
        omega
      have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
        rintro w hw (h | ⟨k', hk', hin⟩)
        · rw [h]
          exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
          simp only [hN, Finset.mem_filter, List.mem_toFinset]
          exact ⟨hin, hw⟩
      have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
        intro k hk
        rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
        · left
          rw [h]
        · right
          refine ⟨b, ?_, hb3⟩
          rw [hE, Finset.mem_filter]
          exact ⟨(hR b).2 hb, hb1, hb2⟩
      set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
      have hS2card : S2.card = Ene.card :=
        Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
      have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
        rw [Finset.disjoint_left]
        intro w hw hw2
        rw [Finset.mem_filter] at hw
        rw [hS2, Finset.mem_image] at hw2
        obtain ⟨k, hk, rfl⟩ := hw2
        rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
        rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
        · omega
        · rw [Nat.add_sub_cancel_left] at h3
          rcases h3 with h3 | h3
          · exact hk.1.2.1 h3
          · exact h3 hk.1.2.2
      have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · rw [Finset.mem_filter] at hw
          rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
          · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
            rw [hE, Finset.mem_filter]
            exact ⟨hk, hk1, hk2⟩
          · have := hRU _ h2
            rw [Nat.add_sub_cancel' h1] at this
            exact hmem w hw.2 this
        · rw [hS2, Finset.mem_image] at hw
          obtain ⟨k, hk, rfl⟩ := hw
          rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
          exact hmem _ hk.2 (hRU k hk.1.1)
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
      have h4 := Finset.card_le_card hE2I
      omega

    have top_step2 (n : ℕ) (g : ℕ → Gate)
        (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
        (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
        (f : ℕ → Finset (Fin n))
        (hf1 : ∀ w, w < n → (f w).card ≤ 1)
        (hf2 : ∀ k, (g k).op = GateOp.or →
          ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
        (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
        (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
        (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
          (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
        ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
          (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
            Relation.ReflTransGen (fun k k' : ℕ =>
              (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
          (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
      classical
      by_cases hρ : ρ < n
      · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
        calc (((f ρ).image (fun v => s(c, v))) \ E0).card
            ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
          _ ≤ (f ρ).card := Finset.card_image_le
          _ ≤ 1 := hf1 ρ hρ
          _ ≤ (∅ : Finset ℕ).card + 1 := by simp
      · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
        obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
        have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
          intro k h
          induction h with
          | refl => exact le_refl _
          | tail _ hbc ih =>
            have := hback _ _ hbc.2.2
            omega
        set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
          Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
        have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
          intro k
          rw [hRdef, Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
        set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
          (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
          (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
        have hstops : ∀ w, w ∈ stops ↔
            (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
            (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
          intro w
          rw [hsdef, Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨?_, h⟩
            rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
            · omega
            · have := hle _ ((hR _).1 h2)
              omega
        set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
          with hZn
        obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
        have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
          cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
            intro k hk hkZ hor htwo
            rw [hZn, Finset.mem_filter]
            exact ⟨hk, hkZ, hor, htwo⟩)
        refine ⟨Znew, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro k hk hk2
          rw [hZn, Finset.mem_filter] at hk2
          exact hk2.2.1 hk
        · intro k hk
          rw [hZn, Finset.mem_filter] at hk
          refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
          rw [Nat.add_sub_cancel_left]
          have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
              (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
              Relation.ReflTransGen (fun k k' : ℕ =>
                (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
            intro k h
            induction h with
            | refl => exact Relation.ReflTransGen.refl
            | tail _ hbc ih => exact ih.tail hbc.2
          exact hreach k ((hR k).1 hk.1)
        · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
              (stops.filter (fun w => (f w).Nonempty)).biUnion
                (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
            intro e he
            rw [Finset.mem_sdiff, Finset.mem_image] at he
            obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
            obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
            refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
          have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
              (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
            intro w hw'
            have hw := (Finset.mem_filter.1 hw').1
            have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
                ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
              (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
            rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
            · exact himg _ (hf1 w hwn)
            · have hweq : n + (w - n) = w := by omega
              rcases hw2 with hz | hnor
              · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
                rcases hZ _ hz hsubw with hall | hc1
                · rw [hweq] at hall
                  have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                    rw [Finset.sdiff_eq_empty_iff_subset]
                    intro e he
                    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                    exact hall v hv
                  rw [hempty]
                  simp
                · rw [hweq] at hc1
                  exact himg _ hc1
              · have := hf3 _ hnor
                rw [hweq] at this
                exact himg _ this
          calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
              ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
                  (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
                Finset.card_le_card hsub
            _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
                Finset.card_biUnion_le_card_mul _ _ _ hone
            _ ≤ Znew.card + 1 := by omega

    have star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
        (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
          ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
        (g : ℕ → Gate)
        (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
        (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
        (f : ℕ → Finset (Fin n))
        (hf1 : ∀ w, w < n → (f w).card ≤ 1)
        (hf2 : ∀ k, (g k).op = GateOp.or →
          ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
        (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
        (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
        (l : List (Fin n × ℕ))
        (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
        ∃ Z : Finset ℕ,
          (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
            Relation.ReflTransGen (fun k k' : ℕ =>
              (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
          (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
            ≤ l.length + Z.card := by
      classical
      induction l with
      | nil => exact ⟨∅, by simp, by simp⟩
      | cons p l ih =>
        obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
        set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
        obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
          intro k hk hsub
          rcases Finset.mem_union.1 hk with hk | hk
          · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
            by_cases hc : q.1 = p.1
            · left
              intro v hv
              rw [hE0]
              refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
              rw [← hc]
              exact Finset.mem_image_of_mem _ (hfq hv)
            · right
              by_contra hcard
              have h2 : 1 < (f (n + k)).card := by omega
              obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
              have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
              have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
              have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
              have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
              exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
          · exact Or.inr (hB k hk))
        have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
        refine ⟨Z ∪ Znew, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_union.1 hk with hk | hk
          · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
            exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
          · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
            refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
            intro hkB
            exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
        · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
            List.length_cons, ← hE0]
          have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
              (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
            rw [Finset.sdiff_union_self_eq_union]
          have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
          rw [← hsplit] at hle
          omega

    have assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
        (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
          ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
        (g : ℕ → Gate)
        (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
        (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
        (f : ℕ → Finset (Fin n))
        (hf1 : ∀ w, w < n → (f w).card ≤ 1)
        (hf2 : ∀ k, (g k).op = GateOp.or →
          ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
        (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
        (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
        (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
        (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
          ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
        (Es : Finset (Sym2 (Fin n)))
        (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
        (∃ Z : Finset ℕ,
          (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
            n ≤ o a b ∧
            Relation.ReflTransGen (fun k k' : ℕ =>
              (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
            f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
          Es.card ≤ T.card + Z.card) ∧
        ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
          (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
      classical
      by_cases hEe : Es = ∅
      · subst hEe
        refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
        intro H K hH hK
        have h0 := hK.2 ∅ (by
          intro u v huv
          exact absurd (hH u v huv) (Finset.notMem_empty _))
        simp only [Finset.card_empty] at h0
        omega
      · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
        obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
        set c : ℕ → Fin n := fun a =>
          if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
          else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
        set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
        have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
            (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
          intro a ha u hu v hv
          by_cases h0 : (f (o a 0)).card ≤ 1
          · left
            have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
            refine ⟨?_, ?_⟩
            · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
              exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
            · simp only [hρ, h0, ↓reduceIte]
              exact hv
          · right
            have h1 : (f (o a 1)).card ≤ 1 := by
              rcases (hstar a ha).2 with h | h
              · exact absurd h h0
              · exact h
            have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
            refine ⟨?_, ?_⟩
            · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
              exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
            · simp only [hρ, h0, ↓reduceIte]
              exact hu
        set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
          with hT'
        have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
        have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
        have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
          intro a ha' v hv
          have ha := hT'T a ha'
          have hnn := (Finset.mem_filter.1 ha').2
          by_cases h0 : (f (o a 0)).card ≤ 1
          · simp only [hρ, h0, ↓reduceIte] at hv
            have hne := hnn.1
            simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
            exact (hstar a ha).1 _ hne.choose_spec v hv
          · simp only [hρ, h0, ↓reduceIte] at hv
            have hne := hnn.2
            simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
            exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
        have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
          intro e he
          obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
          have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
          rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨a, ha', v, h2, by rw [h1]⟩
          · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
        refine ⟨?_, ?_⟩
        · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
            (T'.toList.map (fun a => (c a, ρ a))) (by
              intro p hp v hv
              obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
              exact hadjc a (Finset.mem_toList.1 ha) v hv)
          refine ⟨Z, ?_, ?_⟩
          · intro k hk
            obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
            obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
            have ha' := Finset.mem_toList.1 ha
            have hnn := (Finset.mem_filter.1 ha').2
            refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
            by_cases h0 : (f (o a 0)).card ≤ 1
            · refine ⟨1, ?_⟩
              simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
              have e : (1 - 1 : Fin 2) = 0 := by decide
              rw [e]
              exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
            · refine ⟨0, ?_⟩
              simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
              have e : (1 - 0 : Fin 2) = 1 := by decide
              rw [e]
              have h1' : (f (o a 1)).card ≤ 1 := by
                rcases (hstar a (hT'T a ha')).2 with h | h
                · exact absurd h h0
                · exact h
              exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
          · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
                (fun p => (f p.2).image (fun v => s(p.1, v))) := by
              intro e he
              obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
              refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
              exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
            have h1 := Finset.card_le_card hsub
            rw [List.length_map, Finset.length_toList] at hZ2
            omega
        · intro H K hH hK
          refine (cover_bound n H T' c ?_ K hK).trans hT'card
          intro u v huv
          obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
          refine ⟨a, ha, ?_⟩
          have := Sym2.eq_iff.1 he
          rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact Or.inl h1.symm
          · exact Or.inr h2.symm

    have gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
        gateAt C k = ⟨GateOp.or, []⟩ := by
      change C.gates.getD k ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩
      exact List.getD_eq_default _ _ hk

    have orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
        u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (OrStep n C) p u.val :=
      ⟨mem_orIn_reach u, reach_mem_orIn u⟩

    have orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
        (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [orIn_iff_reach] at ha hb
      have h1 : ∀ c : Fin n, Relation.ReflTransGen (OrStep n C) w c.val → c.val = w := by
        intro c hc
        rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
        · exact h.symm
        · obtain ⟨k, _, h3, _⟩ := hd
          omega
      exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

    have orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
        u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
          (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
            u ∈ PEqualNP.TopForm.orIn n C w := by
      rw [orIn_iff_reach]
      constructor
      · intro h
        rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
        · have := u.isLt
          omega
        · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
          have hkk : k' = k := by omega
          subst hkk
          exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
      · rintro ⟨hk, hop, w, hw, hlt, hu⟩
        exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)


    have flat_count_reserve {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
        (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
        (hC : PEqualNP.TopForm.IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
        (hflat : ∀ a b : ℕ, (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
          (n + b = C.output ∨ InCone n C b (C.output - n)) → ¬ InCone n C a b)
        (K : Finset (Fin n)) (hK : IsMinCover G K) :
        G.edgeFinset.card + K.card ≤ C.size + 1 ∧
          ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
            (PEqualNP.TopForm.orIn n C (n+k)).Nonempty →
            (∀ c : Fin n, ∃ v ∈ PEqualNP.TopForm.orIn n C (n+k), ¬ G.Adj c v) →
            G.edgeFinset.card + K.card ≤ C.size := by
      classical
      obtain ⟨hAO, hback, htwo⟩ := hC
      let f := PEqualNP.TopForm.orIn n C
      let reach (k : ℕ) : Prop := Relation.ReflTransGen (OrStep n C) C.output (n + k)
      let T := (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.and ∧ reach k
      let O := (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.or ∧ reach k
      let o := PEqualNP.TopForm.opnd C
      have memT (k) : k ∈ T ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ reach k := by
        simp only [T,Finset.mem_filter,Finset.mem_range]
      have memO (k) : k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ reach k := by
        simp only [O,Finset.mem_filter,Finset.mem_range]
      have hF (u v : Fin n) : graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
        (graphFun_pair G u v).mp
      have out (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hfun x
      have noInput (u : Fin n) : ¬ Relation.ReflTransGen (OrStep n C) C.output u.val := by
        intro path
        have hv := reach_var_val (pairInput u u) _ u path (pairInput_left u u)
        rw [out] at hv
        exact G.irrefl (hF u u hv)
      have ltwo (k) (hk : k < C.gates.length) : ∃ p q, (gateAt C k).inputs = [p,q] :=
        List.length_eq_two.mp (htwo _ (gateAt_mem hk))
      have ao (k) (hk : k < C.gates.length) : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
        hAO _ (gateAt_mem hk)
      have op0 (a p q) (hi : (gateAt C a).inputs = [p,q]) : o a 0 = p := by
        change (gateAt C a).inputs.getD 0 0 = p
        rw [hi]
        rfl
      have op1 (a p q) (hi : (gateAt C a).inputs = [p,q]) : o a 1 = q := by
        change (gateAt C a).inputs.getD 1 0 = q
        rw [hi]
        rfl
      have hlen (k) (_ : (gateAt C k).op = GateOp.or) : (gateAt C k).inputs.length ≤ 2 := by
        by_cases hk : k < C.gates.length
        · rw [htwo _ (gateAt_mem hk)]
        · rw [gateAt_ge (Nat.le_of_not_gt hk)]
          decide
      have back (k i) (hi : i ∈ (gateAt C k).inputs) : i < n + k := by
        by_cases hk : k < C.gates.length
        · exact hback k hk i hi
        · rw [gateAt_ge (Nat.le_of_not_gt hk)] at hi
          simp at hi
      have hf2 (k) (hop : (gateAt C k).op = GateOp.or) (u) :
          u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w := by
        change u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ _
        rw [orIn_gate]
        constructor
        · rintro ⟨_,_,w,hw,_,hu⟩
          exact ⟨w,hw,hu⟩
        · rintro ⟨w,hw,hu⟩
          have hk : k < C.gates.length := by
            by_contra hn
            rw [gateAt_ge (Nat.le_of_not_gt hn)] at hw
            simp at hw
          exact ⟨hk,hop,w,hw,back k w hw,hu⟩
      have hf3 (k) (hn : (gateAt C k).op ≠ GateOp.or) : (f (n + k)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha
        exact (hn ((orIn_gate C k a).mp ha).2.1).elim
      have adjSide (a) (ha : a ∈ T) : ∀ u ∈ f (o a 0), ∀ v ∈ f (o a 1), G.Adj u v := by
        obtain ⟨hk,hand,hr⟩ := (memT a).mp ha
        obtain ⟨p,q,hin⟩ := ltwo a hk
        have hp : p ∈ (gateAt C a).inputs := by simp [hin]
        have hq : q ∈ (gateAt C a).inputs := by simp [hin]
        intro u hu v hv
        rw [op0 a p q hin] at hu
        rw [op1 a p q hin] at hv
        exact side_adj G (graphFun G ∅) hF a hk hand (below_of_reach _ out a hr) p q hin
          (back a p hp) (back a q hq) u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
      have hstar (a) (ha : a ∈ T) : (∀ u ∈ f (o a 0), ∀ v ∈ f (o a 1), G.Adj u v) ∧
          ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1) :=
        ⟨adjSide a ha, biclique_star G h4 _ _ (adjSide a ha)⟩
      have rawOnly (a) (ha : a ∈ T) (p) (hp : p ∈ (gateAt C a).inputs) (u v : Fin n)
          (hv : val C (List.ofFn (pairInput u v)) p = true) :
          ∃ t : Fin n, (t = u ∨ t = v) ∧ t ∈ f p := by
        rcases operand_trace u v p hv with h | ⟨j,hj,jnor,path,_⟩
        · obtain ⟨t,ht,hr⟩ := h
          exact ⟨t,ht,reach_mem_orIn t hr⟩
        · obtain ⟨ha',hand,haPath⟩ := (memT a).mp ha
          have nle : n ≤ C.output := (Nat.le_add_right n a).trans (orStep_le haPath)
          have hOutEq : C.output = n + (C.output - n) := by omega
          have habove : n + a = C.output ∨ InCone n C a (C.output - n) := by
            rcases orStep_cone haPath _ a hOutEq rfl with he | hc
            · left
              omega
            · exact Or.inr hc
          have jand := (ao j hj).resolve_right jnor
          exact (hflat j a jand hand habove (operand_cone ha' hp (back a p hp) path)).elim
      have covered : ∀ e ∈ G.edgeFinset, ∃ a ∈ T, ∃ u ∈ f (o a 0), ∃ v ∈ f (o a 1), e = s(u,v) := by
        intro e he
        induction e using Sym2.inductionOn with
        | hf u v =>
          have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
          obtain ⟨a,ha,hn,hr,hv⟩ := edge_trace G (graphFun G ∅) hF out u v ((graphFun_pair G u v).mpr huv)
          have hand := (ao a ha).resolve_right hn
          have ht := (memT a).mpr ⟨ha,hand,hr⟩
          obtain ⟨p,q,hin⟩ := ltwo a ha
          have hp : p ∈ (gateAt C a).inputs := by simp [hin]
          have hq : q ∈ (gateAt C a).inputs := by simp [hin]
          have valid := (val_and (n := n) (by simp) ha hand).mp hv
          obtain ⟨l,hl,hlf⟩ := rawOnly a ht p hp u v (valid p hp).2
          obtain ⟨r,hr',hrf⟩ := rawOnly a ht q hq u v (valid q hq).2
          rw [← op0 a p q hin] at hlf
          rw [← op1 a p q hin] at hrf
          have ne := G.ne_of_adj (adjSide a ht l hlf r hrf)
          refine ⟨a,ht,l,hlf,r,hrf,?_⟩
          rcases hl with hl|hl <;> rcases hr' with hh|hh
          · exact (ne (hl.trans hh.symm)).elim
          · rw [hl,hh]
          · rw [hl,hh]
            exact Sym2.eq_swap
          · exact (ne (hl.trans hh.symm)).elim
      obtain ⟨⟨Z,hZ,hEdge⟩,hCover⟩ := assemble2 n G h4 (gateAt C) hlen back f
        (fun w h => orIn_input C w h) hf2 hf3 ∅ (by simp) T o hstar G.edgeFinset covered
      have hTau := hCover G K (fun u v h => SimpleGraph.mem_edgeFinset.mpr h) hK
      have hTZ : Disjoint T Z := by
        apply Finset.disjoint_left.mpr
        intro k ht hz
        have hand := ((memT k).mp ht).2.1
        have hor := (hZ k hz).2.1
        rw [hand] at hor
        cases hor
      have hTO : Disjoint T O := by
        apply Finset.disjoint_left.mpr
        intro k ht ho
        have hand := ((memT k).mp ht).2.1
        have hor := ((memO k).mp ho).2.1
        rw [hand] at hor
        cases hor
      have hOZ : Disjoint O Z := by
        apply Finset.disjoint_left.mpr
        intro k ho hz
        obtain ⟨_,hor,⟨w,hw,_,_,_,⟨u,hu⟩,_⟩,_⟩ := hZ k hz
        have hk : u ∈ f (n + k) := (hf2 k hor u).mpr ⟨w,hw,hu⟩
        exact noInput u (((memO k).mp ho).2.2.trans (mem_orIn_reach u hk))
      have hZrange : Z ⊆ Finset.range C.gates.length := by
        intro k hk
        obtain ⟨w,hw,_⟩ := (hZ k hk).2.2.1
        apply Finset.mem_range.mpr
        by_contra hn
        rw [gateAt_ge (Nat.le_of_not_gt hn)] at hw
        simp at hw
      have sAll : T ∪ O ∪ Z ⊆ Finset.range C.gates.length := by
        intro k hk
        rcases Finset.mem_union.mp hk with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact Finset.mem_range.mpr ((memT k).mp h).1
          · exact Finset.mem_range.mpr ((memO k).mp h).1
        · exact hZrange h
      have cardAll : (T ∪ O ∪ Z).card = T.card + O.card + Z.card := by
        have hd : Disjoint (T ∪ O) Z := Finset.disjoint_union_left.mpr ⟨hTZ,hOZ⟩
        rw [Finset.card_union_of_disjoint hd,Finset.card_union_of_disjoint hTO]
      have total : T.card + O.card + Z.card ≤ C.size := by
        have hc := Finset.card_le_card sAll
        change T.card + O.card + Z.card ≤ C.gates.length
        simpa only [cardAll,Finset.card_range] using hc
      have merged : T.card ≤ O.card + 1 := by
        let p (k : ℕ) := n + k
        let U := insert C.output (O.biUnion fun k => (gateAt C k).inputs.toFinset)
        have sub : (T ∪ O).image p ⊆ U := by
          intro w hw
          obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
          have hpath : reach k := (Finset.mem_union.mp hk).elim
            (fun h => ((memT k).mp h).2.2) (fun h => ((memO k).mp h).2.2)
          rcases Relation.ReflTransGen.cases_tail hpath with he | ⟨w,hw',hs⟩
          · simpa only [U,p,he] using Finset.mem_insert_self C.output (O.biUnion fun k => (gateAt C k).inputs.toFinset)
          · obtain ⟨a,ha,rfl,hop,hi,_⟩ := hs
            exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
              ⟨a,(memO a).mpr ⟨ha,hop,hw'⟩,List.mem_toFinset.mpr hi⟩)
        have bnd : (O.biUnion fun k => (gateAt C k).inputs.toFinset).card ≤ O.card * 2 := by
          apply Finset.card_biUnion_le_card_mul
          intro k hk
          exact (List.toFinset_card_le _).trans (hlen k ((memO k).mp hk).2.1)
        have hc := Finset.card_le_card sub
        rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
          Finset.card_union_of_disjoint hTO] at hc
        have hb := Finset.card_insert_le C.output (O.biUnion fun k => (gateAt C k).inputs.toFinset)
        change U.card ≤ _ at hb
        omega
      refine ⟨by omega,?_⟩
      intro k hk hor hne hw
      have notT : k ∉ T := by
        intro kt
        have h := ((memT k).mp kt).2.1
        rw [hor] at h
        cases h
      have notO : k ∉ O := by
        intro ko
        obtain ⟨v,hv⟩ := hne
        exact noInput v (((memO k).mp ko).2.2.trans (mem_orIn_reach v hv))
      have notZ : k ∉ Z := by
        intro kz
        obtain ⟨_,_,_,a,ha,b,_,_,sub,hcard⟩ := hZ k kz
        obtain ⟨c,hc⟩ : (f (o a (1-b))).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨v,hv,hvc⟩ := hw c
        fin_cases b
        · change c ∈ f (o a (1 - (0 : Fin 2))) at hc
          have e : (1 - (0 : Fin 2)) = 1 := by decide
          rw [e] at hc
          exact hvc (adjSide a ha v (sub hv) c hc).symm
        · change c ∈ f (o a (1 - (1 : Fin 2))) at hc
          have e : (1 - (1 : Fin 2)) = 0 := by decide
          rw [e] at hc
          exact hvc (adjSide a ha c hc v (sub hv))
      have notUsed : k ∉ T ∪ O ∪ Z := by simp [notT,notO,notZ]
      have enlarged : insert k (T ∪ O ∪ Z) ⊆ Finset.range C.gates.length :=
        Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr hk,sAll⟩
      have enough := Finset.card_le_card enlarged
      rw [Finset.card_insert_of_notMem notUsed,cardAll,Finset.card_range] at enough
      change _ ≤ C.gates.length
      omega

    let petersen : SimpleGraph (Fin 10) := edgeGraph 10
      [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

    have petersen_target (x : Fin 10 → Bool) : graphFun petersen ∅ x =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] :
          List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2) := by
      let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      have rel : ∀ u v : Fin 10, petersen.Adj u v ↔ (u,v) ∈ E ∨ (v,u) ∈ E := by decide +kernel
      change graphFun petersen ∅ x = E.any _
      apply Bool.eq_iff_iff.mpr
      rw [graphFun_empty]
      simp only [decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, rel]
      constructor
      · rintro ⟨u,v,h,hu,hv⟩
        exact h.elim (fun h => ⟨(u,v),h,hu,hv⟩) (fun h => ⟨(v,u),h,hv,hu⟩)
      · rintro ⟨⟨u,v⟩,e,hu,hv⟩
        exact ⟨u,v,Or.inl e,hu,hv⟩

    have petersen_samples :
        (∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ),
          graphFun petersen ∅ (fun i => r.testBit i.val) = true) ∧
        (∀ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
          graphFun petersen ∅ (fun i => r.testBit i.val) = false) := by
      let E : List (Fin 10 × Fin 10) :=
        [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      let test (r : ℕ) := E.any fun e => r.testBit e.1.val && r.testBit e.2.val
      have positive : ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ).all test = true := by
        decide +kernel
      have negative : ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ).all
          (fun r => !test r) = true := by
        decide +kernel
      constructor
      · intro r hr
        exact (petersen_target _).trans (List.all_eq_true.mp positive r hr)
      · intro r hr
        have h : (!test r) = true := List.all_eq_true.mp negative r hr
        exact (petersen_target _).trans (Bool.eq_false_of_not_eq_true' h)

    have petersen_flat_common (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 10 C)
        (hfun : circuitFun 10 C = graphFun petersen ∅)
        (hflat : ∀ a b : ℕ, (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
          (10 + b = C.output ∨ InCone 10 C b (C.output - 10)) → ¬ InCone 10 C a b) :
        20 ≤ C.size ∧
          (C.gates.head? = some ⟨GateOp.or,[0,1]⟩ → 21 ≤ C.size) := by
      have common : ∀ a c : Fin 10, a ≠ c →
          (Finset.univ.filter fun b => petersen.Adj a b ∧ petersen.Adj c b).card ≤ 1 := by decide +kernel
      have h4 : ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
          ¬ (petersen.Adj a b ∧ petersen.Adj b c ∧ petersen.Adj c d ∧ petersen.Adj d a) := by
        rintro a b c d ac bd ⟨ab,bc,cd,da⟩
        have sub : ({b,d} : Finset (Fin 10)) ⊆
            Finset.univ.filter (fun x => petersen.Adj a x ∧ petersen.Adj c x) := by
          intro x hx
          rw [Finset.mem_filter]
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨Finset.mem_univ _,ab,bc.symm⟩
          · exact ⟨Finset.mem_univ _,da.symm,cd⟩
        have bound := Finset.card_le_card sub
        rw [Finset.card_pair bd] at bound
        have low := common a c ac
        omega
      have hEdge : petersen.edgeFinset.card = 15 := by decide +kernel
      let K : Finset (Fin 10) := {1,3,4,5,6,7}
      have cover : ∀ u v : Fin 10, petersen.Adj u v → u ∈ K ∨ v ∈ K := by decide +kernel
      have min : ∀ S : Finset (Fin 10), (∀ u v : Fin 10, petersen.Adj u v → u ∈ S ∨ v ∈ S) → 6 ≤ S.card := by
        intro S hc
        let f : Fin 5 → Fin 10 := ![0,1,2,3,4]
        let g : Fin 5 → Fin 10 := ![5,7,9,6,8]
        have injF : ∀ a b, f a = f b → a = b := by decide +kernel
        have injG : ∀ a b, g a = g b → a = b := by decide +kernel
        let F : Fin 5 ↪ Fin 10 := ⟨f,by intro a b h; exact injF a b h⟩
        let G : Fin 5 ↪ Fin 10 := ⟨g,by intro a b h; exact injG a b h⟩
        have apart : ∀ a b, f a ≠ g b := by decide +kernel
        have cycF : ∀ i : Fin 5, petersen.Adj (f i) (f (i+1)) := by decide +kernel
        have cycG : ∀ i : Fin 5, petersen.Adj (g i) (g (i+1)) := by decide +kernel
        have cyc : ∀ T : Finset (Fin 5), (∀ i : Fin 5, i ∈ T ∨ i+1 ∈ T) → 3 ≤ T.card := by
          decide +kernel
        let lifted (e : Fin 5 ↪ Fin 10) := (Finset.univ : Finset (Fin 5)).filter fun i => e i ∈ S
        have low (e : Fin 5 ↪ Fin 10) (adj : ∀ i : Fin 5, petersen.Adj (e i) (e (i+1))) :
            3 ≤ (lifted e).card := by
          apply cyc
          intro i
          rcases hc _ _ (adj i) with left | right
          · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,left⟩)
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,right⟩)
        have inCover (e : Fin 5 ↪ Fin 10) : (lifted e).map e ⊆ S := by
          rintro u hu
          obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hu
          exact (Finset.mem_filter.mp hi).2
        have disj : Disjoint ((lifted F).map F) ((lifted G).map G) := by
          apply Finset.disjoint_left.mpr
          intro u ha hb
          obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp ha
          obtain ⟨b,_,eq⟩ := Finset.mem_map.mp hb
          exact apart a b eq.symm
        have cap := Finset.card_le_card (Finset.union_subset (inCover F) (inCover G))
        rw [Finset.card_union_of_disjoint disj,Finset.card_map,Finset.card_map] at cap
        have lf := low F cycF
        have lg := low G cycG
        omega
      have Kcard : K.card = 6 := by decide +kernel
      have hK : IsMinCover petersen K := by
        refine ⟨?_,?_⟩
        · exact cover
        · intro S hS
          rw [Kcard]
          exact min S hS
      have h := flat_count_reserve petersen C h4 hC hfun hflat K hK
      rw [hEdge,Kcard] at h
      refine ⟨by have := h.1; omega,?_⟩
      intro hSeed
      have h0 : 0 < C.gates.length := by
        cases hg : C.gates with
        | nil => simp [hg] at hSeed
        | cons g gs => simp
      have gate0 : gateAt C 0 = ⟨GateOp.or,[0,1]⟩ := by
        cases hg : C.gates with
        | nil => simp [hg] at hSeed
        | cons g gs =>
          have eq : g = ⟨GateOp.or,[0,1]⟩ := by simpa [hg] using hSeed
          change C.gates.getD 0 ⟨GateOp.or, []⟩ = _
          simp [hg,eq]
      have hop : (gateAt C 0).op = GateOp.or := by rw [gate0]
      have rb (u : Fin 10) (hu : u = 0 ∨ u = 1) : u ∈ PEqualNP.TopForm.orIn 10 C (10+0) := by
        rw [orIn_gate]
        refine ⟨h0,hop,u.val,?_,by omega,?_⟩
        · rw [gate0]
          rcases hu with rfl | rfl <;> decide
        · exact reach_mem_orIn u Relation.ReflTransGen.refl
      have noCommon : ∀ c : Fin 10, ¬ petersen.Adj c 0 ∨ ¬ petersen.Adj c 1 := by decide +kernel
      exact h.2 0 h0 hop ⟨0,rb 0 (Or.inl rfl)⟩ (fun c =>
        (noCommon c).elim (fun h => ⟨0,rb 0 (Or.inl rfl),h⟩) (fun h => ⟨1,rb 1 (Or.inr rfl),h⟩))
    have hfun : circuitFun 10 C = graphFun petersen ∅ := by
      funext x
      rw [petersen_target]
      exact hVal x
    have hflat (i j : ℕ) (hi : (gateAt C i).op = .and) (hj : (gateAt C j).op = .and)
      (live : 10 + j = C.output ∨ InCone 10 C j (C.output - 10)) : ¬ InCone 10 C i j := by
      intro path
      apply noNest
      refine ⟨i,j,hi,hj,path,?_⟩
      rcases live with atOutput | ancestor
      · exact Or.inl (by omega)
      · exact Or.inr ancestor
    exact (petersen_flat_common C hAO hfun hflat).1
  change ∀ L : List Signal, L.length ≤ 18 → good basis L →
    (∀ w ∈ L, ∀ a b : Fin 10, a ≠ b →
      ¬(edges.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = true →
      w ≠ fun x => x a && x b) → target ∉ L
  intro L len steps ban hit
  obtain ⟨C,small,ao,start,out,outlt,ev,noPair⟩ := circuit L len steps ban hit
  let isNested := fun (i j : ℕ) => (gateAt C i).op = .and ∧
    (gateAt C j).op = .and ∧ InCone 10 C i j ∧
    (j = C.output-10 ∨ InCone 10 C j (C.output-10))
  by_cases nest : ∃ i j, isNested i j
  · have used := all_inputs_read C start out ev
    have hcount : C.output - 10 < C.gates.length := by
      change C.output < 10 + C.gates.length at outlt
      omega
    have gmem : gateAt C (C.output-10) ∈ C.gates := by
      change C.gates.getD (C.output-10) ⟨.or,[]⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hcount]
      exact List.getElem_mem hcount
    have witness : ∃ j : ℕ, 0 < j ∧ j < C.size ∧ ∃ a b : Fin 10, a ≠ b ∧
        (edges.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = false ∧
        (fun x => BlindGate.wireValue C 10 x (10+j)) = fun x => x a && x b := by
      rcases ao.1 _ gmem with h | h
      · exact nestedMeet C small ao start ev used nest h
      · exact nestedJoin C small ao start ev used nest h
    obtain ⟨j,jpos,jlt,a,b,ne,nonedge,eq⟩ := witness
    exact noPair j jpos jlt a b ne (fun h => Bool.noConfusion (nonedge.symm.trans h)) eq
  · have enough := flat C ao out outlt ev nest
    omega
