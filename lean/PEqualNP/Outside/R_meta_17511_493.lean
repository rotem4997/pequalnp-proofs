import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_17511_493
    (numeric : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8)
    (extract : let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
    ∀ C : Circuit, FanInTwo C → C.size ≤ 17 →
    (∀ x, C.eval (List.ofFn x ++ [x 0 && x 2]) = F x) →
    ∃ (D : Circuit) (u : Nat) (b : Bool), FanInTwo D ∧ D.size ≤ 15 ∧ ∀ x : Fin 10 → Bool, x 9 = false →
      (if b then !(D.wires (List.ofFn x)).getD u false else (D.wires (List.ofFn x)).getD u false) = F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)), Bool.true]) ≠ [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))].any fun (x6 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x5 x6.1 && x5 x6.2 := by
  have previous : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
    intro C fan small
    by_contra! good
    obtain ⟨D,u,b,legal,budget,rep⟩ := extract C fan small good
    obtain ⟨x,zero,ne⟩ := numeric D u b legal budget
    exact ne (rep x zero)
  let target (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let evalRef (w : List Bool) : (Bool ⊕ Nat) → Bool := Sum.elim id (fun i => w.getD i false)
  let isFalseRef : (Bool ⊕ Nat) → Bool := Sum.elim (!·) (fun _ => false)
  let isTrueRef : (Bool ⊕ Nat) → Bool := Sum.elim id (fun _ => false)
  let liveRef : (Bool ⊕ Nat) → Option Nat := Sum.elim (fun _ => none) some
  let shrink (op : GateOp) (xs : List (Bool ⊕ Nat)) : Gate :=
    GateOp.rec (motive := fun _ => Gate)
      (if xs.any isFalseRef then ⟨.or,[]⟩ else ⟨.and,xs.filterMap liveRef⟩)
      (if xs.any isTrueRef then ⟨.and,[]⟩ else ⟨.or,xs.filterMap liveRef⟩)
      (Sum.elim (fun b => ⟨if b then .or else .and,[]⟩) (fun i => ⟨.not,[i]⟩) (xs.headD (.inl false)))
      (fun _ => ⟨.or,[]⟩) ⟨.or,[]⟩ op
  have evalAnd (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have evalOr (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
  have wireAll (w : List Bool) (xs : List (Bool ⊕ Nat)) :
      (xs.map (evalRef w)).all id =
         (!xs.any isFalseRef && ((xs.filterMap liveRef).map fun j => w.getD j false).all id) := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      rcases r with b|j
      · cases b
        · rfl
        · exact ih
      · change (w.getD j false && (xs.map (evalRef w)).all id) =
          (!xs.any isFalseRef && (w.getD j false && ((xs.filterMap liveRef).map fun i => w.getD i false).all id))
        rw [ih]
        exact Bool.and_left_comm _ _ _

  have wireAny (w : List Bool) (xs : List (Bool ⊕ Nat)) :
      (xs.map (evalRef w)).any id =
         (xs.any isTrueRef || ((xs.filterMap liveRef).map fun j => w.getD j false).any id) := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      rcases r with b|j
      · cases b
        · exact ih
        · rfl
      · change (w.getD j false || (xs.map (evalRef w)).any id) =
          (xs.any isTrueRef || (w.getD j false || ((xs.filterMap liveRef).map fun i => w.getD i false).any id))
        rw [ih]
        exact Bool.or_left_comm _ _ _

  have shrink_eval (w : List Bool) (o : GateOp) (xs : List (Bool ⊕ Nat))
      (ho : o = .and ∨ o = .or ∨ o = .not) :
      (shrink o xs).op.eval ((shrink o xs).inputs.map fun j => w.getD j false) =
         o.eval (xs.map (evalRef w)) := by
    rcases ho with rfl|rfl|rfl
    · rw [show GateOp.and.eval _ = (xs.map (evalRef w)).all id by rfl, wireAll]
      cases hh : xs.any isFalseRef <;> dsimp only [shrink] <;> rw [hh] <;> rfl
    · rw [show GateOp.or.eval _ = (xs.map (evalRef w)).any id by rfl, wireAny]
      cases hh : xs.any isTrueRef <;> dsimp only [shrink] <;> rw [hh] <;> rfl
    · cases xs with
      | nil => rfl
      | cons x xs =>
        cases x with
        | inl b => cases b <;> rfl
        | inr i => rfl

  have shrink_mono (o : GateOp) (xs : List (Bool ⊕ Nat)) (h : xs.length ≤ 2) :
      (shrink o xs).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
        (shrink o xs).inputs.length ≤ 2 := by
    have h' : (xs.filterMap liveRef).length ≤ 2 := (List.length_filterMap_le liveRef xs).trans h
    cases o with
    | and => dsimp only [shrink]; split <;> simp [h']
    | or => dsimp only [shrink]; split <;> simp [h']
    | not =>
      cases xs with
      | nil => simp [shrink]
      | cons r xs =>
        cases r with
        | inl b => cases b <;> simp [shrink]
        | inr i => simp [shrink]
    | mod i => simp [shrink]
    | maj => simp [shrink]



  let source {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (m i : ℕ) : (Bool ⊕ Nat) :=
    if h : i<n then r ⟨i,h⟩ else .inr (m+(i-n))

  let convert {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (m : ℕ) (g : Gate) : Gate :=
    shrink g.op (g.inputs.map (source r m))

  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w

  have value {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (old new : List Bool) (size : old.length=n)
      (good : ∀ i j, r i = .inr j → j < new.length)
      (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
      (bits : List Bool) (i : ℕ) :
      evalRef (new++bits) (source r new.length i) = (old++bits).getD i false := by
    dsimp only [source]
    split
    next hi =>
      rw [List.getD_append _ _ _ _ (by omega)]
      have z := agree ⟨i,hi⟩
      cases q : r ⟨i,hi⟩ with
      | inl b => simpa [q,evalRef] using z
      | inr j =>
        change (new++bits).getD j false = _
        rw [List.getD_append _ _ _ _ (good _ _ q)]
        simpa [q, evalRef] using z
    next hi =>
      change (new++bits).getD (new.length+(i-n)) false = _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : new.length ≤ new.length+(i-n)),
        List.getElem?_append_right (by omega : old.length ≤ i),size,Nat.add_sub_cancel_left]

  have replay {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (old new : List Bool) (size : old.length=n)
      (good : ∀ i j, r i = .inr j → j < new.length)
      (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
      (gs : List Gate) (ok : ∀ g ∈ gs, g.op=.and ∨ g.op=.or ∨ g.op=.not) (bits : List Bool) :
      ∃ z, run gs (old++bits) = old++z ∧ run (gs.map (convert r new.length)) (new++bits) = new++z := by
    induction gs generalizing bits with
    | nil => exact ⟨bits,rfl,rfl⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun i => (old++bits).getD i false)
      obtain ⟨z,h1,h2⟩ := ih (fun a h => ok a (List.mem_cons_of_mem _ h)) (bits++[bit])
      refine ⟨z,?_,?_⟩
      · simpa [run,step,bit,List.append_assoc] using h1
      · have next : step (new++bits) (convert r new.length g) = new++(bits++[bit]) := by
          simp only [step,convert,shrink_eval _ _ _ (ok g List.mem_cons_self),List.map_map,Function.comp_def,
            value r old new size good agree bits,bit,List.append_assoc]
        change run (gs.map _) (step _ _) = _
        rw [next]
        exact h2

  have output {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (old new : List Bool) (size : old.length=n)
      (good : ∀ i j, r i = .inr j → j < new.length)
      (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
      (C : Circuit) (fan : FanInTwo C) :
      evalRef (run (C.gates.map (convert r new.length)) new) (source r new.length C.output) =
        C.eval old := by
    obtain ⟨z,h1,h2⟩ := replay r old new size good agree C.gates
      (fun g h => by simpa using (fan _ h).1) []
    simp only [List.append_nil] at h1 h2
    change _ = (run C.gates old).getD C.output false
    rw [h1,h2,value r old new size good agree]

  have fan {n : ℕ} (r : Fin n → (Bool ⊕ Nat)) (m o : ℕ) (C : Circuit) (hf : FanInTwo C) :
      FanInTwo ⟨C.gates.map (convert r m),o⟩ := by
    intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    apply shrink_mono
    simpa using (hf _ hq).2



  let z (x : Fin 10 → Bool) := x 0 && x 2
  let src (f : Fin 10 → Fin 10) (i : Fin 12) : (Bool ⊕ Nat) :=
    if hi : i.val < 10 then .inr (f ⟨i.val,hi⟩).val else if i.val=10 then .inr 10 else .inl true
  let old (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) := List.ofFn (x ∘ f) ++ [z x,true]
  let new (x : Fin 10 → Bool) := List.ofFn x ++ [z x]
  let graph (x : Fin 10 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
      (4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any fun e => x e.1 && x e.2

  have same (x : Fin 10 → Bool) : graph x = target x := by
    simp [graph,target,Bool.or_assoc]

  have valid (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) (i : Fin 12) (j : ℕ) (h : src f i = .inr j) :
      j < (new x).length := by
    dsimp only [src] at h
    split at h
    next hi => cases h; have := (f ⟨i.val,hi⟩).isLt; simp [new]; omega
    next => split at h <;> cases h <;> simp [new]

  have agree (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) (i : Fin 12) :
      evalRef (new x) (src f i) = (old f x).getD i.val false := by
    dsimp only [src]
    split
    next hi =>
      change (List.ofFn x++[z x]).getD (f ⟨i.val,hi⟩).val false =
        (List.ofFn (x ∘ f)++[z x,true]).getD i.val false
      rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,hi,↓reduceDIte,Option.getD_some,
        Function.comp_apply]
    next hi =>
      have both : i=10 ∨ i=11 := by omega
      rcases both with rfl | rfl <;> simp [evalRef,old,new,List.getD_eq_getElem?_getD,
        List.getElem?_append_right]
  intro C f hf size
  change ∃ x : Fin 10 → Bool, C.eval (old f x) ≠ graph x
  by_contra! perfect
  let gs := C.gates.map (convert (src f) 11)
  have ev (x : Fin 10 → Bool) :
      evalRef (run gs (new x)) (source (src f) 11 C.output) = C.eval (old f x) := by
    have h := output (src f) (old f x) (new x) (by simp [old]) (valid f x) (agree f x) C hf
    simpa only [new,List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using h
  cases ht : source (src f) 11 C.output with
  | inl b =>
    have cst (x : Fin 10 → Bool) : b = graph x := by
      have h := ev x
      rw [ht] at h
      exact h.trans (perfect x)
    have off := cst (fun _ => false)
    have on := cst (fun j => decide (j.val ≤ 1))
    have h0 : b = false := off
    have h1 : b = true := on
    exact Bool.noConfusion (h0.symm.trans h1)
  | inr i =>
    let D : Circuit := ⟨gs,i⟩
    have fd : FanInTwo D := fan (src f) 11 i C hf
    have bd : D.size ≤ 17 := by change gs.length ≤ 17; simpa only [gs,List.length_map] using (show C.gates.length ≤ 17 from size)
    obtain ⟨x,bad⟩ := previous D fd bd
    apply bad
    have h := ev x
    rw [ht] at h
    exact (h.trans (perfect x)).trans (same x)

