import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_7243_482
    (chain : let seeds : List ℕ := [16771220508673, 15270196031815690, 58150374342736, 94946423956570756, 54820275478340640, 3870282840359168, 133411506176, 182572334459125767, 218716039641301048, 189725234880840128, 156548607028235776, 229736628136996864, 270286071508729856, 288160007409369088]
      ∃ path : List ℕ, path.length ≤ 25 ∧ 2097151 ∈ seeds ++ path ∧
        ∀ j : Fin path.length, let before := seeds ++ path.take j.val
          (path.get j) ∉ before ∧ ∃ u ∈ before, ∃ v ∈ before, u ≠ v ∧
            ((path.get j) = (u &&& v) ∨ (path.get j) = (u ||| v)))
    (facets : let seeds : List ℕ := [16771220508673, 15270196031815690, 58150374342736, 94946423956570756, 54820275478340640, 3870282840359168, 133411506176, 182572334459125767, 218716039641301048, 189725234880840128, 156548607028235776, 229736628136996864, 270286071508729856, 288160007409369088]
      ∀ a : Fin 7 → Bool, ∃ k : Fin 37,
        (∀ p : Fin 7, a p = true → (seeds.getD p.val 0).testBit (21+k.val) = true) ∧
        ∀ l : Fin 7, (∀ p : Fin 7, a p = true → ¬ (p=l ∨ p=l+1 ∨ p=l+3)) →
          (seeds.getD (7+l.val) 0).testBit (21+k.val) = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) := by
  let seeds : List ℕ := [16771220508673, 15270196031815690, 58150374342736, 94946423956570756, 54820275478340640, 3870282840359168, 133411506176, 182572334459125767, 218716039641301048, 189725234880840128, 156548607028235776, 229736628136996864, 270286071508729856, 288160007409369088]
  have slen : seeds.length = 14 := rfl
  obtain ⟨path, cap, reached, options⟩ := chain
  change 2097151 ∈ seeds ++ path at reached
  let rel (down a b : Bool) := if down then (b = true → a = true) else (a = true → b = true)
  have algebra : ∀ (d o a a' b b' : Bool), rel d a a' → rel d b b' →
      rel d (if o then a || b else a && b) (if o then a' || b' else a' && b') := by
    intro d o a aa b bb
    cases d <;> cases o <;> cases a <;> cases aa <;> cases b <;> cases bb <;> simp [rel]
  have gateValue (o a b : Bool) :
      (if o then GateOp.or else GateOp.and).eval [a,b] = (if o then a || b else a && b) := by
    cases o <;> cases a <;> cases b <;> rfl
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let ok (i : ℕ) (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+i ∧ b < 14+i
  have readPair {α β : Type} (R : α → β → Prop) (da : α) (db : β) (defaults : R da db)
      {l : List α} {w : List β} (paired : List.Forall₂ R l w) :
      ∀ i : ℕ, R (l.getD i da) (w.getD i db) := by
    induction paired with
    | nil => intro i; simpa using defaults
    | cons h _ ih =>
      intro i
      cases i with
      | zero => exact h
      | succ i => exact ih i
  have construct (k : ℕ) (hk : k ≤ path.length) : ∃ gs : List Gate, gs.length = k ∧
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ok j g) ∧
      ∀ (x : Fin 14 → Bool) (t : ℕ) (down : Bool),
        (∀ i : Fin 14, rel down ((seeds.getD i.val 0).testBit t) (x i)) →
        List.Forall₂ (fun n b => rel down (n.testBit t) b)
          (seeds ++ path.take k) (gs.foldl step (List.ofFn x)) := by
    induction k with
    | zero =>
      refine ⟨[],rfl,by simp,?_⟩
      intro x t d h
      simp only [List.take_zero,List.append_nil,List.foldl_nil]
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [slen],?_⟩
      intro i hi hj
      have h14 : i < 14 := slen ▸ hi
      simpa only [List.get_eq_getElem,List.getD_eq_getElem _ _ hi,List.getElem_ofFn] using h ⟨i,h14⟩
    | succ k ih =>
      obtain ⟨gs,len,legal,valid⟩ := ih (by omega)
      have hk' : k < path.length := by omega
      let before := seeds ++ path.take k
      have blen : before.length = 14+k := by simp [before,slen,Nat.min_eq_left (Nat.le_of_lt hk')]
      obtain ⟨_,u,hu,v,hv,ne,which⟩ := options ⟨k,hk'⟩
      change u ∈ before at hu
      change v ∈ before at hv
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hu
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hv
      have hne : i ≠ j := by rintro rfl; exact ne (Option.some.inj (hi.symm.trans hj))
      have ib : i < 14+k := blen ▸ (List.getElem?_eq_some_iff.mp hi).1
      have jb : j < 14+k := blen ▸ (List.getElem?_eq_some_iff.mp hj).1
      have vi : before.getD i 0 = u := by simp [List.getD_eq_getElem?_getD,hi]
      have vj : before.getD j 0 = v := by simp [List.getD_eq_getElem?_getD,hj]
      let o : Bool := decide (path[k] = (u ||| v))
      have value : path[k] = (if o then u ||| v else u &&& v) := by
        by_cases h : path[k] = (u ||| v)
        · simp [o,h]
        · simpa [o,h] using which.resolve_right h
      let g : Gate := ⟨if o then .or else .and,[i,j]⟩
      have shape : ok k g := by
        refine ⟨?_,i,j,rfl,hne,ib,jb⟩
        cases e : o <;> simp [g,e]
      refine ⟨gs ++ [g],by simp [len],?_,?_⟩
      · intro m w hm
        by_cases b : m < gs.length
        · exact legal m w (by simpa [List.getElem?_append_left b] using hm)
        · rw [List.getElem?_append_right (by omega : gs.length ≤ m)] at hm
          by_cases z : m = gs.length
          · subst m
            have eq : g=w := by simpa using hm
            simpa [len,← eq] using shape
          · have zz : m-gs.length ≠ 0 := by omega
            simp [zz] at hm
      · intro x t d h
        let w := gs.foldl step (List.ofFn x)
        have old : List.Forall₂ (fun n b => rel d (n.testBit t) b) before w := valid x t d h
        have defaults : rel d ((0:ℕ).testBit t) false := by cases d <;> simp [rel]
        have r1 := readPair _ 0 false defaults old i
        have r2 := readPair _ 0 false defaults old j
        change rel d ((before.getD i 0).testBit t) (w.getD i false) at r1
        change rel d ((before.getD j 0).testBit t) (w.getD j false) at r2
        rw [vi] at r1
        rw [vj] at r2
        rw [List.take_succ_eq_append_getElem hk',← List.append_assoc,List.foldl_append]
        apply List.rel_append old
        apply List.Forall₂.cons _ List.Forall₂.nil
        change rel d ((path[k]).testBit t) (g.op.eval (g.inputs.map fun n => w.getD n false))
        have yes := algebra d o _ _ _ _ r1 r2
        change rel d ((path[k]).testBit t)
          ((if o then GateOp.or else GateOp.and).eval [w.getD i false,w.getD j false])
        rw [value,gateValue]
        cases e : o <;> simpa [e,Nat.testBit_land,Nat.testBit_lor] using yes
  obtain ⟨gs,len,legal,valid⟩ := construct path.length (le_refl _)
  obtain ⟨w,hw⟩ := List.mem_iff_getElem?.mp reached
  let C : Circuit := ⟨gs,w⟩
  have lookup (x : Fin 14 → Bool) (t : ℕ) (d : Bool)
      (start : ∀ i : Fin 14, rel d ((seeds.getD i.val 0).testBit t) (x i)) :
      rel d ((2097151 : ℕ).testBit t) (C.eval (List.ofFn x)) := by
    have pairs := valid x t d start
    rw [List.take_length] at pairs
    have defaults : rel d ((0:ℕ).testBit t) false := by cases d <;> simp [rel]
    have h := readPair _ 0 false defaults pairs w
    change rel d (((seeds ++ path).getD w 0).testBit t) (C.eval (List.ofFn x)) at h
    simpa only [List.getD_eq_getElem?_getD,hw,Option.getD_some] using h
  have rows : ∀ (p l : Fin 7), (p=l ∨ p=l+1 ∨ p=l+3) → ∃ t : Fin 21,
      ∀ i : Fin 14, (seeds.getD i.val 0).testBit t.val = true →
        i=Fin.castAdd 7 p ∨ i=Fin.natAdd 7 l := by decide +kernel
  have ones : ∀ t : Fin 21, (2097151:ℕ).testBit t.val = true := by decide +kernel
  have zeros : ∀ k : Fin 37, (2097151:ℕ).testBit (21+k.val) = false := by decide +kernel
  refine ⟨C,?_,legal,?_⟩
  · change gs.length ≤ 25
    rwa [len]
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro positive
      by_contra absent
      let a := fun p : Fin 7 => x (Fin.castAdd 7 p)
      obtain ⟨k,points,lines⟩ := facets a
      have lift : ∀ i : Fin 14, rel true ((seeds.getD i.val 0).testBit (21+k.val)) (x i) := by
        intro i
        refine Fin.addCases (m:=7) (n:=7)
          (motive:=fun i => rel true ((seeds.getD i.val 0).testBit (21+k.val)) (x i))
          (fun p => points p) (fun l => ?_) i
        intro xl
        exact lines l (fun p xp e => absent ⟨p,l,e,xp,xl⟩)
      have on := (lookup x (21+k.val) true lift) positive
      rw [zeros k] at on
      contradiction
    · rintro ⟨p,l,edge,xp,xl⟩
      obtain ⟨t,ht⟩ := rows p l edge
      apply (lookup x t.val false (fun i => ?_)) (ones t)
      intro hit
      rcases ht i hit with rfl | rfl
      · exact xp
      · exact xl
