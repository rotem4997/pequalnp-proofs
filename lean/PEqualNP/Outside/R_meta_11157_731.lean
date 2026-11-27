import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_11157_731
    (synth : ∃ C : Circuit, C.size ≤ 27 ∧
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧
        a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      (∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
        C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) ∧
      (∀ A : Fin 7 → Bool, C.eval (List.ofFn (Fin.addCases A
        (fun l : Fin 7 => !(A l || A (l+1) || A (l+3))))) = false) ∧
      (∀ v ∈ ([0,7] : List ℕ), 2 ≤ ((scalarMults C 14 [0,7] v).getD C.output none).getD 2))
    (trace : ∀ (n : ℕ) (C : Circuit) (S : List ℕ) (v : ℕ),
      let r (i : ℕ) := (scalarMults C n S v).getD i none
      (∀ i : Fin n, r i.val = if i.val = v then some 1 else if i.val ∈ S then some 0 else none) ∧
      ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] → a < n+j → b < n+j →
        (g.op = .and → r (n+j) = (r a).bind (fun x => (r b).map (fun y => x+y))) ∧
        (g.op = .or → r (n+j) = ((r a).map (fun x => min x ((r b).getD x))).orElse (fun _ => r b))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((14 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((14 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  classical
  obtain ⟨C,hs,hshape,hpos,hneg,hcost⟩ := synth
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] := by
    intro g hg
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨ho,a,b,hab,_,_,_⟩ := hshape j g (List.getElem?_eq_some_iff.mpr ⟨hj,he⟩)
    exact ⟨ho,a,b,hab⟩
  have stepMono (u v : List Bool) (g : Gate)
      (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b])
      (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
    intro i hi
    by_cases hlt : i < u.length
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases hz : i-u.length = 0
      · simp only [hz, List.getD_cons_zero] at hi ⊢
        obtain ⟨ho,a,b,hab⟩ := hg
        rcases ho with ho | ho
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].all id) = true at hi
          change ([v.getD a false, v.getD b false].all id) = true
          simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hi ⊢
          exact ⟨h a hi.1, h b hi.2⟩
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].any id) = true at hi
          change ([v.getD a false, v.getD b false].any id) = true
          simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hi ⊢
          exact hi.elim (fun ha => Or.inl (h a ha)) (fun hb => Or.inr (h b hb))
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
  have runMono : ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) →
      ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (run gs u).getD i false = true → (run gs v).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro hg u v hlen h i hi; exact h i hi
    | cons g gs ih =>
      intro hg u v hlen h i hi
      change (run gs (step u g)).getD i false = true at hi
      change (run gs (step v g)).getD i false = true
      exact ih (fun k hk => hg k (by simp [hk])) _ _
        (by simp [step, hlen]) (stepMono u v g (hg g (by simp)) hlen h) i hi
  have evalMono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply runMono C.gates hG _ _ (by simp) ?_ C.output
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    split at hi
    · rename_i hlt
      simp [hlt] at hi ⊢
      exact h _ hi
    · simp at hi
  refine ⟨C,hs,hshape,?_,?_⟩
  · intro x
    constructor
    · intro hx
      by_contra noEdge
      let A (p : Fin 7) := x (Fin.castAdd 7 p)
      let B (l : Fin 7) := !(A l || A (l+1) || A (l+3))
      let y (i : Fin 14) : Bool := Fin.addCases (m := 7) (n := 7) (motive := fun _ => Bool) A B i
      have xy : ∀ i, x i = true → y i = true := by
        intro i
        refine Fin.addCases (m := 7) (n := 7) (motive := fun j => x j = true → y j = true) ?_ ?_ i
        · intro p hp
          simpa only [y,Fin.addCases_left,A] using hp
        · intro l hl
          have off (p : Fin 7) (inc : p = l ∨ p = l+1 ∨ p = l+3) : A p = false := by
            cases h : A p with
            | false => rfl
            | true => exact (noEdge ⟨p,l,inc,h,hl⟩).elim
          change Fin.addCases (motive := fun _ => Bool) A B (Fin.natAdd 7 l) = true
          rw [Fin.addCases_right]
          simp only [B,off l (Or.inl rfl),off (l+1) (Or.inr (Or.inl rfl)),
            off (l+3) (Or.inr (Or.inr rfl))]
          rfl
      have hy := evalMono x y xy hx
      have off : C.eval (List.ofFn y) = false := hneg A
      exact Bool.false_ne_true (off.symm.trans hy)
    · rintro ⟨p,l,hi,hp,hl⟩
      apply evalMono _ x ?_ (hpos p l hi)
      intro i hi
      rcases of_decide_eq_true hi with e | e
      · subst i
        exact hp
      · subst i
        exact hl
  · intro s
    let v : ℕ := if s then 7 else 0
    let r (i : ℕ) := (scalarMults C 14 [0,7] v).getD i none
    let cap (z : Option ℕ) := min 2 (z.getD 2)
    obtain ⟨raw,gates⟩ := trace 14 C [0,7] v
    have raw0 := raw (0 : Fin 14)
    have raw7 := raw (7 : Fin 14)
    change r 0 = _ at raw0
    change r 7 = _ at raw7
    have good := hcost v (by cases s <;> simp [v])
    change 2 ≤ (r C.output).getD 2 at good
    refine ⟨fun i => cap (r i),?_,?_,by simpa [cap] using good,?_⟩
    · cases s <;> simp_all [v,cap]
    · cases s <;> simp_all [v,cap]
    · intro j g a b hg hab
      obtain ⟨_,u,w,uw,_,hu,hw⟩ := hshape j g hg
      rw [hab] at uw
      obtain ⟨rfl,rfl⟩ : a=u ∧ b=w := by simpa using uw
      obtain ⟨ha,ho⟩ := gates j g a b hg hab hu hw
      change (g.op = .and → cap (r (14+j)) ≤ cap (r a) + cap (r b)) ∧
        (g.op = .or → cap (r (14+j)) ≤ min (cap (r a)) (cap (r b)))
      constructor
      · intro hop
        rw [show r (14+j) = (r a).bind (fun x => (r b).map (fun y => x+y)) from ha hop]
        cases r a <;> cases r b <;> simp [cap] <;> omega
      · intro hop
        rw [show r (14+j) = ((r a).map (fun x => min x ((r b).getD x))).orElse (fun _ => r b) from ho hop]
        cases r a <;> cases r b <;> simp [cap] <;> omega
