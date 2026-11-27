import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Simultaneous cyclic shifts of the seven masks give the 37 maximal false inputs.
-- The low seven bits select points and the high seven bits select lines.
set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_11157_58
    (synth : ∃ C : Circuit, C.size ≤ 27 ∧
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
          g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      (∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
        C.eval (List.ofFn fun i : Fin 14 =>
          decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) ∧
      (∀ m ∈ ([127,244,480,720,1188,3008,16256] : List ℕ), ∀ r : Fin 7,
        C.eval (List.ofFn (Fin.addCases
          (fun p : Fin 7 => m.testBit (p+r).val)
          (fun l : Fin 7 => m.testBit (7+(l+r).val)))) = false) ∧
      ∀ s : Bool, ∃ w : List (Fin 3), w.length = 14+C.size ∧
        let d : ℕ → ℕ := fun i => (w.getD i 0).val
        d (if s then 0 else 7) = 0 ∧ d (if s then 7 else 0) ≤ 1 ∧
        2 ≤ d C.output ∧ ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
          (g.op = .and → d (14+j) ≤ d a + d b) ∧
          (g.op = .or → d (14+j) ≤ min (d a) (d b)))
    (cover : ∀ A : Fin 7 → Bool, ∃ m ∈ ([127,244,480,720,1188,3008,16256] : List ℕ), ∃ r : Fin 7,
      (∀ p : Fin 7, A p = true → m.testBit (p+r).val = true) ∧
      (∀ l : Fin 7, A l = false → A (l+1) = false → A (l+3) = false →
        m.testBit (7+(l+r).val) = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧
      (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 →
        (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
      (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔
        ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin
          (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧
      ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 =
        Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ x3 x1.output ∧
      ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 →
        x5.inputs = [x6, x7] →
        (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((14 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op =
          PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((14 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  classical
  obtain ⟨C,hs,hshape,hpos,hneg,weights⟩ := synth
  -- Gate monotonicity follows the induction in the checked reduction R_meta_1479_1.
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
      by_contra hnone
      let A (p : Fin 7) := x (Fin.castAdd 7 p)
      obtain ⟨m,hm,r,hp,hl⟩ := cover A
      let y : Fin 14 → Bool := fun i => Fin.addCases (motive := fun _ => Bool)
        (fun p : Fin 7 => m.testBit (p+r).val)
        (fun l : Fin 7 => m.testBit (7+(l+r).val)) i
      have hxy : ∀ i, x i = true → y i = true := by
        intro i
        refine Fin.addCases (m := 7) (n := 7) (motive := fun j => x j = true → y j = true) ?_ ?_ i
        · intro p hxp
          simpa only [y, Fin.addCases_left] using hp p hxp
        · intro l hxl
          have off (p : Fin 7) (inc : p = l ∨ p = l+1 ∨ p = l+3) : A p = false := by
            cases e : A p with
            | false => rfl
            | true => exact (hnone ⟨p,l,inc,e,hxl⟩).elim
          simpa only [y, Fin.addCases_right] using hl l (off l (Or.inl rfl))
            (off (l+1) (Or.inr (Or.inl rfl))) (off (l+3) (Or.inr (Or.inr rfl)))
      have hyt := evalMono x y hxy hx
      have hyf : C.eval (List.ofFn y) = false := hneg m hm r
      rw [hyf] at hyt
      cases hyt
    · rintro ⟨p,l,hi,hp,hl⟩
      apply evalMono _ x ?_ (hpos p l hi)
      intro i h
      rcases of_decide_eq_true h with e | e
      · subst i; exact hp
      · subst i; exact hl
  · intro s
    obtain ⟨w,_,hw⟩ := weights s
    exact ⟨fun i => (w.getD i 0).val,hw⟩
