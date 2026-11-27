import PEqualNP.Defs

-- Synthesis first ignores certification of contaminated intersections. The second
-- subproblem is a lower bound for the smaller class that can contaminate only
-- two designated AND positions. The construction extracts three different
-- positions and their individual rejecting rows from any separating trace.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_8610_427
    (trace : ∃ w : Nat → Nat,
      (∀ i : Fin 11, w i.val = ([(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] : List Nat).getD i.val 0) ∧
      (∃ o : Fin 32, w o.val = 65535) ∧
      ∀ j : Fin 21, ∃ a b : Fin (11 + j.val),
        w (11 + j.val) = w a.val ||| w b.val ∨ w (11 + j.val) = w a.val &&& w b.val)
    (sparse : ∀ (w : Nat → Nat) (u v : Fin 21),
      (∀ i : Fin 11, w i.val = ([(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] : List Nat).getD i.val 0) →
      (∀ j : Fin 21, ∃ a b : Fin (11 + j.val),
        w (11 + j.val) = w a.val ||| w b.val ∨
        (w (11 + j.val) = w a.val &&& w b.val ∧
          (j = u ∨ j = v ∨ ∀ q : Fin 24, (w (11 + j.val)).testBit (16 + q.val) = false))) →
      ∀ o : Fin 32, w o.val ≠ 65535) : (∃ (x1 : Fin (22 : ℕ)) (x2 : Fin ↑x1 → Bool) (x3 : Fin ↑x1 → Fin (33 : ℕ)) (x4 : Fin ↑x1 → Fin (33 : ℕ)) (x5 : Fin (33 : ℕ)) (x6 : ℕ → ℕ) (x7 : Fin (3 : ℕ) → Fin ↑x1) (x8 : Fin (3 : ℕ) → Fin (24 : ℕ)), ↑x5 < (11 : ℕ) + ↑x1 ∧ x6 ↑x5 = (65535 : ℕ) ∧ (∀ (x9 : Fin (11 : ℕ)), x6 ↑x9 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x9 (0 : ℕ)) ∧ (∀ (x9 : Fin ↑x1), ↑(x3 x9) < (11 : ℕ) + ↑x9 ∧ ↑(x4 x9) < (11 : ℕ) + ↑x9 ∧ x6 ((11 : ℕ) + ↑x9) = if x2 x9 = Bool.true then x6 ↑(x3 x9) &&& x6 ↑(x4 x9) else x6 ↑(x3 x9) ||| x6 ↑(x4 x9)) ∧ Function.Injective x7 ∧ ∀ (x9 : Fin (3 : ℕ)), x2 (x7 x9) = Bool.true ∧ (x6 ((11 : ℕ) + ↑(x7 x9))).testBit ((16 : ℕ) + ↑(x8 x9)) = Bool.true) := by
  classical
  obtain ⟨w,initial,⟨o,hit⟩,steps⟩ := trace
  choose a b gate using steps
  let isAnd (j : Fin 21) : Bool := decide (w (11+j.val) = w (a j).val &&& w (b j).val)
  let bad (j : Fin 21) : Prop := isAnd j = true ∧ ∃ q : Fin 24, (w (11+j.val)).testBit (16+q.val) = true
  have more (u v : Fin 21) : ∃ j : Fin 21, j ≠ u ∧ j ≠ v ∧ bad j := by
    by_contra! none
    apply sparse w u v initial _ o hit
    intro j
    refine ⟨a j, b j, ?_⟩
    rcases gate j with h | h
    · exact Or.inl h
    right
    refine ⟨h, ?_⟩
    by_cases hu : j = u
    · exact Or.inl hu
    by_cases hv : j = v
    · exact Or.inr (Or.inl hv)
    right; right
    intro q
    cases bit : (w (11+j.val)).testBit (16+q.val) with
    | false => rfl
    | true => exact False.elim (none j hu hv ⟨by simp [isAnd,h], q, bit⟩)
  obtain ⟨p,_,_,hp⟩ := more 0 0
  obtain ⟨q,hqp,_,hq⟩ := more p p
  obtain ⟨t,htp,htq,ht⟩ := more p q
  let marks (i : Fin 3) : Fin 21 := if i=0 then p else if i=1 then q else t
  have inject : Function.Injective marks := by
    intro i j eq
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact False.elim (hqp eq) | exact False.elim (hqp eq.symm) | exact False.elim (htp eq) | exact False.elim (htp eq.symm) | exact False.elim (htq eq) | exact False.elim (htq eq.symm)
  have dirty (i : Fin 3) : bad (marks i) := by fin_cases i <;> first | exact hp | exact hq | exact ht
  choose bits hbits using (fun i => (dirty i).2)
  let aa (j : Fin 21) : Fin 33 := ⟨(a j).val, by have h := (a j).isLt; have hj := j.isLt; omega⟩
  let bb (j : Fin 21) : Fin 33 := ⟨(b j).val, by have h := (b j).isLt; have hj := j.isLt; omega⟩
  refine ⟨⟨21, by decide⟩, isAnd, aa, bb, ⟨o.val, by have ho := o.isLt; omega⟩, w, marks, bits, o.isLt, hit, initial, ?_, inject, ?_⟩
  · intro j
    refine ⟨(a j).isLt, (b j).isLt, ?_⟩
    change w (11+j.val) = if isAnd j = true then w (a j).val &&& w (b j).val else w (a j).val ||| w (b j).val
    by_cases h : w (11+j.val) = w (a j).val &&& w (b j).val
    · simp [isAnd,h]
    · simpa [isAnd,h] using (gate j).resolve_right h
  · exact fun i => ⟨(dirty i).1,hbits i⟩
