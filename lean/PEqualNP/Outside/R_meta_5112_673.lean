import Mathlib.Data.List.GetD

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5112_673
    (synth : let small : List ℕ := [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
    ∃ gs : List (Bool × ℕ × ℕ),
      1 ≤ gs.length ∧ gs.length ≤ 14 ∧
      (gs.foldl (fun (ws : List ℕ) (g : Bool × ℕ × ℕ) =>
        ws ++ [if g.1 = true then ws.getD g.2.1 0 ||| ws.getD g.2.2 0
          else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]) small).getD (13 + gs.length - 1) 0 = 4095)
    (cover : let orig : List ℕ := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
    let small : List ℕ := [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
    ∀ i : Fin 58, ∃ j : Fin 24,
      (1764784 : ℕ).testBit i.val = (4095 : ℕ).testBit j.val ∧
      ∀ w : Fin 13,
        if (1764784 : ℕ).testBit i.val = true then
          (small.getD w.val 0).testBit j.val = true → (orig.getD w.val 0).testBit i.val = true
        else (orig.getD w.val 0).testBit i.val = true → (small.getD w.val 0).testBit j.val = true) :
    ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (14 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  let orig : List ℕ := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
  let small : List ℕ := [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
  let op : List ℕ → Bool × ℕ × ℕ → ℕ := fun w g =>
    if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0
  let step : List ℕ → Bool × ℕ × ℕ → List ℕ := fun w g => w ++ [op w g]
  let RowLE : List ℕ → List ℕ → ℕ → ℕ → Prop := fun xs ys i j =>
    ∀ w, (xs.getD w 0).testBit i = true → (ys.getD w 0).testBit j = true
  have op_mono (xs ys : List ℕ) (i j : ℕ) (h : RowLE xs ys i j) (g : Bool × ℕ × ℕ) :
      (op xs g).testBit i = true → (op ys g).testBit j = true := by
    rcases g with ⟨b, l, r⟩
    cases b
    · simpa [op, Bool.and_eq_true] using fun (p : (xs.getD l 0).testBit i = true ∧
        (xs.getD r 0).testBit i = true) => And.intro (h l p.1) (h r p.2)
    · simpa [op, Bool.or_eq_true] using fun (p : (xs.getD l 0).testBit i = true ∨
        (xs.getD r 0).testBit i = true) => p.imp (h l) (h r)
  have step_mono (xs ys : List ℕ) (i j : ℕ) (len : xs.length = ys.length)
      (h : RowLE xs ys i j) (g : Bool × ℕ × ℕ) : RowLE (step xs g) (step ys g) i j := by
    intro w
    change ((xs ++ [op xs g]).getD w 0).testBit i = true →
      ((ys ++ [op ys g]).getD w 0).testBit j = true
    by_cases hw : w < xs.length
    · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (len ▸ hw)]
      exact h w
    · have leX : xs.length ≤ w := Nat.le_of_not_gt hw
      have leY : ys.length ≤ w := len ▸ leX
      rw [List.getD_append_right _ _ _ _ leX, List.getD_append_right _ _ _ _ leY, ← len]
      cases w - xs.length with
      | zero => exact op_mono xs ys i j h g
      | succ d => simp
  have run_mono (gs : List (Bool × ℕ × ℕ)) (xs ys : List ℕ) (i j : ℕ)
      (len : xs.length = ys.length) (h : RowLE xs ys i j) :
      RowLE (gs.foldl step xs) (gs.foldl step ys) i j := by
    induction gs generalizing xs ys with
    | nil => exact h
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (by simp [step, len]) (step_mono xs ys i j len h g)
  have lift_rows (xs ys : List ℕ) (i j : ℕ) (len : xs.length = 13)
      (h : ∀ w : Fin 13, (xs.getD w.val 0).testBit i = true → (ys.getD w.val 0).testBit j = true) :
      RowLE xs ys i j := by
    intro w
    by_cases hw : w < 13
    · exact h ⟨w, hw⟩
    · have hs : xs.length ≤ w := by omega
      rw [List.getD_eq_default _ _ hs]
      simp
  obtain ⟨gs, hlo, hhi, hs⟩ := synth
  let out := 13 + gs.length - 1
  change (gs.foldl step small).getD out 0 = 4095 at hs
  refine ⟨gs, hlo, hhi, ?_⟩
  change (gs.foldl step orig).getD out 0 = 1764784
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases fits : bit < 58
  · obtain ⟨rep, same, comp⟩ := cover ⟨bit, fits⟩
    change (1764784 : ℕ).testBit bit = (4095 : ℕ).testBit rep.val at same
    change ∀ w : Fin 13,
      if (1764784 : ℕ).testBit bit = true then
        (small.getD w.val 0).testBit rep.val = true → (orig.getD w.val 0).testBit bit = true
      else (orig.getD w.val 0).testBit bit = true → (small.getD w.val 0).testBit rep.val = true at comp
    cases wanted : (1764784 : ℕ).testBit bit with
    | true =>
      simp only [wanted] at comp
      apply run_mono gs small orig rep.val bit rfl (lift_rows small orig rep.val bit rfl comp) out
      rw [hs, ← same, wanted]
    | false =>
      simp only [wanted, Bool.false_eq_true, ite_false] at comp
      apply Bool.eq_false_iff.mpr
      intro bad
      have e := run_mono gs orig small bit rep.val rfl (lift_rows orig small bit rep.val rfl comp) out bad
      rw [hs, ← same, wanted] at e
      cases e
  · have expLe : 2 ^ 58 ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt fits)
    have bound : ∀ v : Fin 13, orig.getD v.val 0 < 2 ^ 58 := by decide
    have ini : RowLE orig small bit 12 := by
      apply lift_rows orig small bit 12 rfl
      intro w bad
      have clean := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (bound w) expLe)
      rw [clean] at bad
      cases bad
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show 1764784 < 2 ^ 58 by decide) expLe)]
    apply Bool.eq_false_iff.mpr
    intro bad
    have e := run_mono gs orig small bit 12 rfl ini out bad
    rw [hs] at e
    exact (by decide : (4095 : ℕ).testBit 12 ≠ true) e
