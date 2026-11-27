import Mathlib.Data.List.GetD

-- Keep the twelve positive rows and the twelve inclusion-maximal negative rows.
-- Every omitted negative input is componentwise below a retained negative input.
-- Induct on the gate list for the transfer premise. Existing wires keep their bits,
-- and both Boolean operations preserve implication on the appended wire.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_5112_24
    (small : ∃ gs : List (Bool × ℕ × ℕ), 1 ≤ gs.length ∧ gs.length ≤ 14 ∧
      (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) ([251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064] : List ℕ)).getD (13 + gs.length - 1) 0 = 4095)
    (transfer : ∀ (gs : List (Bool × ℕ × ℕ)) (a b : List ℕ) (r s : ℕ),
      a.length = b.length →
      (∀ k : ℕ, (a.getD k 0).testBit r = true → (b.getD k 0).testBit s = true) →
      ∀ k : ℕ, ((gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) a).getD k 0).testBit r = true →
        ((gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) b).getD k 0).testBit s = true) :
    ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (14 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  let a : List ℕ := [256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664]
  let b : List ℕ := [251137, 817232, 3224100, 5542026, 11018243, 9060364, 12746800, 10682560, 13370112, 15731712, 15376435, 16403468, 15664064]
  let step := (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0])
  obtain ⟨gs, hpos, hlen, hs⟩ := small
  let out := 13 + gs.length - 1
  change ((gs.foldl step b).getD out 0) = 4095 at hs
  refine ⟨gs, hpos, hlen, ?_⟩
  change (gs.foldl step a).getD out 0 = 1764784
  have allWires (x y : List ℕ) (r s : ℕ) (hx : x.length = 13)
      (h : ∀ k : Fin 13, (x.getD k 0).testBit r = true → (y.getD k 0).testBit s = true) :
      ∀ k : ℕ, (x.getD k 0).testBit r = true → (y.getD k 0).testBit s = true := by
    intro k
    by_cases hk : k < 13
    · exact h ⟨k, hk⟩
    · rw [List.getD_eq_default x 0 (by omega : x.length ≤ k)]
      simp
  have rows : ∀ i : Fin 58, if (1764784 : ℕ).testBit i = true then
      ∃ j : Fin 12, ∀ k : Fin 13, (b.getD k 0).testBit j = true → (a.getD k 0).testBit i = true
    else ∃ j : Fin 12, ∀ k : Fin 13, (a.getD k 0).testBit i = true → (b.getD k 0).testBit (12 + j.val) = true := by
    decide
  have pos : ∀ j : Fin 12, (4095 : ℕ).testBit j = true := by decide
  have neg : ∀ j : Fin 12, (4095 : ℕ).testBit (12 + j.val) = false := by decide
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 58
  · have hr := rows ⟨i, hi⟩
    change (if (1764784 : ℕ).testBit i = true then _ else _) at hr
    split at hr
    next hp =>
      obtain ⟨j, hj⟩ := hr
      rw [hp]
      apply transfer gs b a j i rfl (allWires b a j i rfl hj) out
      change ((gs.foldl step b).getD out 0).testBit j = true
      rw [hs]
      exact pos j
    next hn =>
      obtain ⟨j, hj⟩ := hr
      have lift := transfer gs a b i (12 + j.val) rfl (allWires a b _ _ rfl hj) out
      change ((gs.foldl step a).getD out 0).testBit i = true →
        ((gs.foldl step b).getD out 0).testBit (12 + j.val) = true at lift
      rw [hs, neg] at lift
      cases h : ((gs.foldl step a).getD out 0).testBit i <;> simp_all
  · have hp : 2 ^ 58 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have ha : ∀ k : Fin 13, a.getD k 0 < 2 ^ 58 := by decide
    have hj : ∀ k : Fin 13, (a.getD k 0).testBit i = true → (b.getD k 0).testBit 12 = true := by
      intro k
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (ha k) hp)]
      simp
    have lift := transfer gs a b i 12 rfl (allWires a b _ _ rfl hj) out
    change ((gs.foldl step a).getD out 0).testBit i = true →
      ((gs.foldl step b).getD out 0).testBit 12 = true at lift
    rw [hs, show (4095 : ℕ).testBit 12 = false by decide] at lift
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1764784 < 2 ^ 58) hp)]
    cases h : ((gs.foldl step a).getD out 0).testBit i <;> simp_all
