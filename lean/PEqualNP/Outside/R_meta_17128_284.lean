import PEqualNP.Defs

-- Only the five surviving points, seven lines and three free line ORs are exposed to the tail.
-- The all-lines negative row bounds both packed trace directions on this bank.
theorem PEqualNP.Outside.R_meta_17128_284
    (ordinary :
      let safe (w : ℕ) := 22 ≤ w ∨ w ∈ ([1,3,4,5,6,7,8,9,10,11,12,13,14,18,20] : List ℕ)
      let meet (a b : ℕ) := (a &&& b &&& 1729382256910270463) |||
        ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& 2882303761517117440)
      let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 then a ||| b else meet a b]
      let value (tail : List (Bool × ℕ × ℕ)) (r : ℕ) :=
        (tail.foldl step [1729399028130512903, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 2776645719824533521, 218716039641317512, 189725234880971840, 156548607029289472, 229736628137037828, 270286071509057568, 288160007407796482, 2862231898204215317, 2882303761517117445, 3170463768924913927, 2305843009213693959, 3170473751662051727, 2305901159587512775, 3170475987293324751, 455]).getD r 0

      ∃ (tail : List (Bool × ℕ × ℕ)) (r : ℕ),
        tail.length ≤ 18 ∧
        (∀ i : Fin tail.length, let g := tail.get i
          g.2.1 ≠ g.2.2 ∧ g.2.1 < 22+i.val ∧ g.2.2 < 22+i.val) ∧
        r < 22+tail.length ∧ safe r ∧
        (∀ g ∈ tail, safe g.2.1 ∧ safe g.2.2) ∧
        (455 : ℕ) ||| (value tail r % (2^58)) = 2097151)
    (trace :
      let safe (w : ℕ) := 22 ≤ w ∨ w ∈ ([1,3,4,5,6,7,8,9,10,11,12,13,14,18,20] : List ℕ)
      let meet (a b : ℕ) := (a &&& b &&& 1729382256910270463) |||
        ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& 2882303761517117440)
      let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 then a ||| b else meet a b]
      let value (tail : List (Bool × ℕ × ℕ)) (r : ℕ) :=
        (tail.foldl step [1729399028130512903, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 2776645719824533521, 218716039641317512, 189725234880971840, 156548607029289472, 229736628137037828, 270286071509057568, 288160007407796482, 2862231898204215317, 2882303761517117445, 3170463768924913927, 2305843009213693959, 3170473751662051727, 2305901159587512775, 3170475987293324751, 455]).getD r 0

      ∀ (tail : List (Bool × ℕ × ℕ)) (r : ℕ),
        safe r → (∀ g ∈ tail, safe g.2.1 ∧ safe g.2.2) →
        (value tail r).testBit 57 = false → value tail r < 2^58) :
    have x1 : ℕ → ℕ → ℕ := fun (x1 x2 : ℕ) => x1 &&& x2 &&& (1729382256910270463 : ℕ) ||| (x1 <<< (1 : ℕ) &&& x2 ||| x1 &&& x2 <<< (1 : ℕ)) &&& (2882303761517117440 : ℕ); have x2 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) =>   have x4 : ℕ := x2.getD x3.2.1 (0 : ℕ);   have x5 : ℕ := x2.getD x3.2.2 (0 : ℕ);   x2 ++ [if x3.1 = Bool.true then x4 ||| x5 else x1 x4 x5]; ∃ (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ),   x3.length ≤ (18 : ℕ) ∧     (∀ (x5 : Fin x3.length),         have x6 : Bool × ℕ × ℕ := x3.get x5;         x6.2.1 ≠ x6.2.2 ∧ x6.2.1 < (22 : ℕ) + ↑x5 ∧ x6.2.2 < (22 : ℕ) + ↑x5) ∧       x4 < (22 : ℕ) + x3.length ∧ x4 ≠ (21 : ℕ) ∧ (455 : ℕ) ||| (List.foldl x2 [(1729399028130512903 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (2776645719824533521 : ℕ), (218716039641317512 : ℕ), (189725234880971840 : ℕ), (156548607029289472 : ℕ), (229736628137037828 : ℕ), (270286071509057568 : ℕ), (288160007407796482 : ℕ), (2862231898204215317 : ℕ), (2882303761517117445 : ℕ), (3170463768924913927 : ℕ), (2305843009213693959 : ℕ), (3170473751662051727 : ℕ), (2305901159587512775 : ℕ), (3170475987293324751 : ℕ), (455 : ℕ)] x3).getD x4 (0 : ℕ) = (2097151 : ℕ) := by
  dsimp only at ordinary trace ⊢
  obtain ⟨tail,r,cap,shape,valid,safeRoot,safePins,check⟩ := ordinary
  have r21 : r ≠ 21 := by
    rintro rfl
    exact (by decide +kernel : ¬ (22 ≤ 21 ∨ 21 ∈ ([1,3,4,5,6,7,8,9,10,11,12,13,14,18,20] : List ℕ))) safeRoot
  refine ⟨tail,r,cap,shape,valid,r21,?_⟩
  have neg := congrArg (fun w : ℕ => w.testBit 57) check
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow] at neg
  have off : (455 : ℕ).testBit 57 = false := by decide +kernel
  have offTarget : (2097151 : ℕ).testBit 57 = false := by decide +kernel
  have lowBit : decide (57 < 58) = true := by decide +kernel
  rw [off,offTarget,Bool.false_or,lowBit,Bool.true_and] at neg
  exact (by simpa only [Nat.mod_eq_of_lt (trace tail r safeRoot safePins neg)] using check)
