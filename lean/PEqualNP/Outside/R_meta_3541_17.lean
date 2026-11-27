import Mathlib
import PEqualNP.Defs

-- The first eleven gates combine the three lines 7, 8, 13, which meet in three
-- distinct points. The four remaining lines have 12 minimal true and 15 maximal
-- false assignments on eleven raw inputs. Six point-side ORs from the opening
-- are also available to the smaller program, at their original register numbers.
set_option maxRecDepth 24000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3541_17
    (residual : let step := fun (w : List ℕ) (c : ℕ) => w ++ [if c < 4096 then (w.getD (c % 64) 0 &&& w.getD (c / 64 % 64) 0) else (w.getD (c % 64) 0 ||| w.getD (c / 64 % 64) 0)]
      ∃ (rot8 rot13 : Fin 3) (p : List (Fin 8192)), p.length ≤ 14 ∧
        ((p.map Fin.val).foldl step ([28520456, 47534081, 1044992, 62528, 3158160, 71714, 5263620, 134213632, 134213632, 86679559, 105693240, 126812608, 133172736, 134213632, 66547721, 66581577, 66580480, ([29356552, 32731404, 6288132] : List ℕ).getD rot8.val 0, 33551116, 33550336, ([48230913, 49639569, 4190864] : List ℕ).getD rot13.val 0, 50328209, 50327552, 67104768, 67104768] : List ℕ)).getD (24+p.length) 0 = 4095)
    (transport : let step := fun (w : List ℕ) (c : ℕ) => w ++ [if c < 4096 then (w.getD (c % 64) 0 &&& w.getD (c / 64 % 64) 0) else (w.getD (c % 64) 0 ||| w.getD (c / 64 % 64) 0)]
      ∀ (a b : List ℕ) (p : List (Fin 8192)) (u v : ℕ), a.length = b.length →
        (∀ j : ℕ, (a.getD j 0).testBit u = true → (b.getD j 0).testBit v = true) →
        ∀ j : ℕ, (((p.map Fin.val).foldl step a).getD j 0).testBit u = true →
          (((p.map Fin.val).foldl step b).getD j 0).testBit v = true) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → List ℕ := fun (x2 : List ℕ) (x3 : ℕ) => x2 ++ [if x3 < (4096 : ℕ) then x2.getD (x3 % (64 : ℕ)) (0 : ℕ) &&& x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x2.getD (x3 % (64 : ℕ)) (0 : ℕ) ||| x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; have x3 : ℕ → ℕ → Bool → ℕ := fun (x3 x4 : ℕ) (x5 : Bool) => x3 + (64 : ℕ) * x4 + if x5 = Bool.true then (4096 : ℕ) else (0 : ℕ); ∃ (x4 : Fin (65 : ℕ)) (x5 : Bool) (x6 : Bool) (x7 : List (Fin (8192 : ℕ))),   x7.length ≤ (24 : ℕ) ∧     have x8 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);     have x9 : List ℕ := x3 (0 : ℕ) (↑(Fin.ofNat (14 : ℕ) (x8 / (225 : ℕ)))) x5 :: x3 (↑(Fin.ofNat (15 : ℕ) (x8 % (225 : ℕ) / (15 : ℕ)))) (↑(Fin.ofNat (15 : ℕ) (x8 % (15 : ℕ)))) x6 :: List.map Fin.val x7;     (List.foldl x2 x1 x9).getD ((13 : ℕ) + x9.length) (0 : ℕ) = (2097151 : ℕ) := by
  let step := fun (w : List ℕ) (c : ℕ) => w ++ [if c < 4096 then (w.getD (c % 64) 0 &&& w.getD (c / 64 % 64) 0) else (w.getD (c % 64) 0 ||| w.getD (c / 64 % 64) 0)]
  let initial : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  obtain ⟨rot8,rot13,p,hp,solution⟩ := residual
  let middle : List (Fin 8192) := [967,
    (![4224,4480,4482] : Fin 3 → Fin 8192) rot8, (![5190,5186,5184] : Fin 3 → Fin 8192) rot8,
    1160, (![4225,4353,4354] : Fin 3 → Fin 8192) rot13, (![5380,5378,5377] : Fin 3 → Fin 8192) rot13,
    1357,5328,5590]
  let opening : List ℕ := 4160 :: 4995 :: middle.map Fin.val
  let small : List ℕ := [28520456, 47534081, 1044992, 62528, 3158160, 71714, 5263620, 134213632, 134213632, 86679559, 105693240, 126812608, 133172736, 134213632, 66547721, 66581577, 66580480, ([29356552, 32731404, 6288132] : List ℕ).getD rot8.val 0, 33551116, 33550336, ([48230913, 49639569, 4190864] : List ℕ).getD rot13.val 0, 50328209, 50327552, 67104768, 67104768]
  let full := opening.foldl step initial
  let last := 24+p.length
  let ws := (p.map Fin.val).foldl step full
  change ((p.map Fin.val).foldl step small).getD last 0 = 4095 at solution
  have lenF : full.length=25 := rfl
  have lenS : small.length=25 := rfl
  have openValue : full.getD 24 0 = 279403 := by fin_cases rot8 <;> fin_cases rot13 <;> decide +kernel
  have low : ∀ j : Fin 25, full.getD j 0 < 2^58 := by fin_cases rot8 <;> fin_cases rot13 <;> decide +kernel
  have pos : ∀ k : Fin 21, (279403 : ℕ).testBit k = false →
      ∃ v : Fin 12, ∀ j : Fin 25, (small.getD j 0).testBit v = true →
        (full.getD j 0).testBit k = true := by fin_cases rot8 <;> fin_cases rot13 <;> decide +kernel
  have neg : ∀ k : Fin 37, ∃ v : Fin 15, ∀ j : Fin 25,
      (full.getD j 0).testBit (21+k.val) = true →
      (small.getD j 0).testBit (12+v.val) = true := by fin_cases rot8 <;> fin_cases rot13 <;> decide +kernel
  have extend {a b : List ℕ} (ha : a.length=25) (u v : ℕ)
      (all : ∀ j : Fin 25, (a.getD j 0).testBit u=true → (b.getD j 0).testBit v=true) :
      ∀ j : ℕ, (a.getD j 0).testBit u=true → (b.getD j 0).testBit v=true := by
    intro j h
    by_cases hj : j<25
    · exact all ⟨j,hj⟩ h
    · rw [List.getD_eq_default _ _ (by omega)] at h
      simp at h
  have mask (t k : ℕ) : (2^t-1 : ℕ).testBit k = decide (k<t) := Nat.testBit_two_pow_sub_one ..
  have output : (279403 ||| ws.getD last 0) = (2097151 : ℕ) := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_or]
    change (_ || _) = (2^21-1 : ℕ).testBit k
    rw [mask]
    by_cases hk : k<21
    · simp only [hk,decide_true]
      cases h : (279403 : ℕ).testBit k with
      | true => rfl
      | false =>
        obtain ⟨v,hv⟩ := pos ⟨k,hk⟩ h
        have ok := transport small full p v k (lenS.trans lenF.symm) (extend lenS v k hv) last
        apply ok
        rw [show ((p.map Fin.val).foldl step small).getD last 0 = 4095 from solution]
        exact (mask 12 v.val).trans (decide_eq_true v.isLt)
    · have h0 : (279403 : ℕ).testBit k=false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (show 279403<2^21 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [hk,decide_false,h0,Bool.false_or]
      have d : ∃ v : Fin 15, ∀ j : Fin 25, (full.getD j 0).testBit k=true →
          (small.getD j 0).testBit (12+v.val)=true := by
        by_cases smallK : k<58
        · obtain ⟨v,hv⟩ := neg ⟨k-21,by omega⟩
          exact ⟨v,by simpa only [show 21+(k-21)=k by omega] using hv⟩
        · refine ⟨0,?_⟩
          intro j hj
          have hj0 := Nat.testBit_lt_two_pow ((low j).trans_le
            (Nat.pow_le_pow_right (by decide) (show 58≤k by omega)))
          exact False.elim (Bool.noConfusion (hj.symm.trans hj0))
      obtain ⟨v,hv⟩ := d
      cases h : (ws.getD last 0).testBit k with
      | false => rfl
      | true =>
        have ok := transport full small p k (12+v.val) (lenF.trans lenS.symm)
          (extend lenF k (12+v.val) hv) last h
        change (((p.map Fin.val).foldl step small).getD last 0).testBit (12+v.val)=true at ok
        rw [solution] at ok
        have z : (4095 : ℕ).testBit (12+v.val)=false :=
          (mask 12 (12+v.val)).trans (decide_eq_false (by omega))
        exact False.elim (Bool.noConfusion (ok.symm.trans z))
  have lengths (q : List ℕ) (a : List ℕ) : (q.foldl step a).length = a.length+q.length := by
    induction q generalizing a with
    | nil => simp
    | cons c q ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have earlier (q : List ℕ) (a : List ℕ) (j : ℕ) (hj : j<a.length) :
      (q.foldl step a).getD j 0 = a.getD j 0 := by
    induction q generalizing a with
    | nil => rfl
    | cons c q ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have keep : ws.getD 24 0 = 279403 := (earlier _ full 24 (by omega)).trans openValue
  have wl : ws.length=last+1 := by simp [ws,lengths,lenF,last]; omega
  let finalGate : Fin 8192 := ⟨4096+24+64*last,by dsimp [last]; omega⟩
  have ml : middle.length=9 := rfl
  refine ⟨20,true,true,middle++p++[finalGate],by simp [ml]; omega,?_⟩
  change ((4160 :: 4995 :: (middle++p++[finalGate]).map Fin.val).foldl step initial).getD
    (13+(4160 :: 4995 :: (middle++p++[finalGate]).map Fin.val).length) 0 = _
  have prep : 4160 :: 4995 :: (middle++p++[finalGate]).map Fin.val =
      opening++p.map Fin.val++[finalGate.val] := by simp [opening]
  rw [prep,List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have lenOpen : opening.length=11 := rfl
  have idx : 13+(opening++p.map Fin.val++[finalGate.val]).length = ws.length := by
    simp [lenOpen,wl,last]; omega
  rw [idx]
  change (ws++[if finalGate.val<4096 then _ else _]).getD ws.length 0 = _
  have atEnd (w : List ℕ) (z : ℕ) : (w++[z]).getD w.length 0=z := by simp
  rw [atEnd]
  have ge : ¬finalGate.val<4096 := by dsimp [finalGate]; omega
  have left : finalGate.val % 64 = 24 := by dsimp [finalGate]; omega
  have right : finalGate.val / 64 % 64 = last := by dsimp [finalGate,last]; omega
  change (if finalGate.val<4096 then ws.getD (finalGate.val % 64) 0 &&& ws.getD (finalGate.val / 64 % 64) 0
    else ws.getD (finalGate.val % 64) 0 ||| ws.getD (finalGate.val / 64 % 64) 0) = _
  simp only [ge,↓reduceIte,left,right]
  rw [keep]
  exact output
