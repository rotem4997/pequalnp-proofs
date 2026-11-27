import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3541_317
    (encode :
    ∀ (m k : ℕ) (base : List ℕ) (v : ℕ → ℕ), base.length = m → m + k ≤ 64 →
      (∀ i < m, base.getD i 0 = v i) →
      (∀ i < k, ∃ (a b : ℕ) (flag : Bool), a < m + i ∧ b < m + i ∧
        v (m + i) = (if flag = true then v a ||| v b else v a &&& v b)) →
      ∃ codes : List (Fin 8192), codes.length = k ∧ ∀ i < m + k,
        (codes.foldl (fun s c => s ++ [if c.val < 4096 then
          s.getD (c.val % 64) 0 &&& s.getD (c.val / 64 % 64) 0 else
          s.getD (c.val % 64) 0 ||| s.getD (c.val / 64 % 64) 0]) base).getD i 0 = v i)
    (witness : ∃ (choice : Fin 65) (first second : Bool) (v : ℕ → ℕ),
      let t := (([[226, 227, 228, 232, 233, 234, 236, 239, 258, 259, 260, 262, 263], [264, 266, 267, 269, 277, 278, 281, 284, 338, 341, 344, 354, 355], [356, 359, 402, 404, 1576, 1577, 1582, 1583, 1584, 1589, 1592, 1593, 1598], [1599, 1601, 1604, 1609, 1611, 1614, 1617, 1619, 2026, 2027, 2032, 2034, 2036], [2039, 2042, 2043, 2045, 2047, 2048, 2051, 2053, 2054, 2058, 2066, 2067, 2069]] : List (List ℕ)).getD (choice.val / 13) []).getD (choice.val % 13) 0
      let a := (Fin.ofNat 14 (t / 225)).val
      let b := (Fin.ofNat 15 (t % 225 / 15)).val
      let c := (Fin.ofNat 15 (t % 15)).val
      (∀ i < 14, ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] : List ℕ).getD i 0 = v i) ∧
      v 14 = (if first = true then v 0 ||| v a else v 0 &&& v a) ∧
      v 15 = (if second = true then v b ||| v c else v b &&& v c) ∧
      (∀ i < 24, ∃ (u w : ℕ) (flag : Bool), u < 16 + i ∧ w < 16 + i ∧
        v (16 + i) = (if flag = true then v u ||| v w else v u &&& v w)) ∧
      v 39 = 2097151) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → List ℕ := fun (x2 : List ℕ) (x3 : ℕ) => x2 ++ [if x3 < (4096 : ℕ) then x2.getD (x3 % (64 : ℕ)) (0 : ℕ) &&& x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x2.getD (x3 % (64 : ℕ)) (0 : ℕ) ||| x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; have x3 : ℕ → ℕ → Bool → ℕ := fun (x3 x4 : ℕ) (x5 : Bool) => x3 + (64 : ℕ) * x4 + if x5 = Bool.true then (4096 : ℕ) else (0 : ℕ); ∃ (x4 : Fin (65 : ℕ)) (x5 : Bool) (x6 : Bool) (x7 : List (Fin (8192 : ℕ))),   x7.length ≤ (24 : ℕ) ∧     have x8 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);     have x9 : List ℕ := x3 (0 : ℕ) (↑(Fin.ofNat (14 : ℕ) (x8 / (225 : ℕ)))) x5 :: x3 (↑(Fin.ofNat (15 : ℕ) (x8 % (225 : ℕ) / (15 : ℕ)))) (↑(Fin.ofNat (15 : ℕ) (x8 % (15 : ℕ)))) x6 :: List.map Fin.val x7;     (List.foldl x2 x1 x9).getD ((13 : ℕ) + x9.length) (0 : ℕ) = (2097151 : ℕ) := by
  dsimp only
  obtain ⟨choice, first, second, v, hBase, hFirst, hSecond, hGates, hOut⟩ := witness
  let cols : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let t := (([[226, 227, 228, 232, 233, 234, 236, 239, 258, 259, 260, 262, 263], [264, 266, 267, 269, 277, 278, 281, 284, 338, 341, 344, 354, 355], [356, 359, 402, 404, 1576, 1577, 1582, 1583, 1584, 1589, 1592, 1593, 1598], [1599, 1601, 1604, 1609, 1611, 1614, 1617, 1619, 2026, 2027, 2032, 2034, 2036], [2039, 2042, 2043, 2045, 2047, 2048, 2051, 2053, 2054, 2058, 2066, 2067, 2069]] : List (List ℕ)).getD (choice.val / 13) []).getD (choice.val % 13) 0
  let a := (Fin.ofNat 14 (t / 225)).val
  let b := (Fin.ofNat 15 (t % 225 / 15)).val
  let c := (Fin.ofNat 15 (t % 15)).val
  let code (a b : ℕ) (flag : Bool) := a + 64 * b + if flag = true then 4096 else 0
  let step (s : List ℕ) (z : ℕ) := s ++ [if z < 4096 then
    s.getD (z % 64) 0 &&& s.getD (z / 64 % 64) 0 else
    s.getD (z % 64) 0 ||| s.getD (z / 64 % 64) 0]
  have code_step (s : List ℕ) (u w : ℕ) (flag : Bool) (hu : u < 64) (hw : w < 64) :
      step s (code u w flag) = s ++
        [if flag = true then s.getD u 0 ||| s.getD w 0 else s.getD u 0 &&& s.getD w 0] := by
    have h1 : code u w flag % 64 = u := by dsimp [code]; cases flag <;> simp <;> omega
    have h2 : code u w flag / 64 % 64 = w := by dsimp [code]; cases flag <;> simp <;> omega
    have h3 : code u w flag < 4096 ↔ flag = false := by
      dsimp [code]
      cases flag <;> simp <;> omega
    simp only [step, h1, h2, h3]
    cases flag <;> rfl
  have extend (s : List ℕ) (p : ℕ) (hs : s.length = p)
      (he : ∀ i < p, s.getD i 0 = v i) : ∀ i < p + 1, (s ++ [v p]).getD i 0 = v i := by
    intro i hi
    by_cases h : i < p
    · rw [List.getD_append _ _ _ _ (by rwa [hs])]
      exact he i h
    · have hi' : i = p := by omega
      subst i
      rw [← hs]
      simp
  have ha : a < 14 := (Fin.ofNat 14 (t / 225)).isLt
  have hb : b < 15 := (Fin.ofNat 15 (t % 225 / 15)).isLt
  have hc : c < 15 := (Fin.ofNat 15 (t % 15)).isLt
  have hCols : cols.length = 14 := rfl
  let w1 := step cols (code 0 a first)
  let w2 := step w1 (code b c second)
  have hw1 : w1 = cols ++ [v 14] := by
    dsimp only [w1]
    rw [code_step cols 0 a first (by decide) (by omega)]
    rw [hBase 0 (by decide), hBase a ha, ← hFirst]
  have len1 : w1.length = 15 := by simp [hw1, hCols]
  have read1 (i : ℕ) (hi : i < 15) : w1.getD i 0 = v i := by
    rw [hw1]
    exact extend cols 14 hCols hBase i hi
  have hw2 : w2 = w1 ++ [v 15] := by
    dsimp only [w2]
    rw [code_step w1 b c second (by omega) (by omega), read1 b hb, read1 c hc, ← hSecond]
  have len2 : w2.length = 16 := by simp [hw2, len1]
  have read2 (i : ℕ) (hi : i < 16) : w2.getD i 0 = v i := by
    rw [hw2]
    exact extend w1 15 len1 read1 i hi
  obtain ⟨codes, hCodes, hVal⟩ := encode 16 24 w2 v len2 (by decide) read2 hGates
  refine ⟨choice, first, second, codes, hCodes.le, ?_⟩
  have hLast := hVal 39 (by decide)
  rw [hOut] at hLast
  change ((code 0 a first :: code b c second :: codes.map Fin.val).foldl step cols).getD
    (13 + (code 0 a first :: code b c second :: codes.map Fin.val).length) 0 = 2097151
  simpa only [List.foldl_cons, List.foldl_map, List.length_cons, List.length_map, hCodes,
    Nat.reduceAdd, Function.comp_def, w1, w2, step] using hLast
