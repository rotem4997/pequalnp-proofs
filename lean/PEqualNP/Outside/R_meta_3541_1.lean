import Mathlib
import PEqualNP.Defs

-- The four lines with wire numbers 7, 10, 12 and 13 avoid point 6.
-- Their stars cover twelve of the twenty-one positive rows and reject all negative rows.
-- The other three lines meet at point 6. Each receives two further private point inputs.
-- The builder leaves all its intermediate wires available to the completion.
-- The parameters select independently which two points to combine first on three lines.
-- For a selected triple in ascending order, rotate by the parameter before combining it.
-- The first two gates combine points 0, 1 and 3, as in entry 20 of the posted table.
-- With zero rotations the thirteen subsequent codes are 967, 4352, 5189, 1162,
-- 4290, 5381, 1356, 4225, 5572, 1549, 5328, 5718 and 5850.
-- On line 10 the two OR codes are (4352, 5189), (4420, 5184) or (4416, 5188).
-- On line 12 the two OR codes are (4290, 5381), (4419, 5378) or (4418, 5379).
-- On line 13 the two OR codes are (4225, 5572), (4354, 5569) or (4353, 5570).
-- The last three OR gates join lines 7 and 10, lines 12 and 13, and then both pairs.
-- A second route saves the gate on the four-line side. Its thirteen scratch values
-- may be arbitrary because the twelve closing gates read only the inputs and the aggregate.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_3541_1
    (build : let initial : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let advance : List ℕ → ℕ → List ℕ := fun (w : List ℕ) (k : ℕ) =>
        w ++ [if k < 4096 then w.getD (k % 64) 0 &&& w.getD (k / 64 % 64) 0
              else w.getD (k % 64) 0 ||| w.getD (k / 64 % 64) 0]
      ∀ a b c : Fin 3, ∃ p : List (Fin 8192), p.length = 13 ∧
        (([4160, 4995] : List ℕ) ++ p.map Fin.val).foldl advance initial =
          initial ++ [95274182876594239,
        98933359855537727,
        521,
        ([95235063194611719, 14011931637837824, 104658453169143815] : List ℕ).getD a.val 0,
        104664500684451847,
        69636,
        ([4292751074004928, 17944063519198720, 14003653759435200] : List ℕ).getD b.val 0,
        17944304641347520,
        133248,
        ([63221765505528, 8777837343168, 70185669128248] : List ℕ).getD c.val 0,
        70368742109688,
        16672,
        70157,
        149920,
        220077])
    (finish : let initial : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let advance : List ℕ → ℕ → List ℕ := fun (w : List ℕ) (k : ℕ) =>
        w ++ [if k < 4096 then w.getD (k % 64) 0 &&& w.getD (k / 64 % 64) 0
              else w.getD (k % 64) 0 ||| w.getD (k / 64 % 64) 0]
      (∃ (a b c : Fin 3) (s : List (Fin 8192)), s.length ≤ 11 ∧
        ((s.map Fin.val).foldl advance (initial ++ [95274182876594239,
        98933359855537727,
        521,
        ([95235063194611719, 14011931637837824, 104658453169143815] : List ℕ).getD a.val 0,
        104664500684451847,
        69636,
        ([4292751074004928, 17944063519198720, 14003653759435200] : List ℕ).getD b.val 0,
        17944304641347520,
        133248,
        ([63221765505528, 8777837343168, 70185669128248] : List ℕ).getD c.val 0,
        70368742109688,
        16672,
        70157,
        149920,
        220077])).getD (28 + s.length) 0 = 2097151) ∨
      (∃ (p : List (Fin 8192)) (z : Fin 13 → ℕ), p.length = 12 ∧
        (([4160,4995] : List ℕ) ++ p.map Fin.val).foldl advance initial = initial ++ List.ofFn z ++ [220077])) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → List ℕ := fun (x2 : List ℕ) (x3 : ℕ) => x2 ++ [if x3 < (4096 : ℕ) then x2.getD (x3 % (64 : ℕ)) (0 : ℕ) &&& x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x2.getD (x3 % (64 : ℕ)) (0 : ℕ) ||| x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; have x3 : ℕ → ℕ → Bool → ℕ := fun (x3 x4 : ℕ) (x5 : Bool) => x3 + (64 : ℕ) * x4 + if x5 = Bool.true then (4096 : ℕ) else (0 : ℕ); ∃ (x4 : Fin (65 : ℕ)) (x5 : Bool) (x6 : Bool) (x7 : List (Fin (8192 : ℕ))),   x7.length ≤ (24 : ℕ) ∧     have x8 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);     have x9 : List ℕ := x3 (0 : ℕ) (↑(Fin.ofNat (14 : ℕ) (x8 / (225 : ℕ)))) x5 :: x3 (↑(Fin.ofNat (15 : ℕ) (x8 % (225 : ℕ) / (15 : ℕ)))) (↑(Fin.ofNat (15 : ℕ) (x8 % (15 : ℕ)))) x6 :: List.map Fin.val x7;     (List.foldl x2 x1 x9).getD ((13 : ℕ) + x9.length) (0 : ℕ) = (2097151 : ℕ) := by
  let initial : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let advance : List ℕ → ℕ → List ℕ := fun (w : List ℕ) (k : ℕ) =>
        w ++ [if k < 4096 then w.getD (k % 64) 0 &&& w.getD (k / 64 % 64) 0
              else w.getD (k % 64) 0 ||| w.getD (k / 64 % 64) 0]
  let bank (a b c : Fin 3) : List ℕ := initial ++ [95274182876594239,
        98933359855537727,
        521,
        ([95235063194611719, 14011931637837824, 104658453169143815] : List ℕ).getD a.val 0,
        104664500684451847,
        69636,
        ([4292751074004928, 17944063519198720, 14003653759435200] : List ℕ).getD b.val 0,
        17944304641347520,
        133248,
        ([63221765505528, 8777837343168, 70185669128248] : List ℕ).getD c.val 0,
        70368742109688,
        16672,
        70157,
        149920,
        220077]
  rcases finish with ⟨a,b,c,s,hs,hout⟩ | ⟨p,z,hp,hstate⟩
  · obtain ⟨p,hp,hstate⟩ := build a b c
    change (([4160,4995] : List ℕ) ++ p.map Fin.val).foldl advance initial = bank a b c at hstate
    change ((s.map Fin.val).foldl advance (bank a b c)).getD (28+s.length) 0 = 2097151 at hout
    refine ⟨20,true,true,p++s,?_,?_⟩
    · rw [List.length_append,hp]; omega
    · change ((([4160,4995] : List ℕ) ++ (p++s).map Fin.val).foldl advance initial).getD
        (13+(([4160,4995] : List ℕ) ++ (p++s).map Fin.val).length) 0 = 2097151
      rw [List.map_append, ← List.append_assoc]
      have index : 13 + ((([4160,4995] : List ℕ) ++ p.map Fin.val) ++ s.map Fin.val).length = 28+s.length := by
        simp only [List.length_append,List.length_cons,List.length_nil,List.length_map,hp]
        omega
      rw [index, List.foldl_append, hstate]
      exact hout
  · let s : List (Fin 8192) := [4224, 5894, 1864, 4417, 6086, 2057, 4355, 6278, 2251, 6043, 6497, 6564]
    have hs : s.length = 12 := rfl
    change (([4160,4995] : List ℕ) ++ p.map Fin.val).foldl advance initial = initial ++ List.ofFn z ++ [220077] at hstate
    refine ⟨20,true,true,p++s,?_,?_⟩
    · rw [List.length_append,hp,hs]
    · change ((([4160,4995] : List ℕ) ++ (p++s).map Fin.val).foldl advance initial).getD
        (13+(([4160,4995] : List ℕ) ++ (p++s).map Fin.val).length) 0 = 2097151
      rw [List.map_append, ← List.append_assoc]
      have index : 13 + ((([4160,4995] : List ℕ) ++ p.map Fin.val) ++ s.map Fin.val).length = 39 := by
        simp only [List.length_append,List.length_cons,List.length_nil,List.length_map,hp,hs]
      rw [index, List.foldl_append, hstate]
      simp [s, initial, advance, List.ofFn_succ, List.getD_eq_getElem?_getD]
