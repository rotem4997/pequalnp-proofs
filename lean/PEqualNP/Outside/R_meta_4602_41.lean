import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4602_41
    (compile : ∀ S L : List (BitVec 59), S.length = 14 → L.length ≤ 25 →
    (∀ i : Fin L.length,
      ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
      L.get i = a &&& b ∨ L.get i = a ||| b) →
    ∃ gs : List (Bool × Fin 40 × Fin 40), gs.length = 25 ∧
      ∀ i : Fin L.length,
        (gs.foldl (fun (w : List (BitVec 59)) (t : Bool × Fin 40 × Fin 40) =>
        w ++ [if t.1 = true then w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0
          else w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0]) S).getD (14 + i.val) 0 = L.get i)
    (generate : let S : List (BitVec 59) := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
    let codes : List Nat := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
    ∃ L : List (BitVec 59), L.length ≤ 25 ∧ L.Nodup ∧ (∀ a ∈ L, a ∉ S) ∧
    (∀ i : Fin L.length,
      ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
      L.get i = a &&& b ∨ L.get i = a ||| b) ∧ ∃ (i j : Fin L.length) (h : Fin 16), i < j ∧
      let z := codes.getD h.val 0
      let u := z % 64
      let v := z / 64
      let a := L.get i
      let b := L.get j
      (if u < 21 then a ||| b else a &&& b) = 2097151 ∧
        a.getLsbD u ≠ b.getLsbD u ∧ a.getLsbD u = b.getLsbD v ∧ b.getLsbD u = a.getLsbD v) :
    have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (39 : ℕ)) (x5 : Fin (39 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (25 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9 := by
  let S : List (BitVec 59) := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
  let codes : List Nat := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
  obtain ⟨L, cap, _, _, cm, i, j, h, order, hit⟩ := generate
  obtain ⟨gs,len,eq⟩ := compile S L rfl cap cm
  let a : Fin 39 := ⟨14+i.val, by have := i.isLt; omega⟩
  let b : Fin 39 := ⟨14+j.val, by have := j.isLt; omega⟩
  refine ⟨gs,a,b,h,len,by dsimp [a]; omega,by change 14+i.val < 14+j.val; omega,?_⟩
  change (if codes.getD h.val 0 % 64 < 21 then _ else _) = _ ∧ _
  dsimp only [a,b]
  rw [eq i, eq j]
  exact hit
