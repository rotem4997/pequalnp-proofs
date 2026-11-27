import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3531_742
    (bridge :
      let step := fun (us : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
        us ++ [if g.1 = true then us.getD g.2.1.val 0 ||| us.getD g.2.2.val 0
          else us.getD g.2.1.val 0 &&& us.getD g.2.2.val 0]
      let stepNat := fun (us : List ℕ) (g : Bool × ℕ × ℕ) =>
        us ++ [if g.1 = true then us.getD g.2.1 0 ||| us.getD g.2.2 0
          else us.getD g.2.1 0 &&& us.getD g.2.2 0]
      ∀ (us : List (BitVec 59)) (gs : List (Bool × Fin 40 × Fin 40)),
        (gs.map (fun g => (g.1,g.2.1.val,g.2.2.val))).foldl stepNat (us.map BitVec.toNat) =
          (gs.foldl step us).map BitVec.toNat)
    (witness :
      let initial : List (BitVec 59) :=
        [95229015649944073,63038587928642,256463372304,4292497062825988,
          8521482511360,14003410187716736,55389823206179104,189297016294080519,
          155696362464215096,218994303131713984,183565875465424384,229736628136996864,
          270286071508729856,288160007409369088]
      let choices : List ℕ := [64,256,448,1429,1557,2389,3669,1494,1558,1750,1942,2390,2902,1688,1880,2008]
      ∃ (gs : List (Bool × Fin 40 × Fin 40)) (l r : Fin 39) (i : Fin 16),
        gs.length = 25 ∧ 14 ≤ l.val ∧ l < r ∧
        let p := choices.getD i.val 0
        let u := p % 64
        let v := p / 64
        let ws := gs.foldl (fun us g => us ++ [if g.1 = true then
          us.getD g.2.1.val 0 ||| us.getD g.2.2.val 0 else
          us.getD g.2.1.val 0 &&& us.getD g.2.2.val 0]) initial
        let a := ws.getD l.val 0
        let b := ws.getD r.val 0
        (if u < 21 then a ||| b else a &&& b) = 2097151 ∧
          a.getLsbD u ≠ b.getLsbD u ∧ a.getLsbD u = b.getLsbD v ∧ b.getLsbD u = a.getLsbD v) :
    ∃ (x1 : List (Bool × ℕ × ℕ)) (x2 : ℕ) (x3 : ℕ) (x4 : Fin (16 : ℕ)),   x1.length ≤ (25 : ℕ) ∧     (14 : ℕ) ≤ x2 ∧       x2 < x3 ∧         x3 < (14 : ℕ) + x1.length ∧           have x5 : ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)].getD ↑x4 (0 : ℕ);           have x6 : ℕ := x5 % (64 : ℕ);           have x7 : ℕ := x5 / (64 : ℕ);           have x8 : List ℕ := List.foldl (fun (x8 : List ℕ) (x9 : Bool × ℕ × ℕ) => x8 ++ [(fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)) x8 x9]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)] x1;           have x9 : ℕ := x8.getD x2 (0 : ℕ);           have x10 : ℕ := x8.getD x3 (0 : ℕ);           (if x6 < (21 : ℕ) then x9 ||| x10 else x9 &&& x10) = (2097151 : ℕ) ∧ x9.testBit x6 ≠ x10.testBit x6 ∧ x9.testBit x6 = x10.testBit x7 ∧ x10.testBit x6 = x9.testBit x7 := by
  obtain ⟨gs,l,r,i,hLen,hLow,hOrder,hGoal,hne,hl,hr⟩ := witness
  let base : List (BitVec 59) :=
    [95229015649944073,63038587928642,256463372304,4292497062825988,
      8521482511360,14003410187716736,55389823206179104,189297016294080519,
      155696362464215096,218994303131713984,183565875465424384,229736628136996864,
      270286071508729856,288160007409369088]
  let pairs : List ℕ := [64,256,448,1429,1557,2389,3669,1494,1558,1750,1942,2390,2902,1688,1880,2008]
  let p := pairs.getD i.val 0
  let u := p % 64
  let v := p / 64
  let wordStep := fun (us : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
    us ++ [if g.1 = true then us.getD g.2.1.val 0 ||| us.getD g.2.2.val 0
      else us.getD g.2.1.val 0 &&& us.getD g.2.2.val 0]
  let natStep := fun (us : List ℕ) (g : Bool × ℕ × ℕ) =>
    us ++ [if g.1 = true then us.getD g.2.1 0 ||| us.getD g.2.2 0
      else us.getD g.2.1 0 &&& us.getD g.2.2 0]
  let program := gs.map (fun g => (g.1,g.2.1.val,g.2.2.val))
  let words := gs.foldl wordStep base
  let a := words.getD l.val 0
  let b := words.getD r.val 0
  have lens : program.length = 25 := by simpa only [program, List.length_map] using hLen
  refine ⟨program,l.val,r.val,i,by omega,hLow,hOrder,by omega,?_⟩
  change (if u < 21 then (program.foldl natStep (base.map BitVec.toNat)).getD l.val 0 |||
                          (program.foldl natStep (base.map BitVec.toNat)).getD r.val 0
           else (program.foldl natStep (base.map BitVec.toNat)).getD l.val 0 &&&
                  (program.foldl natStep (base.map BitVec.toNat)).getD r.val 0) = 2097151 ∧
    ((program.foldl natStep (base.map BitVec.toNat)).getD l.val 0).testBit u ≠
      ((program.foldl natStep (base.map BitVec.toNat)).getD r.val 0).testBit u ∧
    ((program.foldl natStep (base.map BitVec.toNat)).getD l.val 0).testBit u =
      ((program.foldl natStep (base.map BitVec.toNat)).getD r.val 0).testBit v ∧
    ((program.foldl natStep (base.map BitVec.toNat)).getD r.val 0).testBit u =
      ((program.foldl natStep (base.map BitVec.toNat)).getD l.val 0).testBit v
  have tr : program.foldl natStep (base.map BitVec.toNat) = words.map BitVec.toNat := bridge base gs
  have getWord (xs : List (BitVec 59)) (j : ℕ) :
      (xs.map BitVec.toNat).getD j 0 = (xs.getD j 0).toNat := by
    induction xs generalizing j with
    | nil => rfl
    | cons w xs ih =>
      cases j with
      | zero => rfl
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j
  rw [tr, getWord, getWord]
  change (if u < 21 then a.toNat ||| b.toNat else a.toNat &&& b.toNat) = 2097151 ∧
    a.toNat.testBit u ≠ b.toNat.testBit u ∧ a.toNat.testBit u = b.toNat.testBit v ∧
    b.toNat.testBit u = a.toNat.testBit v
  refine ⟨?_, hne, hl, hr⟩
  change (if u < 21 then a ||| b else a &&& b) = (2097151 : BitVec 59) at hGoal
  have natEq := congrArg BitVec.toNat hGoal
  by_cases cond : u < 21
  · simpa [cond, BitVec.toNat_or] using natEq
  · simpa [cond, BitVec.toNat_and] using natEq
