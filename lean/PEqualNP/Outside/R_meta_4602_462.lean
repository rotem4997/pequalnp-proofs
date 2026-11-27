import PEqualNP.Defs

-- Cut the 25-gate synthesis after at most 13 gates with at most 14 cut signals,
-- compress 59 rows by bit-dominance mask q, and finish in at most 12 gates.
theorem PEqualNP.Outside.R_meta_4602_462
    (hLift :
      let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
        ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
      let cover := fun (K : List ℕ) (q u v : ℕ) =>
        q.testBit u = true ∧ q.testBit v = true ∧ ∀ i < 59, ∃ j < 59,
          q.testBit j = true ∧ (j < 21 ↔ i < 21) ∧ ∀ w ∈ K,
            if i < 21 then (w.testBit j = true → w.testBit i = true)
            else (w.testBit i = true → w.testBit j = true)
      ∀ (K : List ℕ) (q u v : ℕ) (U : List ℕ) (aq bq : ℕ),
        (∀ w ∈ K, w < 2 ^ 59) → cover K q u v →
        let B := K.map fun w => w &&& q
        legal B U → aq ∈ B ++ U → bq ∈ B ++ U →
        (if u < 21 then aq ||| bq else aq &&& bq) = 2097151 &&& q →
        aq.testBit u ≠ bq.testBit u → aq.testBit u = bq.testBit v → bq.testBit u = aq.testBit v →
        ∃ V : List ℕ, V.length ≤ U.length ∧ legal K V ∧ ∃ a ∈ K ++ V, ∃ b ∈ K ++ V,
          (if u < 21 then a ||| b else a &&& b) = 2097151 ∧
          a.testBit u ≠ b.testBit u ∧ a.testBit u = b.testBit v ∧ b.testBit u = a.testBit v)
    (hGlue :
      let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
        ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
      let step := fun (ws : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
        ws ++ [if g.1 = true then ws.getD g.2.1.val 0 ||| ws.getD g.2.2.val 0
               else ws.getD g.2.1.val 0 &&& ws.getD g.2.2.val 0]
      ∀ (init : List (BitVec 59)) (F K V : List ℕ) (a b : ℕ),
        init.length = 14 → F.length + V.length ≤ 25 →
        legal (init.map BitVec.toNat) F → (∀ k ∈ K, k ∈ init.map BitVec.toNat ++ F) →
        legal K V → a ∈ K ++ V → b ∈ K ++ V →
        a ∉ init.map BitVec.toNat → b ∉ init.map BitVec.toNat → a ≠ b →
        ∃ (gs : List (Bool × Fin 40 × Fin 40)) (l r : Fin 39),
          gs.length = 25 ∧ 14 ≤ l.val ∧ l < r ∧
          let W := gs.foldl step init
          ((W.getD l.val 0).toNat = a ∧ (W.getD r.val 0).toNat = b) ∨
          ((W.getD l.val 0).toNat = b ∧ (W.getD r.val 0).toNat = a))
    (hCut :
      let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
        ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
      let cover := fun (K : List ℕ) (q u v : ℕ) =>
        q.testBit u = true ∧ q.testBit v = true ∧ ∀ i < 59, ∃ j < 59,
          q.testBit j = true ∧ (j < 21 ↔ i < 21) ∧ ∀ w ∈ K,
            if i < 21 then (w.testBit j = true → w.testBit i = true)
            else (w.testBit i = true → w.testBit j = true)
      let A : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
      let C : List ℕ := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
      ∃ (F K : List ℕ) (q : ℕ) (U : List ℕ) (aq bq : ℕ) (i : Fin 16),
        F.length ≤ 13 ∧ K.length ≤ 14 ∧ U.length ≤ 12 ∧ legal A F ∧ (∀ k ∈ K, k ∈ A ++ F) ∧
        let p := C.getD i.val 0; let u := p % 64; let v := p / 64
        cover K q u v ∧ let B := K.map fun w => w &&& q
        legal B U ∧ aq ∈ B ++ U ∧ bq ∈ B ++ U ∧
        (if u < 21 then aq ||| bq else aq &&& bq) = 2097151 &&& q ∧
        aq.testBit u ≠ bq.testBit u ∧ aq.testBit u = bq.testBit v ∧ bq.testBit u = aq.testBit v) :
    have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (39 : ℕ)) (x5 : Fin (39 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (25 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9 := by
  let legal := fun (A U : List ℕ) => ∀ i : Fin U.length,
    ∃ a ∈ A ++ U.take i.val, ∃ b ∈ A ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
  let step := fun (ws : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) =>
    ws ++ [if g.1 = true then ws.getD g.2.1.val 0 ||| ws.getD g.2.2.val 0
           else ws.getD g.2.1.val 0 &&& ws.getD g.2.2.val 0]
  let initBV : List (BitVec 59) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]
  let initNat : List ℕ := [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]
  let C : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]
  obtain ⟨F, K, q, U, aq, bq, i, hF, hKlen, hU, hlegF, hKsub, hcov, hlegU, haq, hbq, hWqEq, hne, he1, he2⟩ := hCut
  let p := C.getD i.val 0
  let u := p % 64
  let v := p / 64
  have hInitMap : initBV.map BitVec.toNat = initNat := by decide
  have hInitBound : ∀ w ∈ initNat, w < 2 ^ 59 := by decide
  have hFBound : ∀ (j : ℕ) (hj : j < F.length), F[j] < 2 ^ 59 := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      obtain ⟨a, ha, b, hb, hEq⟩ := hlegF ⟨j, hj⟩
      have hmem (z : ℕ) (hz : z ∈ initNat ++ F.take j) : z < 2 ^ 59 := by
        rcases List.mem_append.mp hz with hz | hz
        · exact hInitBound z hz
        · rcases List.mem_iff_getElem.mp hz with ⟨t, ht, rfl⟩
          rw [List.length_take] at ht
          have htj : t < j := Nat.lt_of_lt_of_le ht (Nat.min_le_left _ _)
          have htF : t < F.length := Nat.lt_trans htj hj
          rw [List.getElem_take]
          exact ih t htj htF
      have haB := hmem a ha
      have hbB := hmem b hb
      rw [List.get_eq_getElem] at hEq
      rcases hEq with hEq | hEq
      · rw [hEq]
        exact Nat.and_lt_two_pow _ hbB
      · rw [hEq]
        exact Nat.or_lt_two_pow haB hbB
  have hKBound : ∀ w ∈ K, w < 2 ^ 59 := by
    intro w hw
    rcases List.mem_append.mp (hKsub w hw) with hw | hw
    · exact hInitBound w hw
    · rcases List.mem_iff_getElem.mp hw with ⟨j, hj, rfl⟩
      exact hFBound j hj
  have hFull := hLift K q u v U aq bq hKBound hcov hlegU haq hbq hWqEq hne he1 he2
  obtain ⟨V, hVlen, hlegV, a, ha, b, hb, hGoal, hneF, he1F, he2F⟩ := hFull
  have hNoInit : ∀ w ∈ initNat, (w ||| 2097151) ≠ 2097151 ∧ (w &&& 2097151) ≠ 2097151 := by decide
  have haNot : a ∉ initNat := by
    intro hmem
    by_cases hu : u < 21
    · have hOp : a ||| b = 2097151 := by simpa only [hu, ite_true] using hGoal
      have hAbs : a ||| 2097151 = 2097151 := by
        calc a ||| 2097151 = a ||| (a ||| b) := by rw [hOp]
        _ = (a ||| a) ||| b := by rw [Nat.or_assoc]
        _ = a ||| b := by rw [Nat.or_self]
        _ = 2097151 := hOp
      exact (hNoInit a hmem).1 hAbs
    · have hOp : a &&& b = 2097151 := by simpa only [hu, ite_false] using hGoal
      have hAbs : a &&& 2097151 = 2097151 := by
        calc a &&& 2097151 = a &&& (a &&& b) := by rw [hOp]
        _ = (a &&& a) &&& b := by rw [Nat.and_assoc]
        _ = a &&& b := by rw [Nat.and_self]
        _ = 2097151 := hOp
      exact (hNoInit a hmem).2 hAbs
  have hbNot : b ∉ initNat := by
    intro hmem
    by_cases hu : u < 21
    · have hOp : a ||| b = 2097151 := by simpa only [hu, ite_true] using hGoal
      have hAbs : b ||| 2097151 = 2097151 := by
        calc b ||| 2097151 = b ||| (b ||| a) := by rw [Nat.or_comm b a, hOp]
        _ = (b ||| b) ||| a := by rw [Nat.or_assoc]
        _ = b ||| a := by rw [Nat.or_self]
        _ = 2097151 := by rw [Nat.or_comm, hOp]
      exact (hNoInit b hmem).1 hAbs
    · have hOp : a &&& b = 2097151 := by simpa only [hu, ite_false] using hGoal
      have hAbs : b &&& 2097151 = 2097151 := by
        calc b &&& 2097151 = b &&& (b &&& a) := by rw [Nat.and_comm b a, hOp]
        _ = (b &&& b) &&& a := by rw [Nat.and_assoc]
        _ = b &&& a := by rw [Nat.and_self]
        _ = 2097151 := by rw [Nat.and_comm, hOp]
      exact (hNoInit b hmem).2 hAbs
  have hab : a ≠ b := fun h => hneF (by rw [h])
  have hFVlen : F.length + V.length ≤ 25 := by omega
  have hlegF' : legal (initBV.map BitVec.toNat) F := by rw [hInitMap]; exact hlegF
  have hKsub' : ∀ k ∈ K, k ∈ initBV.map BitVec.toNat ++ F := by rw [hInitMap]; exact hKsub
  have haNot' : a ∉ initBV.map BitVec.toNat := by rw [hInitMap]; exact haNot
  have hbNot' : b ∉ initBV.map BitVec.toNat := by rw [hInitMap]; exact hbNot
  obtain ⟨gs, l, r, hgsLen, hlow, hlt, hpair⟩ :=
    hGlue initBV F K V a b rfl hFVlen hlegF' hKsub' hlegV ha hb haNot' hbNot' hab
  refine ⟨gs, l, r, i, hgsLen, hlow, hlt, ?_⟩
  let W := gs.foldl step initBV
  let x11 := W.getD l.val 0
  let x12 := W.getD r.val 0
  change (if u < 21 then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec 59) ∧
    x11.getLsbD u ≠ x12.getLsbD u ∧ x11.getLsbD u = x12.getLsbD v ∧ x12.getLsbD u = x11.getLsbD v
  have ht : (2097151 : BitVec 59).toNat = 2097151 := by decide
  rcases hpair with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · have hL' : x11.toNat = a := hL
    have hR' : x12.toNat = b := hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [ht]
      by_cases cond : u < 21
      · simpa only [cond, ite_true, BitVec.toNat_or, hL', hR'] using hGoal
      · simpa only [cond, ite_false, BitVec.toNat_and, hL', hR'] using hGoal
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hL', hR']; exact hneF
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hL', hR']; exact he1F
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hR', hL']; exact he2F
  · have hL' : x11.toNat = b := hL
    have hR' : x12.toNat = a := hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [ht]
      by_cases cond : u < 21
      · have hOp : b ||| a = 2097151 := by rw [Nat.or_comm]; exact by simpa only [cond, ite_true] using hGoal
        simpa only [cond, ite_true, BitVec.toNat_or, hL', hR'] using hOp
      · have hOp : b &&& a = 2097151 := by rw [Nat.and_comm]; exact by simpa only [cond, ite_false] using hGoal
        simpa only [cond, ite_false, BitVec.toNat_and, hL', hR'] using hOp
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hL', hR']; exact Ne.symm hneF
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hL', hR']; exact he2F
    · rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, hR', hL']; exact he1F
