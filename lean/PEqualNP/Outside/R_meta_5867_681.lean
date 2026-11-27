import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_5867_681
  (selectors : ∀ (C : Circuit) (a b : ℕ) (N : Fin 236 → Fin 26 → Bool),
    Monotone2 C → {i : ℕ | ∃ g : Gate, C.gates[i]? = some g ∧ g.op = .and}.ncard ≤ 7 →
    let f (x : Fin 26 → Bool) := wireVal C (List.ofFn x) a && wireVal C (List.ofFn x) b
    (∀ r, f (N r) = false) →
    (∀ r s, r ≠ s → ∃ x, f x = true ∧ ∀ i, x i = true → N r i = true ∨ N s i = true) →
    let H (M : Finset (Fin 26)) := M.biUnion (fun i => Finset.univ.filter (fun r => N r i))
    ∃ A B, ((H A)ᶜ ∪ H B).card ≤ 128 ∧ ((H B)ᶜ ∪ H A).card ≤ 128)
  (bounded : ∀ (C : Circuit) (a b : ℕ), Monotone2 C → C.size ≤ 62 →
    8 ≤ {i : ℕ | ∃ g : Gate, C.gates[i]? = some g ∧ g.op = .and}.ncard →
    let f (x : List Bool) := wireVal C x a && wireVal C x b
    (∀ p l, p ∈ singerLines3 l → f (pointLineInput 13 13 p l) = true) →
    (∀ P, let L := missLines singerLines3 P
      P = zeroSet singerLines3 L → ¬IsGeneric singerLines3 0 P L → f (incidenceInput P L) = false) →
    (∃ I : Finset ℕ, 19 ≤ I.card ∧ ∀ i ∈ I, 26 ≤ i ∧ i ≤ a ∧
      (gateAt C (i-26)).op = GateOp.or) → False) :
have x1 : Bool → List Bool → Prop := fun (x1 : Bool) (x2 : List Bool) =>   if x1 = Bool.true then ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 = PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x3 x4   else     ∃ (x3 : Finset (Fin (13 : ℕ))),       have x4 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3;       x3 = PEqualNP.GenericRejection.zeroSet PEqualNP.HeptadCover.singerLines3 x4 ∧ ¬PEqualNP.GenericRejection.IsGeneric PEqualNP.HeptadCover.singerLines3 (0 : ℕ) x3 x4 ∧ x2 = PEqualNP.GenericRejection.incidenceInput x3 x4; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) =>   have x4 : Finset (Fin (13 : ℕ)) := (PEqualNP.HeptadCover.singerLines3 x3).erase x2;   PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∀ (x5 x6 : Fin ((26 : ℕ) + x3.size)), x5 ≠ x6 → (∀ (x8 : Bool) (x9 : List Bool), x1 x8 x9 → (PEqualNP.LowMerge.wireVal x3 x9 ↑x5 && PEqualNP.LowMerge.wireVal x3 x9 ↑x6) = x8) → PEqualNP.LowMerge.wireVal x3 (x2 (0 : Fin (13 : ℕ)) (0 : Fin (13 : ℕ))) ↑x5 = Bool.false → (∀ (x10 : List Bool), x1 Bool.false x10 → ∀ (x12 : ℕ), x12 = ↑x5 ∨ x12 = ↑x6 → PEqualNP.LowMerge.wireVal x3 x10 x12 = Bool.false → ∃ (x15 : Finset ℕ), List.count Bool.false x10 ≤ x15.card + (1 : ℕ) ∧ ∀ x16 ∈ x15, (26 : ℕ) ≤ x16 ∧ x16 ≤ x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x16 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.LowMerge.wireVal x3 x10 x16 = Bool.false) → (∀ x11 < x3.size, (26 : ℕ) + x11 ≠ ↑x5 → (26 : ℕ) + x11 ≠ ↑x6 → ∀ (x15 : ℕ), x15 < (26 : ℕ) + x11 ∨ x15 = (26 : ℕ) + x3.size → ∃ (x17 : Bool) (x18 : List Bool), x1 x17 x18 ∧ PEqualNP.LowMerge.wireVal x3 x18 ((26 : ℕ) + x11) = x17 ∧ PEqualNP.LowMerge.wireVal x3 x18 x15 ≠ x17) → (63 : ℕ) ≤ x3.size := by
  -- Each row is a bit mask, with its thirteen points first and its thirteen lines second.
  let rows : Array Nat := #[0x3ffe000,0x17dc001,0x2fb8002,0x798003,0x1f72004,0x1750005,0xf30006,0x3ee4008,0x16c4009,0x2ea000a,0x68000b,0x1e6000c,0x3dca010,0x15c8011,0x2d88012,0x1d42014,0xd00016,0x3cc0018,0x3b96020,0x1394021,0x2b90022,0x1b12024,0x3a84028,0x1a0002c,0x3982030,0x1180031,0x372e040,0x170c041,0x2728042,0x1722044,0x3624048,0x350a050,0x3400058,0x3306060,0x2300062,0x2e5e080,0x65c081,0x2e18082,0xe52084,0x2e44088,0x2c4a090,0x448091,0x2a160a0,0x2140a1,0x28020b0,0x260e0c0,0x6020c4,0x6000cf,0x1cbe100,0x149c101,0xcb8102,0x1c32104,0x1410105,0x1ca4108,0x1c8a110,0x1896120,0x890122,0x142e140,0x428142,0x140015d,0x1006160,0xc1e180,0xc04188,0xc0019e,0x4081d3,0x397c200,0x115c201,0x2938202,0x118203,0x1970204,0x3864208,0x1044209,0x282020a,0x3948210,0x3914220,0x312c240,0x1120244,0x1100275,0x285c280,0x850284,0x28002ba,0x200c2c0,0x183c300,0x1808310,0x180033c,0x1004369,0x8103a6,0x32fa400,0x12d8401,0x22b8402,0x1272404,0x230406,0x32e0408,0x30ca410,0x2088412,0x1042414,0x3292420,0x322a440,0x1208441,0x120046d,0x225a480,0x2240488,0x2104a7,0x22004ea,0x10ba500,0x10a0508,0x1080539,0x1002574,0x1a580,0x3078600,0x104061d,0x3010620,0x3000678,0x20086d2,0x1010725,0x102074c,0x1008751,0x100077d,0x18783,0x25f6800,0x5d4801,0x25b0802,0x572804,0x24e4808,0x46080c,0x25c2810,0x2196820,0x112824,0x2084828,0x2526840,0x504841,0x500857,0x2456880,0x2410882,0x44089d,0x24008da,0x4b6900,0x482910,0x48091b,0x42094e,0x410987,0x4049c9,0x4029d4,0x4009df,0x2174a00,0x2140a10,0x110a27,0x2100a72,0x2004ae8,0x34b00,0x14ba1,0x20f2c00,0xd0c01,0x2080c3a,0x2022c40,0x2002cf0,0x90d23,0x12da4,0x2020e4a,0x50e85,0x2040e98,0x2010ea2,0x2000efa,0x30f06,0x10fa7,0xbef000,0x3cd001,0xba9002,0xb63004,0x341005,0xae5008,0x9cb010,0x8c1018,0xb87020,0x32f040,0x225048,0x10b050,0x301067,0xa4f080,0xa09082,0xa010ae,0x2050e9,0x8af100,0x8d101,0x823104,0x88113a,0x8031b4,0x96d200,0x905220,0x901236,0x109253,0x84129c,0x82130e,0x809392,0x8053a8,0x8013be,0xd3c1,0x2eb400,0x283420,0x28142b,0x22144e,0x24148d,0x2094c3,0x2034e4,0x2014ef,0x89513,0xb5d0,0x69600,0x49691,0x29742,0x97d3,0x1e7800,0x1a1802,0x181833,0x103874,0x47880,0x85929,0x79e0,0x141a15,0x121a46,0x105a61,0x101a77,0x45a89,0x25b48,0x5be9,0xc1c19,0x43c94,0xa1d0a,0x83d30,0x81d3b,0x23d44,0x3df4,0x61e0c,0x41e9d,0x21f4e,0x1fff]





  let hit (r : Fin 236) (i : Fin 26) : Bool := (rows[r.val]!).testBit i.val
  let points (r : Fin 236) : Finset (Fin 13) := Finset.univ.filter fun p => hit r (Fin.castAdd 13 p)
  let lines (r : Fin 236) : Finset (Fin 13) := Finset.univ.filter fun l => hit r (Fin.natAdd 13 l)
  let incident (a b : Fin 26) : Bool := decide (
    (a.val<13 ∧ 13≤b.val ∧ Fin.ofNat 13 a.val ∈ singerLines3 (Fin.ofNat 13 b.val)) ∨
    (b.val<13 ∧ 13≤a.val ∧ Fin.ofNat 13 b.val ∈ singerLines3 (Fin.ofNat 13 a.val)))
  let neighbors (a b : Fin 26) : Finset (Fin 26) := Finset.univ.filter fun i => incident a i ∧ incident b i
  let onRows (i : Fin 26) : Finset (Fin 236) := Finset.univ.filter fun r => hit r i
  have counts : ∀ i : Fin 26, (onRows i).card = 71 := by decide +kernel
  have pairCounts : ∀ a b : Fin 26, ¬incident a b → 22 ≤ (onRows a ∩ onRows b).card := by
    intro a
    fin_cases a <;> decide +kernel
  -- Two raw inputs on each side cannot span four incidences.
  have squareFree : ∀ a b : Fin 26, a ≠ b → (neighbors a b).card ≤ 1 := by decide +kernel
  have four (a b c d : Fin 26) (ab : a≠b) (cd : c≠d) :
      22 ≤ ((onRows a ∪ onRows b) ∩ (onRows c ∪ onRows d)).card := by
    have one (u v : Fin 26) (hu : onRows u ⊆ onRows a ∪ onRows b) (hv : onRows v ⊆ onRows c ∪ onRows d)
        (h : ¬incident u v) : 22 ≤ ((onRows a ∪ onRows b) ∩ (onRows c ∪ onRows d)).card :=
      (pairCounts u v h).trans (Finset.card_le_card (Finset.inter_subset_inter hu hv))
    by_cases ac : incident a c
    · by_cases ad : incident a d
      · by_cases bc : incident b c
        · by_cases bd : incident b d
          · have hc : c ∈ neighbors a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ac,bc⟩
            have hd : d ∈ neighbors a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ad,bd⟩
            exact False.elim (cd (Finset.card_le_one.mp (squareFree _ _ ab) c hc d hd))
          · exact one _ _ Finset.subset_union_right Finset.subset_union_right bd
        · exact one _ _ Finset.subset_union_right Finset.subset_union_left bc
      · exact one _ _ Finset.subset_union_left Finset.subset_union_right ad
    · exact one _ _ Finset.subset_union_left Finset.subset_union_left ac

  have legal : ∀ r : Fin 236, lines r = missLines singerLines3 (points r) ∧
      points r = zeroSet singerLines3 (lines r) ∧ ¬ IsGeneric singerLines3 0 (points r) (lines r) := by decide +kernel

  have rowAsInput : ∀ r : Fin 236, List.ofFn (hit r) = incidenceInput (points r) (lines r) := by decide +kernel
  have pairAsInput : ∀ p l : Fin 13, PEqualNP.LowMerge.pointLineInput 13 13 p l =
      List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) := by decide +kernel

  let mask (r : Fin 236) := (rows[r.val]!) % 8192
  have maskDef : ∀ r : Fin 236, (points r).sum (fun p => 2^p.val) = mask r := by decide +kernel
  have maskInc : StrictMono mask := by
    apply Fin.strictMono_iff_lt_succ.mpr
    decide +kernel
  have pointsInj : Function.Injective points := by
    intro i j h
    apply maskInc.injective
    rw [← maskDef,← maskDef,h]
  have mixed (i j : Fin 236) (ne : i ≠ j) :
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      (p∈points i ∨ p∈points j) ∧ (l∈lines i ∨ l∈lines j) := by
    have side (r s : Fin 236) (inc : ¬ points r ⊆ points s) :
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧ p∈points r ∧ l∈lines s := by
      obtain ⟨p,hp,hs⟩ := Finset.not_subset.mp inc
      rw [(legal s).2.1] at hs
      change p ∉ Finset.univ.filter _ at hs
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_forall,Classical.not_not] at hs
      obtain ⟨l,hl,h⟩ := hs
      exact ⟨p,l,h,hp,hl⟩
    by_cases ij : points i ⊆ points j
    · have ji : ¬ points j ⊆ points i := fun h => ne (pointsInj (Finset.Subset.antisymm ij h))
      obtain ⟨p,l,e,hp,hl⟩ := side j i ji
      exact ⟨p,l,e,Or.inr hp,Or.inl hl⟩
    · obtain ⟨p,l,e,hp,hl⟩ := side i j ij
      exact ⟨p,l,e,Or.inl hp,Or.inr hl⟩

  have capacityImpossible (A B : Finset (Fin 26)) :
      let h (M : Finset (Fin 26)) := M.biUnion onRows
      let left := (h A)ᶜ ∪ h B
      let right := (h B)ᶜ ∪ h A
      ¬ (left.card ≤ 128 ∧ right.card ≤ 128) := by
    classical
    intro h left right hsize
    have hasPair (M V : Finset (Fin 26)) (bound : ((h M)ᶜ ∪ h V).card ≤ 128) :
        ∃ a ∈ M, ∃ b ∈ M, a ≠ b := by
      by_contra! bad
      have small : (h M).card ≤ 71 := by
        rcases M.eq_empty_or_nonempty with e|⟨a,ha⟩
        · simp [h,e]
        · have e : M = {a} := Finset.ext fun i => by
            simp only [Finset.mem_singleton]
            exact ⟨fun hi => bad i hi a ha,fun eq => eq ▸ ha⟩
          simp [h,e,counts]
      have sub : ((h M)ᶜ : Finset (Fin 236)).card ≤ 128 :=
        (Finset.card_le_card Finset.subset_union_left).trans bound
      rw [Finset.card_compl,Fintype.card_fin] at sub
      omega
    obtain ⟨a,ha,b,hb,ab⟩ := hasPair A B hsize.1
    obtain ⟨c,hc,d,hd,cd⟩ := hasPair B A hsize.2
    have sub (M : Finset (Fin 26)) (x y : Fin 26) (hx : x∈M) (hy : y∈M) :
        onRows x ∪ onRows y ⊆ h M := by
      intro r hr
      rcases Finset.mem_union.mp hr with q|q
      · exact Finset.mem_biUnion.mpr ⟨x,hx,q⟩
      · exact Finset.mem_biUnion.mpr ⟨y,hy,q⟩
    have overlap := (four a b c d ab cd).trans (Finset.card_le_card
      (Finset.inter_subset_inter (sub A a b ha hb) (sub B c d hc hd)))
    have extended : h A ∩ h B ⊆ left ∩ right := by
      intro r hr
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hr).2,
        Finset.mem_union_right _ (Finset.mem_inter.mp hr).1⟩
    have large := overlap.trans (Finset.card_le_card extended)
    have cover : left ∪ right = Finset.univ := by
      ext r
      simp only [left,right,Finset.mem_union,Finset.mem_compl,Finset.mem_univ,iff_true]
      by_cases q : r∈h A
      · exact Or.inr (Or.inr q)
      · exact Or.inl (Or.inl q)
    have card := Finset.card_union_add_card_inter left right
    rw [cover,Finset.card_univ,Fintype.card_fin] at card
    omega
  intro T F C hC a b _ response anchor quota _
  have good (p l : Fin 13) (e : p ∈ singerLines3 l) :=
    response true (pointLineInput 13 13 p l) ⟨p,l,e,rfl⟩
  have no (P : Finset (Fin 13)) (h : P = zeroSet singerLines3 (missLines singerLines3 P))
      (d : ¬ IsGeneric singerLines3 0 P (missLines singerLines3 P)) :=
    response false (incidenceInput P (missLines singerLines3 P)) ⟨P,h,d,rfl⟩
  have heavy : 8 ≤ {i : ℕ | ∃ g : Gate, C.gates[i]? = some g ∧ g.op = .and}.ncard := by
    by_contra! few
    apply Nat.le_of_lt_succ at few
    apply False.elim
    obtain ⟨A,B,hA,hB⟩ := selectors C a b hit hC few (by
      intro r
      dsimp only
      rw [rowAsInput,(legal r).1]
      exact no (points r) (by rw [← (legal r).1]; exact (legal r).2.1)
        (by rw [← (legal r).1]; exact (legal r).2.2)) (by
      intro r s rs
      obtain ⟨p,l,hi,hp,hl⟩ := mixed r s rs
      refine ⟨fun i : Fin 26 => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l),?_,?_⟩
      · dsimp only
        rw [← pairAsInput p l]
        exact good p l hi
      · intro i on
        rcases of_decide_eq_true on with e|e
        · subst i
          simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using hp
        · subst i
          simpa only [lines, Finset.mem_filter, Finset.mem_univ, true_and] using hl)
    exact capacityImpossible A B ⟨hA,hB⟩
  by_contra! low
  apply bounded C a b hC (by omega) heavy good no
  have anchT : T false (F 0 0) := by
    let P := (singerLines3 0).erase 0
    exact ⟨P,by dsimp [P]; decide +kernel,by dsimp [P]; decide +kernel,rfl⟩
  obtain ⟨I,hI,each⟩ := quota (F 0 0) anchT a (Or.inl rfl) anchor
  have weight : (F 0 0).count false = 20 := by dsimp [F]; decide +kernel
  rw [weight] at hI
  exact ⟨I,by omega,fun i hi => ⟨(each i hi).1,(each i hi).2.1,(each i hi).2.2.1⟩⟩
