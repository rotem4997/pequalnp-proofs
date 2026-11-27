import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Identify inputs 10 and 15, which occur with the same point in the positive rows.
    The resulting 16-input search has 19 positive and 40 negative rows. Lifting the
    answer prepends the OR of the twins, costing one gate. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_2644_1
    (search : ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack 16 C ∧ C.size ≤ 22 ∧
      (∀ m ∈ ([33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772] : List ℕ), circuitFun 16 C (fun i => m.testBit i.val) = true) ∧
      (∀ m ∈ ([31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504] : List ℕ), circuitFun 16 C (fun i => m.testBit i.val) = false))
    (liftOr : ∀ (n k : ℕ) (hit : Fin n) (l r : Fin k) (σ : Fin n → Fin k)
      (C : Circuit), Monotone2 C → NestedCover.ReadsBack n C →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack k D ∧ D.size ≤ C.size + 1 ∧
        ∀ x : Fin k → Bool, circuitFun k D x =
          circuitFun n C (fun i => if i = hit then x l || x r else x (σ i))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x1 ∧       x1.size ≤ (23 : ℕ) ∧         (∀ x2 ∈ [(33 : ℕ), (513 : ℕ), (16385 : ℕ), (65537 : ℕ), (34 : ℕ), (66 : ℕ), (1026 : ℕ), (32770 : ℕ), (68 : ℕ), (132 : ℕ), (2052 : ℕ), (65540 : ℕ), (40 : ℕ), (136 : ℕ), (264 : ℕ), (4104 : ℕ), (80 : ℕ), (272 : ℕ), (528 : ℕ), (8208 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];                   (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x3;                 have x4 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x3;                 (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x3;                 (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x4;               have x5 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x4;               (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x5,             (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.false := by
  obtain ⟨C, hm, hb, hs, hp, hn⟩ := search
  let σ (i : Fin 16) : Fin 17 := if i.val = 15 then 16 else ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  obtain ⟨D, hD, hB, hS, ev⟩ := liftOr 16 17 10 10 15 σ C hm hb
  let q (m : ℕ) := (m % 32768) ||| ((m / 32768 % 2) * 1024) ||| ((m / 65536 % 2) * 32768)
  let ps := ([33, 513, 16385, 65537, 34, 66, 1026, 32770, 68, 132, 2052, 65540, 40, 136, 264, 4104, 80, 272, 528, 8208] : List ℕ)
  let ns := ([31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455, 8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040] : List ℕ)
  have proj : ∀ m ∈ ps ++ ns, ∀ i : Fin 16,
      (if i = 10 then m.testBit 10 || m.testBit 15 else m.testBit (σ i).val) =
        (q m).testBit i.val := by decide +kernel
  have row (m : ℕ) (h : m ∈ ps ++ ns) :
      circuitFun 17 D (fun i => m.testBit i.val) =
        circuitFun 16 C (fun i => (q m).testBit i.val) :=
    (ev _).trans (congrArg (circuitFun 16 C) (funext (proj m h)))
  have ptab : ∀ m ∈ ps, q m ∈ ([33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772] : List ℕ) := by decide +kernel
  have ntab : ∀ m ∈ ns, q m ∈ ([31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504] : List ℕ) := by decide +kernel
  refine ⟨D, hD, hB, by omega, ?_, ?_⟩
  · intro m h
    exact (row m (List.mem_append_left _ h)).trans (hp _ (ptab m h))
  · intro m h
    exact (row m (List.mem_append_right _ h)).trans (hn _ (ntab m h))
