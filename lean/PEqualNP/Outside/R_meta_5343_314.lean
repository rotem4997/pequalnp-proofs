import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

-- An initial AND can be set to false after dropping its sole positive edge.
-- An initial OR can be supplied as a fifteenth input on the sample rows.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5343_314
    (peel :
      let sat (n s : ℕ) (P N : List ℕ) := FormulaSat (enc n s (fun r => decide (r ∈ P)) (P ++ N))
      let lift (k r : ℕ) := if r.testBit (k / 16) || r.testBit (k % 16) then r + 16384 else r
      let digit (c i : ℕ) := (c / 16 ^ i) % 16
      let image (c r : ℕ) := ((List.range 14).filter r.testBit).foldl (fun m i => m + 2 ^ digit c i) 0
      ∀ P N K D : List ℕ, (∀ r ∈ P ++ N, r < 16384) → P.Nodup → (∀ r ∈ P, r ∉ N) → P ≠ [] → K ≠ [] → D ≠ [] →
        (∀ i < 14, ∀ j < 14, i < j → ∃ c : ℕ,
          ((List.range 14).map (digit c)).Perm (List.range 14) ∧
          (P.map (image c)).Perm P ∧ (N.map (image c)).Perm N ∧
          16 * min (digit c i) (digit c j) + max (digit c i) (digit c j) ∈ K ∧
          ∃ d ∈ D, ∀ r ∈ P, r.testBit i = true → r.testBit j = true → image c r = d) →
        sat 14 24 P N →
        (∃ d ∈ D, sat 14 22 (P.erase d) N) ∨
        ∃ k ∈ K, sat 15 23 (P.map (lift k)) (N.map (lift k)))
    (andCases :
      let P : List ℕ := [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let N : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129]
      ∀ d ∈ ([257, 514, 4100] : List ℕ), ¬ FormulaSat (enc 14 22
        (fun r => decide (r ∈ P.erase d)) (P.erase d ++ N)))
    (orCases :
      let P : List ℕ := [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let N : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129]
      let lift (k r : ℕ) := if r.testBit (k / 16) || r.testBit (k % 16) then r + 16384 else r
      ∀ k ∈ ([1, 2, 7, 8, 9, 18, 19, 24, 25, 27, 36, 38, 41, 44] : List ℕ), ¬ FormulaSat (enc 15 23
        (fun r => decide (r ∈ P.map (lift k))) (P.map (lift k) ++ N.map (lift k))))
    : have x1 : List ℕ := [(257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ), (129 : ℕ)];       (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: (10656 : ℕ) :: x2;     have x3 : List ℕ := (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: (8488 : ℕ) :: x2;     (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: (5186 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: (4304 : ℕ) :: x2;     (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: (2338 : ℕ) :: x3;   have x4 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x3;   (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x4; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (14 : ℕ) (24 : ℕ) (fun (x3 : ℕ) => Decidable.decide (x3 ∈ x1)) (x1 ++ x2)) := by
  let P : List ℕ := [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let N : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129]
  let K : List ℕ := [1, 2, 7, 8, 9, 18, 19, 24, 25, 27, 36, 38, 41, 44]
  let D : List ℕ := [257, 514, 4100]
  let digit (c i : ℕ) := (c / 16 ^ i) % 16
  let image (c r : ℕ) := ((List.range 14).filter r.testBit).foldl (fun m i => m + 2 ^ digit c i) 0
  let maps : List ℕ := [62129658859368976, 28502781892209031, 61863585619522576, 28236708652362631, 44113344757904656, 10486467790744711, 43851652369036816, 10224775401876871, 57872487274582576, 24245610307422631, 53366765914559536, 19739888947399591, 56814765646943536, 23187888679783591, 52313425137899056, 18686548170739111]
  let valid (c : ℕ) : Prop := ((List.range 14).map (digit c)).Perm (List.range 14) ∧
    (P.map (image c)).Perm P ∧ (N.map (image c)).Perm N
  have hv : ∀ c ∈ maps, valid c := by decide +kernel
  let pick (i j : ℕ) := (maps.find? (fun c =>
    decide (16 * min (digit c i) (digit c j) + max (digit c i) (digit c j) ∈ K))).getD 0
  have cover : ∀ i j : Fin 14, i < j →
      let c := pick i.val j.val
      c ∈ maps ∧ 16 * min (digit c i.val) (digit c j.val) + max (digit c i.val) (digit c j.val) ∈ K ∧
      ∃ d ∈ D, ∀ r ∈ P, r.testBit i.val = true → r.testBit j.val = true → image c r = d := by
    decide +kernel
  have symm : (∀ i < 14, ∀ j < 14, i < j → ∃ c : ℕ,
          ((List.range 14).map (digit c)).Perm (List.range 14) ∧
          (P.map (image c)).Perm P ∧ (N.map (image c)).Perm N ∧
          16 * min (digit c i) (digit c j) + max (digit c i) (digit c j) ∈ K ∧
          ∃ d ∈ D, ∀ r ∈ P, r.testBit i = true → r.testBit j = true → image c r = d) := by
    intro i hi j hj hij
    have h := cover ⟨i, hi⟩ ⟨j, hj⟩ hij
    let c := pick i j
    obtain ⟨hper, hp, hn⟩ := hv c h.1
    exact ⟨c, hper, hp, hn, h.2.1, h.2.2⟩
  change ¬ FormulaSat (enc 14 24 (fun r => decide (r ∈ P)) (P ++ N))
  intro model
  obtain h | h := peel P N K D (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) symm model
  · obtain ⟨d, hd, smaller⟩ := h
    exact andCases d hd smaller
  · obtain ⟨k, hk, smaller⟩ := h
    exact orCases k hk smaller
