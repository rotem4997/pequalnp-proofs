import PEqualNP.Defs

-- Cut: symmetry breaking plus cubes. decode turns a satisfying assignment of the plain encoding
-- enc n s g rows back into a monotone circuit with at most s gates that agrees with g on the rows
-- (generic, any n and s). link is the generic cube link lemma (desk step L-meta-4805, verbatim):
-- such a circuit makes one of the 3 * (n + s) cubes of the symmetry-broken encoding enc2 satisfiable.
-- cubes says each of the 114 cubes of enc2 14 24 on the same 58 rows is unsatisfiable: finite
-- claims, each an LRAT-checkable SAT instance much smaller than the plain enc instance (lex order
-- on adjacent independent gates, first source and operation of the top gate fixed).
theorem PEqualNP.Outside.R_meta_5343_1
    (decode : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ n) →
      PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc n s g rows) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin n => r.testBit i.val)) = g r)
    (link : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < s → (∀ r ∈ rows, r < 2 ^ n) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin n => r.testBit i.val)) = g r) →
      ∃ k < PEqualNP.Defs.LratEncoding.enc2CubeCount n s,
        PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 n s g rows ++
          PEqualNP.Defs.LratEncoding.enc2Cube n s k))
    (cubes : ∀ k < PEqualNP.Defs.LratEncoding.enc2CubeCount 14 24,
      ¬ PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 14 24
        (fun r : ℕ => decide (r ∈ ([257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ)))
        (([257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ) ++
          ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129] : List ℕ)) ++
        PEqualNP.Defs.LratEncoding.enc2Cube 14 24 k)) :
    have x1 : List ℕ := [(257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ), (129 : ℕ)];       (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: (10656 : ℕ) :: x2;     have x3 : List ℕ := (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: (8488 : ℕ) :: x2;     (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: (5186 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: (4304 : ℕ) :: x2;     (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: (2338 : ℕ) :: x3;   have x4 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x3;   (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x4; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (14 : ℕ) (24 : ℕ) (fun (x3 : ℕ) => Decidable.decide (x3 ∈ x1)) (x1 ++ x2)) := by
  show ¬ PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc 14 24
    (fun r : ℕ => decide (r ∈ ([257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ)))
    (([257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ) ++
      ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129] : List ℕ)))
  intro hsat
  have hb : ∀ r ∈ (([257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ) ++
      ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129] : List ℕ)), r < 2 ^ 14 := by
    decide +kernel
  obtain ⟨C, hm, hs, he⟩ := decode 14 24 _ _ hb hsat
  obtain ⟨k, hk, hk2⟩ := link 14 24 _ _ C (by decide) hb hm hs he
  exact cubes k hk hk2
