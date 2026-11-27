import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- Each row is a bit mask, with vertex zero in the least significant bit.
-- The positive rows are edges. The negative rows are maximal independent sets.
-- Cube k selects the operation and first source of the final gate.
theorem PEqualNP.Outside.R_meta_1985_58
    (encodeSmall : ∀ (C : Circuit) (rows : List ℕ) (label : ℕ → Bool),
      Monotone2 C → NestedCover.ReadsBack 14 C → C.size ≤ 26 →
      (∀ r ∈ rows, r < 16384) →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = label r) →
      ∃ k < enc2CubeCount 14 26, FormulaSat (enc2 14 26 label rows ++ enc2Cube 14 26 k))
    (excludeCubes :
      let positive : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let negative : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      ∀ k < enc2CubeCount 14 26,
        ¬ FormulaSat (enc2 14 26 (fun r => decide (r ∈ positive)) (positive ++ negative) ++
          enc2Cube 14 26 k)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  intro C hmono hback _ hfun
  let positive : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let negative : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
  have bounded : ∀ r ∈ positive ++ negative, r < 16384 := by decide
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  have rowLabels : ∀ r ∈ positive ++ negative,
      (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ r.testBit u.val = true ∧
        r.testBit v.val = true) ↔ r ∈ positive := by decide
  by_contra hsmall
  obtain ⟨k, hk, hs⟩ := encodeSmall C (positive ++ negative)
    (fun r => decide (r ∈ positive)) hmono hback (by omega)
    bounded (fun r hr => Bool.eq_iff_iff.mpr (by
      rw [decide_eq_true_eq]
      exact (hfun (fun i => r.testBit i.val)).trans (rowLabels r hr)))
  exact excludeCubes k hk hs
