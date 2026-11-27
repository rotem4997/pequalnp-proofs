import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2097_1
    (h1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 17 C ∧ C.size ≤ 23 ∧
      (∀ m ∈ ([33, 513, 16385, 65537, 34, 66, 1026, 32770, 68, 132, 2052, 65540, 40, 136, 264, 4104, 80, 272, 528, 8208] : List ℕ), PEqualNP.MetaComplexity.circuitFun 17 C (fun i => m.testBit i.val) = true) ∧
      (∀ m ∈ ([31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455, 8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040] : List ℕ), PEqualNP.MetaComplexity.circuitFun 17 C (fun i => m.testBit i.val) = false))
    (h2 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (m : ℕ) (x : Fin n → Bool), (∀ i, x i = true → m.testBit i.val = true) →
      PEqualNP.MetaComplexity.circuitFun n C (fun i => m.testBit i.val) = false →
      PEqualNP.MetaComplexity.circuitFun n C x = false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x1 ∧       x1.size ≤ (23 : ℕ) ∧         (have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x3 : Fin (17 : ℕ) → Fin (26 : ℕ) := fun (x3 : Fin (17 : ℕ)) => Fin.ofNat (26 : ℕ) (if ↑x3 < (5 : ℕ) then ↑x3 else if ↑x3 < (14 : ℕ) then ↑x3 + (8 : ℕ) else ↑x3 + (9 : ℕ));           ∀ (x4 x5 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → (∃ x7 ∈ x2, x4 = x5 + x7) → (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x8 : Fin (17 : ℕ)) => Decidable.decide (x3 x8 = Fin.castAdd (13 : ℕ) x4 ∨ x3 x8 = Fin.natAdd (13 : ℕ) x5)) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];                   (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x3;                 have x4 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x3;                 (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x3;                 (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x4;               have x5 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x4;               (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x5,             ∀ (x4 : Fin (17 : ℕ) → Bool), (∀ (x5 : Fin (17 : ℕ)), x4 x5 = Bool.true → x2.testBit ↑x5 = Bool.true) → PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 x4 = Bool.false := by
  obtain ⟨C, hmono, hback, hsize, hpos, hneg⟩ := h1
  refine ⟨C, hmono, hback, hsize, ?_, ?_⟩
  · let D : Finset (Fin 13) := {0, 1, 3, 9}
    let embed (i : Fin 17) : Fin 26 := Fin.ofNat 26 (if i.val < 5 then i.val else if i.val < 14 then i.val + 8 else i.val + 9)
    let mask (p l : Fin 13) : ℕ := 2 ^ p.val + 2 ^ (if l.val < 9 then l.val + 5 else l.val + 4)
    have table : ∀ p l : Fin 13, p.val < 5 → (∃ d ∈ D, p = l + d) →
        mask p l ∈ ([33, 513, 16385, 65537, 34, 66, 1026, 32770, 68, 132, 2052, 65540, 40, 136, 264, 4104, 80, 272, 528, 8208] : List ℕ) ∧
        ∀ i : Fin 17, decide (embed i = Fin.castAdd 13 p ∨ embed i = Fin.natAdd 13 l) = (mask p l).testBit i.val := by
      decide +revert
    dsimp only
    intro p l hp he
    obtain ⟨hm, hbits⟩ := table p l hp he
    exact (congrArg (PEqualNP.MetaComplexity.circuitFun 17 C) (funext hbits)).trans (hpos _ hm)
  · intro m hm x hx
    exact h2 17 C hmono m x hx (hneg m hm)
