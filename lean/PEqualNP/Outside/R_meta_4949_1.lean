import Mathlib.Data.Set.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4949_1
    (h1 : ∀ (X Y : Finset (Fin 13)),
      PEqualNP.GenericRejection.IsMaximalFalse (fun l : Fin 13 => {l, l + 1, l + 3, l + 9}) X Y →
      PEqualNP.GenericRejection.IsGeneric (fun l : Fin 13 => {l, l + 1, l + 3, l + 9}) 3 X Y →
      ∃ m ∈ ([7, 13, 19, 21, 25, 29, 35, 37, 39, 41, 67, 69, 71, 73, 77, 81, 83, 85, 97, 101, 105, 131, 133, 135, 137, 141, 195, 201, 265, 273, 275, 281, 297, 329, 337, 549] : List ℕ),
        ∃ k : Fin 13,
          (∀ p : Fin 13, p ∈ X ↔ m.testBit ↑(p - k) = Bool.true) ∧
          ∀ l : Fin 13, l ∈ Y ↔ ∀ p ∈ X, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9))
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ A : PEqualNP.AndCount.AndCountCircuit 27,
        A.WellFormed ∧
        A.size ≤ {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧
        ∀ x : Fin 26 → Bool,
          A.eval (Finset.univ.filter fun i : Fin 27 => Fin.cases true (fun k => !(x k)) i = true) =
            !(PEqualNP.MetaComplexity.circuitFun 26 C x))
    (h3 : ∀ (A : PEqualNP.AndCount.AndCountCircuit 27),
      A.WellFormed →
      (∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
        A.eval (Finset.univ.filter fun i : Fin 27 =>
          Fin.cases true (fun k : Fin 26 => !decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) i = true) = false) →
      (∀ X Y : Finset (Fin 13),
        PEqualNP.GenericRejection.IsMaximalFalse (fun l : Fin 13 => {l, l + 1, l + 3, l + 9}) X Y →
        PEqualNP.GenericRejection.IsGeneric (fun l : Fin 13 => {l, l + 1, l + 3, l + 9}) 3 X Y →
        A.eval (Finset.univ.filter fun i : Fin 27 =>
          Fin.cases true (fun k : Fin 26 => !decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k = Fin.natAdd 13 l)) i = true) = true) →
      51 ≤ A.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) →       (∀ (x4 : ℕ) (x5 : Fin (13 : ℕ)),           (x4 ∈               have x6 : List ℕ :=                 have x6 : List ℕ :=                   have x6 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];                   (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x6;                 have x7 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x6;                 (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x7;               have x7 : List ℕ :=                 have x7 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x6;                 (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x7;               have x8 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x7;               (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x8) →             have x7 : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | x4.testBit ↑(x7 - x5) = Bool.true};             (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ ∀ x10 ∈ x7, ¬(x10 = x9 ∨ x10 = x9 + (1 : Fin (13 : ℕ)) ∨ x10 = x9 + (3 : Fin (13 : ℕ)) ∨ x10 = x9 + (9 : Fin (13 : ℕ))))) = Bool.false) →         (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hmono hpos hneg
  obtain ⟨A, hwf, hsize, heval⟩ := h2 C hmono
  refine le_trans (h3 A hwf ?_ ?_) hsize
  · intro p l hpl
    let x : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)
    have hf : (Finset.univ.filter fun i : Fin 27 =>
        Fin.cases true (fun k : Fin 26 => !decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) i = true) =
        (Finset.univ.filter fun i : Fin 27 => Fin.cases true (fun k => !(x k)) i = true) := by
      ext i; rfl
    rw [hf, heval x]
    have hp : PEqualNP.MetaComplexity.circuitFun 26 C x = true := hpos p l hpl
    rw [hp]
    rfl
  · intro X Y hmax hgen
    obtain ⟨m, hm, k, hX, hY⟩ := h1 X Y hmax hgen
    let x : Fin 26 → Bool := fun k_1 => decide ((∃ p ∈ X, k_1 = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k_1 = Fin.natAdd 13 l)
    have hf : (Finset.univ.filter fun i : Fin 27 =>
        Fin.cases true (fun k_1 : Fin 26 => !decide ((∃ p ∈ X, k_1 = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k_1 = Fin.natAdd 13 l)) i = true) =
        (Finset.univ.filter fun i : Fin 27 => Fin.cases true (fun k_1 => !(x k_1)) i = true) := by
      ext i; rfl
    rw [hf, heval x]
    have hn := hneg m k hm
    dsimp only at hn
    have heq : x = (fun x8 : Fin (13 + 13) => decide ((∃ x9 ∈ ({x7 : Fin 13 | m.testBit ↑(x7 - k) = true} : Finset (Fin 13)), x8 = Fin.castAdd 13 x9) ∨ ∃ x9 : Fin 13, x8 = Fin.natAdd 13 x9 ∧ ∀ x10 ∈ ({x7 : Fin 13 | m.testBit ↑(x7 - k) = true} : Finset (Fin 13)), ¬(x10 = x9 ∨ x10 = x9 + 1 ∨ x10 = x9 + 3 ∨ x10 = x9 + 9))) := by
      funext x8
      apply decide_eq_decide.mpr
      have hmem : ∀ p : Fin 13, p ∈ ({x7 : Fin 13 | m.testBit ↑(x7 - k) = true} : Finset (Fin 13)) ↔ p ∈ X := by
        intro p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hX p]
      refine or_congr (exists_congr fun p => and_congr (hmem p).symm Iff.rfl) (exists_congr fun l => ?_)
      rw [hY l, and_comm]
      exact and_congr Iff.rfl (forall_congr' fun p => imp_congr_left (hmem p).symm)
    have hx0 : PEqualNP.MetaComplexity.circuitFun 26 C x = false := by
      change PEqualNP.MetaComplexity.circuitFun (13 + 13) C x = false
      rw [heq]
      exact hn
    rw [hx0]
    rfl
