import Mathlib.Algebra.BigOperators.Fin
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

-- Complement inputs using a true sentinel, then count only binary conjunctions.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1896_1
    (dual : ∀ C : Circuit, Monotone2 C → ∃ D : Circuit, Monotone2 D ∧
      Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ∧
      ∀ x : Fin 26 → Bool, circuitFun 27 D (Fin.cases true (fun i => !(x i))) = !(circuitFun 26 C x))
    (compress : ∀ D : Circuit, Monotone2 D →
      (∃ U : Finset (Fin 27), circuitFun 27 D (fun i => decide (i ∈ U)) = false) →
      ∃ A : AndCountCircuit 27, A.WellFormed ∧ A.size ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ∧
        ∀ U : Finset (Fin 27), A.eval U = circuitFun 27 D (fun i => decide (i ∈ U)))
    (bound : ∀ A : AndCountCircuit 27, A.WellFormed →
      let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row := fun (X Y : Finset (Fin 13)) (k : Fin 26) =>
        decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k = Fin.natAdd 13 l)
      let dualRow := fun X Y => Finset.univ.filter
        (fun i : Fin 27 => Fin.cases true (fun k => !(row X Y k)) i = true)
      let miss := fun X : Finset (Fin 13) =>
        Finset.univ.filter (fun l => ∀ p ∈ X, ¬ I p l)
      (∀ p l, I p l → A.eval (dualRow {p} {l}) = false) →
      (∀ X, (∀ p ∉ X, ∃ l ∈ miss X, I p l) →
        (¬ ∃ l, ∀ p ∈ X, I p l) → (¬ ∃ p, ∀ l ∈ miss X, I p l) →
        A.eval (dualRow X (miss X)) = true) → 51 ≤ A.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  classical
  intro C mono pos neg
  obtain ⟨D, hm, hc, hd⟩ := dual C mono
  let mask := fun x : Fin 26 → Bool => Finset.univ.filter
    (fun i : Fin 27 => Fin.cases true (fun k => !(x k)) i = true)
  have liftD (x : Fin 26 → Bool) :
      circuitFun 27 D (fun i => decide (i ∈ mask x)) = !(circuitFun 26 C x) := by
    convert hd x using 2
    funext i
    simp [mask]
  let one := fun k : Fin 26 => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨
    k = Fin.natAdd 13 (0 : Fin 13))
  have hOne : circuitFun 26 C one = true := pos 0 0 (Or.inl rfl)
  obtain ⟨A, wf, ha, he⟩ := compress D hm ⟨mask one, by rw [liftD, hOne]; rfl⟩
  have spec (x : Fin 26 → Bool) : A.eval (mask x) = !(circuitFun 26 C x) :=
    (he _).trans (liftD x)
  apply le_trans _ (le_trans ha hc)
  apply bound A wf
  · intro p l h
    rw [spec]
    simpa using pos p l h
  · intro X closed noline nopencil
    rw [spec]
    simp only [Bool.not_eq_true']
    convert neg X _ ⟨noline, _⟩ using 2
    · funext k
      simp [and_comm]
    · simpa using closed
    · simpa using nopencil
