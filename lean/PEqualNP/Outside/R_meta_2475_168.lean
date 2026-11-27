import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2475_168
    
(h1 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ q → N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + (1 : ℕ)) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ p l : Fin N, I p l → (PEqualNP.MetaComplexity.circuitFun (N + N) C fun (k : Fin (N + N)) => Decidable.decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = Bool.true) →
        (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = Bool.true} ≤ q →
          (¬∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = Bool.true ∧ z (Fin.natAdd N l) = Bool.true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) C z = Bool.false) →
        N * q ≤ (100 : ℕ) * C.size)

    
(h2 : ∀ q : ℕ, (100 : ℕ) < q → (2 : ℕ) ≤ q)
 :
have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size

  := by
    intro x1def q N I dI C h100 hN hdeg hline hmono hout hord htrue hfalse x16 hsub hdef hsmall
    exact h1 q N I C (h2 q h100) hN hdeg hline hmono htrue hfalse
