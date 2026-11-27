import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2008_2
    
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
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size

  := by
    intro q N I dI C h100 hN hdeg hline hmono hout hord htrue hfalse x15 hcross hsmall
    exact h1 q N I C (h2 q h100) hN hdeg hline hmono htrue hfalse
