import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.TopForm

-- A maximal negative is determined by its point bits, so the circuit search
-- only needs the incidence pairs and the closed rows on thirteen point bits.
theorem PEqualNP.Outside.R_meta_2608_1
    (maximalRows :
      let E (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let Z (y : Fin 13 → Bool) (l : Fin 13) := !(y l || y (l + 1) || y (l + 3) || y (l + 9))
      let hit (x : Fin 26 → Bool) :=
        ∃ p l, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ x, Maximal (fun z => ¬ hit z) x →
        ∃ y : Fin 13 → Bool, x = Fin.append y (Z y) ∧
          ∀ p, y p = false → ∃ l, E p l ∧ Z y l = true)
    (certificate :
      let E (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let Z (y : Fin 13 → Bool) (l : Fin 13) := !(y l || y (l + 1) || y (l + 3) || y (l + 9))
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ 64 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 26 + j ∧
        C.gates[j]? = some ⟨GateOp.and, [a, b]⟩ ∧
        (∀ p l, E p l →
          let x (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          wireValue C 26 x a = true ∧ wireValue C 26 x b = true) ∧
        ∀ y : Fin 13 → Bool, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
          wireValue C 26 (Fin.append y (Z y)) (if Z y 0 = true then a else b) = false) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  obtain ⟨C, j, a, b, size, model, distinct, output, finalGate, positives, closed⟩ := certificate
  refine ⟨C, j, a, b, size, model, distinct, output, finalGate, positives, ?_⟩
  intro x maximal
  obtain ⟨y, rfl, closure⟩ := maximalRows x maximal
  have lineZero : (13 : Fin 26) = Fin.natAdd 13 (0 : Fin 13) := by decide
  simpa only [lineZero, Fin.append_right] using closed y closure
