import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover
open scoped BigOperators

-- The rectangle budget applies once all flags are covered. The extraction
-- premise asks for coverage only on flags accepted by the selected gates.
theorem PEqualNP.Outside.R_meta_5278_31
    (hGeometry : ∀ R : Finset (Finset (Fin 13) × Finset (Fin 13)),
        R.biUnion (fun r => r.1 ×ˢ r.2) = incidences singerLines3 →
        65 ≤ ∑ r ∈ R, (r.1.card + r.2.card))
    (hExtract :
      let quadInput := fun (Q : Finset (Fin 13)) =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)
      let quads := quadrangles singerLines3
      ∀ (C : Circuit) (K : Finset ℕ),
        let gate := MetaComplexity.NestedCover.gateAt C
        let wire := LowMerge.wireVal C
        TopForm.IsAO2 26 C → 38 ≤ C.size → C.size < 64 →
        8 ≤ ReadTwo.nAnd C ∧ 18 ≤ ReadTwo.nOr C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ TopForm.andPairs 26 C →
        (∀ j < C.size, (gate j).op = GateOp.and →
          ∀ w ∈ (gate j).inputs, ∃ Q ∈ quads, wire (quadInput Q) (26+j) ≠ wire (quadInput Q) w) →
        (∀ j ∈ K, j < C.size ∧ (gate j).op = GateOp.and ∧
          ∀ Q ∈ quads, wire (quadInput Q) (26+j) = false) →
        2 * K.card ≤ C.size + 1 →
        (∀ x : List Bool, x.length = 26 →
          (C.eval x = true ↔ ∃ j ∈ K, wire x (26+j) = true)) →
        ∃ R : Finset (Finset (Fin 13) × Finset (Fin 13)),
          (R.biUnion fun r => r.1 ×ˢ r.2) ⊆ incidences singerLines3 ∧
          (∀ p l : Fin 13, p ∈ singerLines3 l →
            (∃ j ∈ K, wire (LowMerge.pointLineInput 13 13 p l) (26+j) = true) →
            (p,l) ∈ R.biUnion fun r => r.1 ×ˢ r.2) ∧
          (∑ r ∈ R, (r.1.card + r.2.card)) ≤ C.size + 1) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1);
    have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3;
    ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;
      have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →
    (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) →
    (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 →
    (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) →
    (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 →
    (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) →
    (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) →
    (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) →
    (∀ (x16 : List Bool), x16.length = (26 : ℕ) →
    (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) →
    (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  intro quadInput quads C K gate wire hAO hMin hMax hCounts hDistinct hPairs hActive hSilent hBudget hEval hAll
  obtain ⟨R, hSound, hCover, hCost⟩ :=
    hExtract C K hAO hMin hMax hCounts hDistinct hPairs hActive hSilent hBudget hEval
  have hFull : (R.biUnion fun r => r.1 ×ˢ r.2) = incidences singerLines3 := by
    apply Finset.Subset.antisymm hSound
    rintro ⟨p,l⟩ hpl
    have hi : p ∈ singerLines3 l := (Finset.mem_filter.mp hpl).2
    exact hCover p l hi (hAll p l hi)
  have hLower := hGeometry R hFull
  omega
