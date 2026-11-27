import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- Rotate the point and line coordinates together in the two seven-bit blocks.
-- The three positive representatives generate all incident pairs. The seven
-- negative representatives generate all maximal inputs with no incidence.
theorem PEqualNP.Outside.R_meta_4693_3
    (tests : ∀ C : Circuit, (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let row := fun (r k : ℕ) (i : Fin 14) =>
        r.testBit (i.val / 7 * 7 + (i.val % 7 + k) % 7);
      ∀ k < 7, (∀ r ∈ [129, 130, 136], C.eval (List.ofFn (row r k)) = true) ∧
        (∀ r ∈ [127, 244, 480, 720, 1188, 3008, 16256], C.eval (List.ofFn (row r k)) = false))
    (rigidity : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (let row := fun (r k : ℕ) (i : Fin 14) =>
        r.testBit (i.val / 7 * 7 + (i.val % 7 + k) % 7);
      ∀ k < 7, (∀ r ∈ [129, 130, 136], C.eval (List.ofFn (row r k)) = true) ∧
        (∀ r ∈ [127, 244, 480, 720, 1188, 3008, 16256], C.eval (List.ofFn (row r k)) = false)) →
      let v := fun j (p l : Fin 14) => gateVal 14 C j (pairInput p l)
      let below := InCone 14 C
      let marked := fun (p : Fin 14) j =>
        (gateAt C j).op = .and ∧ (14+j = C.output ∨ below j (C.output-14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput p p) = false
      ∀ i j, i ≠ j → ¬ below i j → ¬ below j i → marked 0 i → marked 7 j →
        v i 7 7 = false ∧ v j 0 0 = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →           have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);           have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;           have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;           have x9 : Fin (14 : ℕ) → ℕ → Prop := fun (x9 : Fin (14 : ℕ)) (x10 : ℕ) => x7 x10 ∧ ((14 : ℕ) + x10 = x1.output ∨ x8 x10 (x1.output - (14 : ℕ))) ∧ x6 x10 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x11) (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.false;           ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬x8 x10 x11 → ¬x8 x11 x10 → x9 (0 : Fin (14 : ℕ)) x10 → x9 (7 : Fin (14 : ℕ)) x11 → (∃ (x17 : ℕ), x7 x17 ∧ (x8 x10 x17 ∧ x6 x10 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∨ x8 x11 x17 ∧ x6 x11 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false)) → False := by
  intro C size shape distinct incidence
  dsimp only
  intro i j different left right hi hj loss
  obtain ⟨atLine, atPoint⟩ := rigidity C size shape distinct (tests C incidence) i j
    different left right hi hj
  obtain ⟨k, _, first | second⟩ := loss
  · exact Bool.noConfusion (atLine.symm.trans first.2.1)
  · exact Bool.noConfusion (atPoint.symm.trans second.2.1)
