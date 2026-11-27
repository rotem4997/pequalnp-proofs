import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- A marked formula cannot attain size 27. A circuit with a repeated gate must
-- reuse a signal which no single input or constant can substitute on the boundary.
-- The remaining case asks whether those shared signals can support both marks.
theorem PEqualNP.Outside.R_meta_1967_726
    (formula : ∀ C : Circuit, C.size ≤ 27 →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup →
    let mark := fun (j : ℕ) (v : Fin 14) =>
      (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7) = true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v) = false
    ∀ a b, mark a 0 → ¬ mark b 7)
    (obstruction : ∀ C : Circuit, C.size ≤ 27 →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup →
    ∃ w : ℕ, 14≤w ∧ 2≤(C.output :: C.gates.flatMap Gate.inputs).count w ∧
      ∀ a : Fin 16, ∃ x : Fin 14 → Bool, wireVal 14 C w x = C.eval (List.ofFn x) ∧
        wireVal 14 C w x ≠ (if h : a.val < 14 then x ⟨a.val,h⟩ else decide (a.val=15)))
    (sharedCase : ∀ C : Circuit, C.size ≤ 27 →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    (∃ w : ℕ, 14≤w ∧ 2≤(C.output :: C.gates.flatMap Gate.inputs).count w ∧
      ∀ a : Fin 16, ∃ x : Fin 14 → Bool, wireVal 14 C w x = C.eval (List.ofFn x) ∧
        wireVal 14 C w x ≠ (if h : a.val < 14 then x ⟨a.val,h⟩ else decide (a.val=15))) →
    let mark := fun (j : ℕ) (v : Fin 14) =>
      (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7) = true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v) = false
    ∀ a b, (InCone 14 C a b ∨ InCone 14 C b a) → mark a 0 → ¬ mark b 7) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C,sz,legal,ok,a,b,compare,oa,la,ya,fa,ob,lb,yb,fb⟩
  by_cases tree : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup
  · exact formula C sz legal ok tree a b ⟨oa,la,ya,fa⟩ ⟨ob,lb,yb,fb⟩
  · exact sharedCase C sz legal ok (obstruction C sz legal ok tree) a b compare
      ⟨oa,la,ya,fa⟩ ⟨ob,lb,yb,fb⟩
