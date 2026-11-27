import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection

-- Nine OR gates must be false on each maximal independent row of size four.
-- The first child uses the remaining true OR gates to bound which input vertices can be identified.
theorem PEqualNP.Outside.R_meta_4691_12
    (count : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      12 ≤ ((Finset.range C.size).filter fun j => (gateAt C j).op.eval [false,true]).card)
    (remaining : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      ComputesIncidence fanoLines C → 12 ≤ ((Finset.range C.size).filter fun j => (gateAt C j).op.eval [false,true]).card →
      let v (j : ℕ) (x y : Fin 14) := gateVal 14 C j (pairInput x y)
      let a (j : ℕ) := (gateAt C j).op = GateOp.and
      let c := InCone 14 C
      let r (x : Fin 14) (j : ℕ) :=
        a j ∧ (14 + j = C.output ∨ c j (C.output - 14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput x x) = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j →
      (∃ k m, a k ∧ a m ∧ c k i ∧ c m j ∧
        v i 7 7 = false ∧ v j 0 0 = false ∧ v k 0 7 = true ∧ v m 0 7 = true ∧
        v k 0 0 = false ∧ v k 7 7 = false ∧ v m 0 0 = false ∧ v m 7 7 = false) → False) :
    ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let v (j : ℕ) (x y : Fin 14) := gateVal 14 C j (pairInput x y)
      let a (j : ℕ) := (gateAt C j).op = GateOp.and
      let c := InCone 14 C
      let r (x : Fin 14) (j : ℕ) :=
        a j ∧ (14 + j = C.output ∨ c j (C.output - 14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput x x) = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j →
      (∃ k m, a k ∧ a m ∧ c k i ∧ c m j ∧
        v i 7 7 = false ∧ v j 0 0 = false ∧ v k 0 7 = true ∧ v m 0 7 = true ∧
        v k 0 0 = false ∧ v k 7 7 = false ∧ v m 0 0 = false ∧ v m 7 7 = false) → False := by
  intro C size mono distinct correct
  have flags : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by decide
  have same : ComputesIncidence fanoLines C := by
    intro P L
    let plane := Fin.append (fun p : Fin 7 => decide (p ∈ P)) (fun l : Fin 7 => decide (l ∈ L))
    have input : List.ofFn plane = incidenceInput P L := List.ofFn_fin_append ..
    rw [←input]
    apply Bool.eq_iff_iff.mpr
    rw [correct plane]
    change _ ↔ decide (∃ p ∈ P, ∃ l ∈ L, p ∈ fanoLines l) = true
    rw [decide_eq_true_eq]
    simp only [plane,Fin.append_left,Fin.append_right,decide_eq_true_eq,flags]
    constructor
    · rintro ⟨p,l,inc,pt,ln⟩
      exact ⟨p,pt,l,ln,inc⟩
    · rintro ⟨p,pt,l,ln,inc⟩
      exact ⟨p,l,inc,pt,ln⟩
  exact remaining C size mono distinct same (count C size mono correct)
