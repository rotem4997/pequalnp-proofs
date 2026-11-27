import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.MetaComplexity PEqualNP.HeptadCover

-- Reconstruct the lines from the point-line pairs accepted by the circuit.
-- The search now asks whether every minimal true input is one such pair.
theorem PEqualNP.Outside.R_meta_4604_316
    (classify : ∀ (n : ℕ) (C : Circuit), IsAO2 (n+n) C →
      (∀ X Y : Finset (Fin n), C.eval (incidenceInput X Y) = true →
        (∀ p ∈ X, C.eval (incidenceInput (X.erase p) Y) = false) →
        (∀ l ∈ Y, C.eval (incidenceInput X (Y.erase l)) = false) →
        X.card = 1 ∧ Y.card = 1) →
      let S := fun l : Fin n => Finset.univ.filter fun p : Fin n =>
        C.eval (incidenceInput {p} {l}) = true
      ComputesIncidence S C)
    (search : ∃ (n : ℕ) (C : Circuit),
      let S := fun l : Fin n => Finset.univ.filter fun p : Fin n =>
        C.eval (incidenceInput {p} {l}) = true
      (∀ i, i ∈ S i) ∧ (∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1) ∧ IsAO2 (n+n) C ∧
      (∀ X Y : Finset (Fin n), C.eval (incidenceInput X Y) = true →
        (∀ p ∈ X, C.eval (incidenceInput (X.erase p) Y) = false) →
        (∀ l ∈ Y, C.eval (incidenceInput X (Y.erase l)) = false) →
        X.card = 1 ∧ Y.card = 1) ∧ C.size + 1 < (incidences S).card + n) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ (∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x5 ∈ x2 x6 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true)) ∧ x3.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x2).card + x1 := by
  obtain ⟨n,C,diagonal,linear,model,minterms,small⟩ := search
  let S := fun l : Fin n => Finset.univ.filter fun p : Fin n =>
    C.eval (incidenceInput {p} {l}) = true
  have correct : ComputesIncidence S C := classify n C model minterms
  refine ⟨n,S,C,diagonal,linear,model,?_,small⟩
  intro z
  let X := Finset.univ.filter fun p : Fin n => z (Fin.castAdd n p) = true
  let Y := Finset.univ.filter fun l : Fin n => z (Fin.natAdd n l) = true
  have split : Fin.append (fun p : Fin n => decide (p ∈ X))
      (fun l : Fin n => decide (l ∈ Y)) = z := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro p
      rw [Fin.append_left]
      cases h : z (Fin.castAdd n p) <;> simp [X,h]
    · intro l
      rw [Fin.append_right]
      cases h : z (Fin.natAdd n l) <;> simp only [Y,Finset.mem_filter,Finset.mem_univ,true_and,h] <;> rfl
  have row : incidenceInput X Y = List.ofFn z := by
    change List.ofFn (fun p : Fin n => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin n => decide (l ∈ Y)) = _
    rw [← List.ofFn_fin_append, split]
  change C.eval (List.ofFn z) = _
  rw [← row, correct X Y]
  apply Bool.eq_iff_iff.mpr
  change decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ S l) = true ↔ _
  simp only [decide_eq_true_eq, X, Y, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p,hp,l,hl,h⟩
    exact ⟨p,l,h,hp,hl⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨p,hp,l,hl,h⟩
