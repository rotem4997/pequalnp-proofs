import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Call an AND gate clean when it is false at the zero input and true at a pair input only on an edge.
-- hClean: every AND gate at or below the output gate is clean. hLow and hPair: the first AND gate
-- at or below the output that is not clean is true at an input of weight at most one, or only at a non-edge pair.
theorem PEqualNP.Outside.R_meta_1985_2
    (hClean : ∀ C : Circuit, Monotone2 C → ReadsBack 14 C →
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      (∀ j : ℕ, (gateAt C j).op = GateOp.and → (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
        (gateVal 14 C j (fun _ => false) = false ∧ ∀ u v : Fin 14, gateVal 14 C j (pairInput u v) = true → ((u.val, v.val) ∈ E ∨ (v.val, u.val) ∈ E))) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) →
      27 ≤ C.size)
    (hLow : ∀ (C : Circuit) (j : ℕ), Monotone2 C → ReadsBack 14 C →
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      (gateAt C j).op = GateOp.and → (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
      (∀ i < j, (gateAt C i).op = GateOp.and → (14 + i = C.output ∨ InCone 14 C i (C.output - 14)) → (gateVal 14 C i (fun _ => false) = false ∧ ∀ u v : Fin 14, gateVal 14 C i (pairInput u v) = true → ((u.val, v.val) ∈ E ∨ (v.val, u.val) ∈ E))) →
      (gateVal 14 C j (fun _ => false) = true ∨ ∃ u : Fin 14, gateVal 14 C j (pairInput u u) = true) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) →
      27 ≤ C.size)
    (hPair : ∀ (C : Circuit) (j : ℕ), Monotone2 C → ReadsBack 14 C →
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      (gateAt C j).op = GateOp.and → (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
      (∀ i < j, (gateAt C i).op = GateOp.and → (14 + i = C.output ∨ InCone 14 C i (C.output - 14)) → (gateVal 14 C i (fun _ => false) = false ∧ ∀ u v : Fin 14, gateVal 14 C i (pairInput u v) = true → ((u.val, v.val) ∈ E ∨ (v.val, u.val) ∈ E))) →
      gateVal 14 C j (fun _ => false) = false →
      (∀ u : Fin 14, gateVal 14 C j (pairInput u u) = false) →
      (∃ u v : Fin 14, gateVal 14 C j (pairInput u v) = true ∧ (u.val, v.val) ∉ E ∧ (v.val, u.val) ∉ E) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) →
      27 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  classical
  intro C hM hRB _ hE
  by_cases hclean : ∀ j : ℕ, (gateAt C j).op = GateOp.and → (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
      (gateVal 14 C j (fun _ => false) = false ∧ ∀ u v : Fin 14, gateVal 14 C j (pairInput u v) = true → ((u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∨ (v.val, u.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))))
  · exact hClean C hM hRB hclean hE
  · have hex : ∃ j : ℕ, ¬ ((gateAt C j).op = GateOp.and → (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
        (gateVal 14 C j (fun _ => false) = false ∧ ∀ u v : Fin 14, gateVal 14 C j (pairInput u v) = true → ((u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∨ (v.val, u.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))))) := by
      by_contra hno
      exact hclean (fun j => not_not.mp (fun hj => hno ⟨j, hj⟩))
    have hmin := fun (i : ℕ) (hi : i < Nat.find hex) => not_not.mp (Nat.find_min hex hi)
    have hspec := Nat.find_spec hex
    have hop : (gateAt C (Nat.find hex)).op = GateOp.and := by
      by_contra hne
      exact hspec (fun h => absurd h hne)
    have hio : (14 + (Nat.find hex) = C.output ∨ InCone 14 C (Nat.find hex) (C.output - 14)) := by
      by_contra hne
      exact hspec (fun _ h => absurd h hne)
    have hdirty := fun hc => hspec (fun _ _ => hc)
    by_cases h0 : gateVal 14 C (Nat.find hex) (fun _ => false) = true
    · exact hLow C (Nat.find hex) hM hRB hop hio hmin (Or.inl h0) hE
    · by_cases hs : ∃ u : Fin 14, gateVal 14 C (Nat.find hex) (pairInput u u) = true
      · exact hLow C (Nat.find hex) hM hRB hop hio hmin (Or.inr hs) hE
      · have h0' : gateVal 14 C (Nat.find hex) (fun _ => false) = false := by
          simpa using h0
        have hs' : ∀ u : Fin 14, gateVal 14 C (Nat.find hex) (pairInput u u) = false := by
          intro u
          by_contra hu
          exact hs ⟨u, by simpa using hu⟩
        refine hPair C (Nat.find hex) hM hRB hop hio hmin h0' hs' ?_ hE
        by_contra hnone
        apply hdirty
        refine ⟨h0', ?_⟩
        intro u v huv
        by_contra hbad
        exact hnone ⟨u, v, huv, fun h => hbad (Or.inl h), fun h => hbad (Or.inr h)⟩
