import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4043_4
    (normalize : let H := SimpleGraph.fromRel (fun (a b : Fin 26) => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ [0,1,3,9]); ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → ∃ D : Circuit, IsLeastAO (H.deleteIncidenceSet x2) D ∧ TopForm (H.deleteIncidenceSet x2) D ∧ D.size ≤ x1.size)
    (small : let H := SimpleGraph.fromRel (fun (a b : Fin 26) => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ [0,1,3,9]); ∀ (v : Fin 26) (D : Circuit),
      IsLeastAO (H.deleteIncidenceSet v) D → TopForm (H.deleteIncidenceSet v) D →
      (Ustar (H.deleteIncidenceSet v) D).card ≤ 5 → 58 ≤ D.size)
    (large : let H := SimpleGraph.fromRel (fun (a b : Fin 26) => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ [0,1,3,9]); ∀ (v : Fin 26) (D : Circuit),
      IsLeastAO (H.deleteIncidenceSet v) D → TopForm (H.deleteIncidenceSet v) D →
      6 ≤ (Ustar (H.deleteIncidenceSet v) D).card → 58 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  classical
  intro C v mono correct
  obtain ⟨D,hLeast,hTop,hsize⟩ := normalize C v mono correct
  let H : SimpleGraph (Fin 26) := SimpleGraph.fromRel (fun (a b : Fin 26) => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ [0,1,3,9])
  by_cases h : (Ustar (H.deleteIncidenceSet v) D).card ≤ 5
  · have lower := small v D hLeast hTop h
    omega
  · have h6 : 6 ≤ (Ustar (H.deleteIncidenceSet v) D).card := by omega
    have lower := large v D hLeast hTop h6
    omega
