import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open scoped Classical

theorem PEqualNP.Outside.R_meta_5373_951
    (highCase : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit) (G : SimpleGraph (Fin (n+m))),
      let fit := fun (F : Finset (Fin n × Fin m)) (D : Circuit) =>
        IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide
          (∃ a b, (a,b) ∈ F ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
      let high := ∃ v : Fin (n+m), let d := (G.neighborSet v).ncard
        let R := readers 0 C v.val
        2 ≤ d ∧ (d < R.card ∨ d = R.card ∧
          ∃ r ∈ R, (gateAt C r).op = .and ∧ ¬ readers (n+m) C r ⊆ R)
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
      ¬G.IsAcyclic → fit E C →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      high → ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ fit (E.erase e) D)
    (residual : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit) (G : SimpleGraph (Fin (n+m))),
      let fit := fun (F : Finset (Fin n × Fin m)) (D : Circuit) =>
        IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide
          (∃ a b, (a,b) ∈ F ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
      let high := ∃ v : Fin (n+m), let d := (G.neighborSet v).ncard
        let R := readers 0 C v.val
        2 ≤ d ∧ (d < R.card ∨ d = R.card ∧
          ∃ r ∈ R, (gateAt C r).op = .and ∧ ¬ readers (n+m) C r ⊆ R)
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
      ¬G.IsAcyclic → fit E C →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      M ⊆ E →
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)) →
      (∀ e ∈ E, ((∀ f ∈ E, f.1 = e.1 → f = e) ∨ ∀ f ∈ E, f.2 = e.2 → f = e) →
        (E.erase e).Nonempty → e ∈ M) →
      ¬high → ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ fit (E.erase e) D)
    : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  intro n m E M C G adj cyc square model ev sub rows cols leaf
  by_cases h : ∃ v : Fin (n+m), let d := (G.neighborSet v).ncard
      let R := readers 0 C v.val
      2 ≤ d ∧ (d < R.card ∨ d = R.card ∧
        ∃ r ∈ R, (gateAt C r).op = .and ∧ ¬ readers (n+m) C r ⊆ R)
  · exact highCase n m E M C G adj cyc ⟨model,ev⟩ rows cols h
  · exact residual n m E M C G adj cyc ⟨model,ev⟩ rows cols sub square leaf h
