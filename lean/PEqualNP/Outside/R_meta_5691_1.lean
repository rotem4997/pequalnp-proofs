import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_5691_1
    (h_min : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) →
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.MetaComplexity.circuitFun (n + m) C = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (n + m) D ∧
    PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) ∧
    D.size ≤ C.size ∧
    ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (n + m) D' →
      PEqualNP.MetaComplexity.circuitFun (n + m) D' = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
      D.size ≤ D'.size)
    (h_decomp : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (D : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) →
  PEqualNP.TopForm.IsAO2 (n + m) D →
  PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
  (∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (n + m) D' →
    PEqualNP.MetaComplexity.circuitFun (n + m) D' = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
    D.size ≤ D'.size) →
  ∀ x10 < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt D x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < n ∨ ∃ x19 < D.gates.length, x17 = n + m + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, n ≤ x17 ∧ x17 < n + m ∨ ∃ x19 < D.gates.length, x17 = n + m + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ x16) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < x1 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x16 :=
by
  classical
  intro x1 x2 x3 x4 x5 h4 hAO hcomp
  let inc : (Fin (x1 + x2) → Bool) → Bool := fun z =>
    Decidable.decide (∃ a : Fin x1, ∃ b : Fin x2, x3 a b ∧
      z (Fin.castAdd x2 a) = Bool.true ∧ z (Fin.natAdd x1 b) = Bool.true)
  have hcomp' : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = inc := by
    funext z
    exact hcomp z
  obtain ⟨D, hDao, hDcomp, hDle, hDmin⟩ := h_min x1 x2 x3 x5 h4 hAO hcomp'
  have hdec := h_decomp x1 x2 x3 D h4 hDao hDcomp hDmin
  refine ⟨D, hDao, ?_, hDle, hdec⟩
  intro z
  exact congrFun hDcomp z
