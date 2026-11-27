import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_8949_2
    (h_min : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.MetaComplexity.circuitFun (n + m) C = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ e ∈ E, z (Fin.castAdd m e.1) = Bool.true ∧ z (Fin.natAdd n e.2) = Bool.true)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (n + m) D ∧
    PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ e ∈ E, z (Fin.castAdd m e.1) = Bool.true ∧ z (Fin.natAdd n e.2) = Bool.true)) ∧ D.size ≤ C.size ∧
    ∀ D' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (n + m) D' → PEqualNP.MetaComplexity.circuitFun (n + m) D' = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ e ∈ E, z (Fin.castAdd m e.1) = Bool.true ∧ z (Fin.natAdd n e.2) = Bool.true)) → D.size ≤ D'.size)
    (h_cover : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (D E2 : PEqualNP.CircuitLowerBounds.Circuit),
  E2.size ≤ D.size →
  (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (n + m) D →
  PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ e ∈ E, z (Fin.castAdd m e.1) = Bool.true ∧ z (Fin.natAdd n e.2) = Bool.true)) →
  ¬ (∃ (A : Finset (Fin n × Fin m)) (B : Finset (Fin n × Fin m)) (c : Fin (n + m)), (A.Nonempty ∧ A ∪ B = E ∧ Disjoint (A.biUnion (fun e : Fin n × Fin m => {Fin.castAdd m e.1, Fin.natAdd n e.2})) (B.biUnion (fun e : Fin n × Fin m => {Fin.castAdd m e.1, Fin.natAdd n e.2})) ∧ (∀ e ∈ A, Fin.castAdd m e.1 = c ∨ Fin.natAdd n e.2 = c))) →
  ∃ (U : Finset (Fin n)) (V : Finset (Fin m)),
    (∀ e ∈ E, e.1 ∈ U ∨ e.2 ∈ V) ∧ E.card + U.card + V.card ≤ E2.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → (∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[(1 : ℕ)]? = Option.some x10) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) :=
by
  classical
  intro x1 x2 x3 x4
  dsimp only
  intro h4 hAO hcomp hsep hgate
  let inc : (Fin (x1 + x2) → Bool) → Bool := fun z =>
    Decidable.decide (∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true)
  have hcomp' : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = inc := by
    funext z
    exact hcomp z
  obtain ⟨D, hDao, hDcomp, hDle, hDmin⟩ := h_min x1 x2 x3 x4 h4 hAO hcomp'
  obtain ⟨U, V, hUV, hcard⟩ := h_cover x1 x2 x3 x4 D hDle h4 hAO hcomp' hsep
  exact ⟨U, V, hUV, le_trans hcard (Nat.add_le_add_right hDle 1)⟩
