import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2063_42
  (extract :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let inner := fun (C : Circuit) i => (gateAt C i).op = .and ∧
      ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
    let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
      (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) ∧
      2 ≤ ((incidences S).filter fun e =>
        ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
    ∀ C, valid C → C.size < 64 → ∃ D, valid D ∧ D.size ≤ C.size ∧ hard D)
  (count :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let inner := fun (C : Circuit) i => (gateAt C i).op = .and ∧
      ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
    let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
      (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) ∧
      2 ≤ ((incidences S).filter fun e =>
        ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
    ∀ C, valid C → hard C → 64 ≤ C.size) : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  intro x1 x2 x3 x4 C mono back ok small _ _
  have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ x1 (p-l) = true := by decide +kernel
  have isQ (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ x2 Q := by
    have eq (l : Fin 13) : Q ∩ singerLines3 l = {p ∈ Q | x1 (p-l) = true} := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ singerLines3 l).card ≤ 2) ↔
      (_ ∧ ∀ l, (Q.filter fun p => x1 (p-l) = true).card ≤ 2)
    simp only [eq]
  have rows (Q : Finset (Fin 13)) : incidenceInput Q (missLines singerLines3 Q) = x3 Q := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (singerLines3 w) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right]
    exact forall₂_congr fun p _ => by rw [geom]; simp
  have positive : RightOnIncidentPairs singerLines3 C := by
    intro l p hp
    change C.eval ((List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = true
    simpa only [Finset.mem_singleton] using ok.1 p l ((geom p l).mp hp)
  have negative : ∀ Q, IsQuadrangle singerLines3 Q →
      C.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
    intro Q hQ
    rw [rows]
    exact ok.2 Q ((isQ Q).mp hQ)
  obtain ⟨E,hE,sizeE,hardE⟩ := extract C ⟨mono,back,positive,negative⟩ small
  exact False.elim ((Nat.not_le_of_lt small) ((count E hE hardE).trans sizeE))
