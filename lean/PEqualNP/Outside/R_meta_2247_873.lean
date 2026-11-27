import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- In a least circuit each gate accepts an incident pair and differs from every earlier wire on a labeled test.
-- A smaller candidate must also multiply at least two line inputs in an output term.
theorem PEqualNP.Outside.R_meta_2247_873
    (separate : ∀ (T : Bool → List Bool → Prop) (C : Circuit), (∀ s x,T s x → x.length=26) →
      Monotone2 C → ReadsBack 26 C → (∀ s x, T s x → C.eval x=s) →
      (¬∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧ ∀ s x,T s x → D.eval x=s) ∧ D.size<C.size) →
      ∀ j<C.size, ∀ a≤26+j, ∃ s x, T s x ∧ (C.wires x).getD (26+j) false=s ∧ (if a=26+j then false else (C.wires x).getD a false)= !s)
    (linear : let d : Finset (Fin 13) := {0,1,3,9}
      let T := fun (s : Bool) (x : List Bool) => if s then
        ∃ p l : Fin 13, p-l∈d ∧ x=List.ofFn (fun a : Fin 13 => decide (a=p)) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
        else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun p => p-l∈d)).card≤2) ∧
          x=List.ofFn (fun p : Fin 13 => decide (p∈Q)) ++ List.ofFn (fun l : Fin 13 => decide (∀ p∈Q,p-l∉d))
      ∀ C : Circuit, Monotone2 C → (∀ s x, T s x → C.eval x=s) → HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64≤C.size)
    (core : let d : Finset (Fin 13) := {0,1,3,9}
      let T := fun (s : Bool) (x : List Bool) => if s then
        ∃ p l : Fin 13, p-l∈d ∧ x=List.ofFn (fun a : Fin 13 => decide (a=p)) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
        else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun p => p-l∈d)).card≤2) ∧
          x=List.ofFn (fun p : Fin 13 => decide (p∈Q)) ++ List.ofFn (fun l : Fin 13 => decide (∀ p∈Q,p-l∉d))
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → (∀ s x, T s x → C.eval x=s) → (2≤C.lineDeg 26 (Finset.Ico 13 26)) →
      (∀ j<C.size, ∀ a≤26+j, ∃ s x, T s x ∧ (C.wires x).getD (26+j) false=s ∧ (if a=26+j then false else (C.wires x).getD a false)= !s) → (∃ i j, (gateAt C i).op=.and ∧ (gateAt C j).op=.and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j) → 64≤C.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → x6.size < (64 : ℕ) → (∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x10 x11) → x4 x6 := by
  intro d T valid smaller _ C fit _ tiny nested
  by_contra least
  have hlen : ∀ s x, T s x → x.length=26 := by
    intro s x h
    cases s
    · obtain ⟨Q,_,_,rfl⟩ := h
      simp
    · obtain ⟨p,l,_,rfl⟩ := h
      simp
  have distinguish := separate T C hlen fit.1 fit.2.1 fit.2.2 least
  by_cases deg : HasLineDegree 26 (Finset.Ico 13 26) C 1
  · exact (Nat.not_le_of_lt tiny) (linear C fit.1 fit.2.2 deg)
  · change ¬C.lineDeg 26 (Finset.Ico 13 26) ≤ 1 at deg
    exact (Nat.not_le_of_lt tiny) (core C fit.1 fit.2.1 fit.2.2 (by omega) distinguish nested)
