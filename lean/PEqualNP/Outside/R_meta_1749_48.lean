import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1749_48
  (prune :
    let d : Finset (Fin 13) := {0,1,3,9}
    let rows := fun (sign : Bool) (x : List Bool) => if sign then
      ∃ i l : Fin 13, i-l ∈ d ∧ x = (List.ofFn (fun a : Fin 13 => decide (a=i))) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
      else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ d)).card ≤ 2) ∧
        x = (List.ofFn (fun a : Fin 13 => decide (a∈Q))) ++ List.ofFn (fun l : Fin 13 => decide (∀ i∈Q, i-l ∉ d))
    let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      ∀ s x, rows s x → C.eval x=s
    let smaller := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∃ D, valid D ∧ D.size < C.size
    let essential := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ j < C.gates.length,
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
      let s := !(g.op.eval [])
      ∀ a∈g.inputs, ∃ x, rows s x ∧ (C.wires x).getD a false = !s ∧ (C.wires x).getD (26+j) false = s
    ∀ C, valid C → smaller C ∨ essential C)
  (core :
    let d : Finset (Fin 13) := {0,1,3,9}
    let rows := fun (sign : Bool) (x : List Bool) => if sign then
      ∃ i l : Fin 13, i-l ∈ d ∧ x = (List.ofFn (fun a : Fin 13 => decide (a=i))) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
      else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ d)).card ≤ 2) ∧
        x = (List.ofFn (fun a : Fin 13 => decide (a∈Q))) ++ List.ofFn (fun l : Fin 13 => decide (∀ i∈Q, i-l ∉ d))
    let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      ∀ s x, rows s x → C.eval x=s
    let smaller := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∃ D, valid D ∧ D.size < C.size
    let essential := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ j < C.gates.length,
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
      let s := !(g.op.eval [])
      ∀ a∈g.inputs, ∃ x, rows s x ∧ (C.wires x).getD a false = !s ∧ (C.wires x).getD (26+j) false = s
    ∀ C, valid C → essential C → C.size < 64 →
      (∃ i j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j) → smaller C) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size := by
  intro d ok nested C mono back good cap pair
  let rows := fun (sign : Bool) (x : List Bool) => if sign then
      ∃ i l : Fin 13, i-l ∈ d ∧ x = (List.ofFn (fun a : Fin 13 => decide (a=i))) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
      else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ d)).card ≤ 2) ∧
        x = (List.ofFn (fun a : Fin 13 => decide (a∈Q))) ++ List.ofFn (fun l : Fin 13 => decide (∀ i∈Q, i-l ∉ d))
  let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      ∀ s x, rows s x → C.eval x=s
  have bridge (A : PEqualNP.CircuitLowerBounds.Circuit) : valid A ↔ PEqualNP.MetaComplexity.Monotone2 A ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 A ∧ ok A := by
    constructor
    · rintro ⟨am,ab,rule⟩
      refine ⟨am,ab,⟨?_,?_⟩⟩
      · intro i l inc
        exact rule true _ ⟨i,l,inc,rfl⟩
      · intro Q card lines
        exact rule false _ ⟨Q,card,lines,rfl⟩
    · rintro ⟨am,ab,pos,neg⟩
      refine ⟨am,ab,?_⟩
      intro s x row
      cases s
      · obtain ⟨Q,card,lines,rfl⟩ := row
        exact neg Q card lines
      · obtain ⟨i,l,inc,rfl⟩ := row
        exact pos i l inc
  have v := (bridge C).mpr ⟨mono,back,good⟩
  have hit : ∃ D, valid D ∧ D.size < C.size := by
    rcases prune C v with hit|keep
    · exact hit
    · exact core C v keep cap pair
  obtain ⟨D,vd,sz⟩ := hit
  obtain ⟨dm,db,dok⟩ := (bridge D).mp vd
  exact ⟨D,dm,db,dok,sz⟩
