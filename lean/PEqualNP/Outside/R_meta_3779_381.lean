import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3779_381
    (earliest : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
  (∃ i, PEqualNP.EdgeOwnership.InCone n C i j ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
  ∃ i < j, PEqualNP.EdgeOwnership.InCone n C i j ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (∀ k, PEqualNP.EdgeOwnership.InCone n C k i →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) ∧
    (∀ k < i, ¬ (PEqualNP.EdgeOwnership.InCone n C k j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and)))
    (repair : ∀ C : Circuit,
      let testQ (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
      let checks (D : Circuit) := Monotone2 D ∧ ReadsBack 26 D ∧
        RightOnIncidentPairs singerLines3 D ∧
        ∀ Q ∈ quadrangles singerLines3, D.eval (testQ Q) = false
      let nested (i j : ℕ) := (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j
      checks C → C.size < 64 →
      (∀ i j, nested i j → ∃ Q ∈ quadrangles singerLines3,
        (C.wires (testQ Q)).getD (26+i) false = true) →
      (∃ i j, i < j ∧ nested i j ∧
        (∀ k, InCone 26 C k i → (gateAt C k).op ≠ .and) ∧
        (∀ k < i, ¬ nested k j)) →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      ∃ D : Circuit, checks D ∧ D.size < C.size) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 → x5.size < (64 : ℕ) → (∀ (x8 x9 : ℕ), x4 x5 x8 x9 → ∃ (x11 : List Bool), x2 Bool.false x11 ∧ (x5.wires x11).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (∃ (x9 : ℕ) (x10 : ℕ), x4 x5 x9 x10) → (∀ x10 ∈ x5.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x3 x11 ∧ x11.size < x5.size := by
  classical
  intro diffSet test good nest C hcorrect hsize hdirty hnested hexact
  let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  let N' (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ diffSet))
  have incident : ∀ p l : Fin 13, p - l ∈ diffSet ↔ p ∈ singerLines3 l := by decide
  have shape (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ diffSet)).card ≤ 2 := by
    have same (k : Fin 13) : Q ∩ singerLines3 k = Q.filter (fun u => u - k ∈ diffSet) := by
      ext u
      simp [incident u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, same]
  have sameInputs (Q : Finset (Fin 13)) : N Q = N' Q := by
    have tailEq : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ diffSet)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← incident]
      constructor
      · intro h r hr hi
        exact h hi hr
      · intro h r hi hr
        exact h r hr hi
    exact congrArg (fun tail : List Bool => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail) tailEq
  have singletons (p l : Fin 13) : incidenceInput {p} {l} =
      List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l)) := by
    change List.ofFn (fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13)))) = _
    simp only [Finset.mem_singleton]
  have posTest (row : List Bool) : test true row ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ row = incidenceInput {p} {l} := by
    change (∃ p l : Fin 13, p-l ∈ diffSet ∧ row =
      (List.ofFn fun u : Fin 13 => decide (u=p)) ++ (List.ofFn fun v : Fin 13 => decide (v=l))) ↔ _
    simp only [incident,singletons]
  have negTest (row : List Bool) : test false row ↔
      ∃ Q ∈ quadrangles singerLines3, row = N Q := by
    change (∃ Q : Finset (Fin 13), Q.card=4 ∧
      (∀ k : Fin 13, (Q.filter (fun u => u-k ∈ diffSet)).card ≤ 2) ∧ row=N' Q) ↔ _
    simp only [shape,sameInputs]
    constructor
    · rintro ⟨Q,hc,hs,he⟩
      exact ⟨Q,⟨hc,hs⟩,he⟩
    · rintro ⟨Q,⟨hc,hs⟩,he⟩
      exact ⟨Q,hc,hs,he⟩
  have both (D : Circuit) : good D ↔
      Monotone2 D ∧ ReadsBack 26 D ∧ RightOnIncidentPairs singerLines3 D ∧
      ∀ Q ∈ quadrangles singerLines3, D.eval (N Q) = false := by
    constructor
    · rintro ⟨mono,back,check⟩
      refine ⟨mono,back,?_,?_⟩
      · intro l p h
        exact check true _ ((posTest _).mpr ⟨p,l,h,rfl⟩)
      · intro Q hQ
        exact check false _ ((negTest _).mpr ⟨Q,hQ,rfl⟩)
    · rintro ⟨mono,back,positives,negatives⟩
      refine ⟨mono,back,?_⟩
      intro b row testRow
      cases b
      · obtain ⟨Q,hQ,rfl⟩ := (negTest _).mp testRow
        exact negatives Q hQ
      · obtain ⟨p,l,edge,rfl⟩ := (posTest _).mp testRow
        exact positives l p edge
  obtain ⟨i,j,hi,hj,cone⟩ := hnested
  obtain ⟨g,glt,gcone,gAnd,lower,first⟩ := earliest 26 C j ⟨i,cone,hi⟩
  have dirty : ∀ i j, nest C i j → ∃ Q ∈ quadrangles singerLines3,
      (C.wires (N Q)).getD (26+i) false = true := by
    intro i j h
    obtain ⟨row,hrow,fire⟩ := hdirty i j h
    obtain ⟨Q,hQ,rfl⟩ := (negTest _).mp hrow
    exact ⟨Q,hQ,fire⟩
  have located : ∃ i j, i < j ∧ nest C i j ∧
      (∀ k, InCone 26 C k i → (gateAt C k).op ≠ .and) ∧
      (∀ k < i, ¬ nest C k j) := by
    refine ⟨g,j,glt,⟨gAnd,hj,gcone⟩,lower,?_⟩
    intro k hk h
    exact first k hk ⟨h.2.2,h.1⟩
  obtain ⟨D,goodD,smaller⟩ := repair C ((both C).mp hcorrect) hsize dirty located hexact
  exact ⟨D,(both D).mpr goodD,smaller⟩
