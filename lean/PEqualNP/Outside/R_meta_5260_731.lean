import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

-- A gate that rejects every negative row covers a star in the incidence graph.
-- Its input disjunctions and the disjunctions leading to the two outputs can be counted together.
theorem PEqualNP.Outside.R_meta_5260_731
  (count : let D : Finset (Fin 13) := {0,1,3,9}
    let F := fun p l : Fin 13 => (List.ofFn fun t : Fin 13 => decide (t=p)) ++ List.ofFn fun t : Fin 13 => decide (t=l)
    let N := fun Q : Finset (Fin 13) => (List.ofFn fun t : Fin 13 => decide (t∈Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ t ∈ Q,t-l ∉ D)
    let quadr := fun Q : Finset (Fin 13) => Q.card=4 ∧ ∀ l : Fin 13,(Q.filter fun t => t-l ∈ D).card ≤ 2
    ∀ (C : Circuit) (w z : Nat),
    let v := fun (i : Nat) (r : List Bool) => (C.wires r).getD i false
    let good := fun (j : Nat) => (gateAt C j).op=.and ∧
      (OrReaches 26 C w j ∨ OrReaches 26 C z j) ∧ ∀ Q, quadr Q → v (26+j) (N Q)=false
    Monotone2 C → ReadsBack 26 C → (¬∃ i j, (gateAt C i).op=.and ∧ (gateAt C j).op=.and ∧ InCone 26 C i j) → (∀ p l, p-l ∈ D → ∃ j, good j ∧ v (26+j) (F p l)=true) → 63 ≤ C.size)
  (remaining : let D : Finset (Fin 13) := {0,1,3,9}
    let F := fun p l : Fin 13 => (List.ofFn fun t : Fin 13 => decide (t=p)) ++ List.ofFn fun t : Fin 13 => decide (t=l)
    let N := fun Q : Finset (Fin 13) => (List.ofFn fun t : Fin 13 => decide (t∈Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ t ∈ Q,t-l ∉ D)
    let quadr := fun Q : Finset (Fin 13) => Q.card=4 ∧ ∀ l : Fin 13,(Q.filter fun t => t-l ∈ D).card ≤ 2
    ∀ (C : Circuit) (w z : Nat),
    let v := fun (i : Nat) (r : List Bool) => (C.wires r).getD i false
    let good := fun (j : Nat) => (gateAt C j).op=.and ∧
      (OrReaches 26 C w j ∨ OrReaches 26 C z j) ∧ ∀ Q, quadr Q → v (26+j) (N Q)=false
    Monotone2 C → ReadsBack 26 C → (¬∃ i j, (gateAt C i).op=.and ∧ (gateAt C j).op=.and ∧ InCone 26 C i j) → C.size < 63 →
      (∀ p l, p-l ∈ D → (v w (F p l) && v z (F p l))=true) →
      (∀ Q, quadr Q → (v w (N Q) && v z (N Q))=false) → (∀ p l, p-l ∈ D → ∃ j, good j ∧ v (26+j) (F p l)=true)) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   (PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9)) → (¬∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11) → (63 : ℕ) ≤ x5.size := by
  intro D F N quadr C w z v h flat
  obtain ⟨legal,back,accept,reject,_⟩ := h
  by_contra! small
  exact (Nat.not_le_of_lt small) (count C w z legal back flat (remaining C w z legal back flat small accept reject))
