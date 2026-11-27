import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The first child counts positive flags lost when a nested predecessor is clamped
-- false. Its proof uses single-flag replacement and the L-meta-2061 cone surgery.
theorem PEqualNP.Outside.R_meta_5164_202
 (count : let S := singerLines3
  let ok := fun (C : Circuit) => Monotone2 C ∧ ReadsBack 26 C ∧
    (∀p l : Fin 13,p∈S l → C.eval (incidenceInput {p} {l})=true) ∧
    ∀Q : Finset (Fin 13), IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q))=false
  let J := andPairs 26
  ∀ C : Circuit,ok C → (∀D,ok D → C.size≤D.size) → (∀D,ok D → D.size=C.size → J C≤J D) →
∀ i j : ℕ,(gateAt C i).op=GateOp.and → (gateAt C j).op=GateOp.and → InCone 26 C i j → let D : Circuit := ⟨C.gates.set i ⟨GateOp.or,[]⟩,C.output⟩
    2≤((incidences S).filter fun e=>D.eval (incidenceInput {e.1} {e.2})=false).card)
 (residual : let S := singerLines3
  let ok := fun (C : Circuit) => Monotone2 C ∧ ReadsBack 26 C ∧
    (∀p l : Fin 13,p∈S l → C.eval (incidenceInput {p} {l})=true) ∧
    ∀Q : Finset (Fin 13), IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q))=false
  let J := andPairs 26
  ∀ C : Circuit,ok C → (∀D,ok D → C.size≤D.size) → (∀D,ok D → D.size=C.size → J C≤J D) →
2≤J C → (∀ i j : ℕ,(gateAt C i).op=GateOp.and → (gateAt C j).op=GateOp.and → InCone 26 C i j → (∃ Q : Finset (Fin 13),IsQuadrangle S Q ∧ (C.wires (incidenceInput Q (missLines S Q))).getD (26+i) false=true) ∧ let D : Circuit := ⟨C.gates.set i ⟨GateOp.or,[]⟩,C.output⟩
    2≤((incidences S).filter fun e=>D.eval (incidenceInput {e.1} {e.2})=false).card) → 64≤C.size) :
have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x6.size = x3.size → PEqualNP.TopForm.andPairs (26 : ℕ) x3 ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x6) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ (x8 x9 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x8 x9 → ∃ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 ∧ (x3.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (64 : ℕ) ≤ x3.size := by
  dsimp only
  intro C ok sm ap many stains
  let OK := fun (D : Circuit) => Monotone2 D ∧ ReadsBack 26 D ∧
    (∀p l : Fin 13,p∈singerLines3 l → D.eval (incidenceInput {p} {l})=true) ∧
    ∀Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q))=false
  have pos (p l : Fin 13) : incidenceInput {p} {l} =
      (List.ofFn fun u : Fin 13=>decide (u=p))++List.ofFn fun u : Fin 13=>decide (u=l) := by
    change (List.ofFn fun u : Fin 13=>decide (u∈({p} : Finset (Fin 13))))++
      List.ofFn (fun u : Fin 13=>decide (u∈({l} : Finset (Fin 13))))=_
    simp only [Finset.mem_singleton]
  have nc : OK C := ⟨ok.1,ok.2.1,fun p l h=>by rw [pos];exact ok.2.2.1 p l h,ok.2.2.2⟩
  have ms : ∀D,OK D → C.size≤D.size := by
    intro D d
    exact sm D ⟨d.1,d.2.1,fun p l h=>by rw [←pos];exact d.2.2.1 p l h,d.2.2.2⟩
  have ma : ∀D,OK D → D.size=C.size → andPairs 26 C≤andPairs 26 D := by
    intro D d
    exact ap D ⟨d.1,d.2.1,fun p l h=>by rw [←pos];exact d.2.2.1 p l h,d.2.2.2⟩
  apply residual C nc ms ma many
  intro i j hi hj con
  exact ⟨stains i j hi hj con,count C nc ms ma i j hi hj con⟩
