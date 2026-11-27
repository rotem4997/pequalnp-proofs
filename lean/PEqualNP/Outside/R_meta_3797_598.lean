import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.HeptadCover PEqualNP.GenericRejection

-- Lower a wire to false if every required positive sample still passes.
-- Raise an AND to either operand if every required negative sample still passes.
-- The remaining circuits have a test that detects every one of these edits.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3797_598
    (lowerWire : ∀ (n : ℕ) (C : Circuit) (j : ℕ), IsAO2 n C → j < C.size →
      let E : Circuit := ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ x : List Bool, x.length = n → D.eval x = E.eval x ∧ (D.eval x = true → C.eval x = true))
    (raiseWire : ∀ (n : ℕ) (C : Circuit) (j p : ℕ), Monotone2 C → ReadsBack n C →
      j < C.size → (gateAt C j).op = .and → p ∈ (gateAt C j).inputs →
      let D := eraseGate n C j p
      Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ x : List Bool, x.length = n → C.eval x = true → D.eval x = true)
    (noRemaining : let Qs := quadrangles singerLines3
      let sample := fun Q => incidenceInput Q (missLines singerLines3 Q)
      ∀ C : Circuit, IsAO2 26 C → C.size < 64 →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) → 2 ≤ andPairs 26 C →
      (∃ j < C.gates.length, (gateAt C j).op = .and ∧ (readers 26 C j).card ≤ 1) →
      RightOnIncidentPairs singerLines3 C → (∀ Q ∈ Qs, C.eval (sample Q) = false) →
      (∀ j < C.size, ¬ RightOnIncidentPairs singerLines3 ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩) →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ p ∈ (gateAt C j).inputs,
        ∃ Q ∈ Qs, (eraseGate 26 C j p).eval (sample Q) = true) → False) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x12 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.TopForm.readers (26 : ℕ) x4 x12).card ≤ (1 : ℕ)) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x13 ∧ x2 x13 ∧ x13.size < x4.size := by
  intro dif Correct nested C hm hb good small _ strict pairs thin
  classical
  let pos (p l : Fin 13) := incidenceInput {p} {l}
  let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  have pEq (p l : Fin 13) : pos p l =
      (List.ofFn (fun u : Fin 13 => decide (u=p)) ++ List.ofFn (fun v : Fin 13 => decide (v=l))) := by
    change (List.ofFn (fun u : Fin 13 => decide (u∈({p} : Finset (Fin 13)))) ++
      List.ofFn (fun v : Fin 13 => decide (v∈({l} : Finset (Fin 13))))) = _
    simp only [Finset.mem_singleton]
  have inputLength (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change (List.ofFn (fun p : Fin 13 => decide (p∈P)) ++ List.ofFn (fun l : Fin 13 => decide (l∈L))).length = 26
    simp
  have hInc : ∀ p l : Fin 13, p-l ∈ dif ↔ p ∈ singerLines3 l := by
    change ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l
    decide +kernel
  have hQuad (Q : Finset (Fin 13)) : Q ∈ quadrangles singerLines3 ↔
      Q.card=4 ∧ ∀ l : Fin 13, (Q.filter (fun u => u-l ∈ dif)).card≤2 := by
    have swap (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun u => u-l ∈ dif) := by
      ext u
      simp [hInc u l]
    change Q ∈ (Finset.univ.powersetCard 4).filter (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,swap]
  have nEq (Q : Finset (Fin 13)) : neg Q =
      (List.ofFn (fun u : Fin 13 => decide (u∈Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ u∈Q, u-v ∉ dif))) := by
    have tail : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ u∈Q, u-v ∉ dif)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change v ∈ Finset.univ.filter (fun l => Disjoint (singerLines3 l) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,← hInc]
      exact ⟨fun h u hu hInc => h hInc hu, fun h u hu hQ => h u hQ hu⟩
    change List.ofFn (fun u : Fin 13 => decide (u∈Q)) ++ _ = _
    rw [tail]
  let Reject (E : Circuit) := ∀ Q ∈ quadrangles singerLines3, E.eval (neg Q) = false
  have splitTests (E : Circuit) : Correct E ↔ RightOnIncidentPairs singerLines3 E ∧ Reject E := by
    change ((∀ p l : Fin 13, p-l ∈ dif → E.eval
      (List.ofFn (fun u : Fin 13 => decide (u=p)) ++ List.ofFn (fun v : Fin 13 => decide (v=l))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card=4 → (∀ l : Fin 13, (Q.filter (fun u => u-l ∈ dif)).card≤2) →
        E.eval (List.ofFn (fun u : Fin 13 => decide (u∈Q)) ++ List.ofFn (fun v : Fin 13 => decide (∀ u∈Q, u-v∉dif))) = false)) ↔ _
    constructor
    · rintro ⟨on,off⟩
      constructor
      · intro l p hp
        change E.eval (pos p l)=true
        rw [pEq]
        exact on p l ((hInc p l).mpr hp)
      · intro Q hQ
        rw [nEq]
        exact off Q ((hQuad Q).mp hQ).1 ((hQuad Q).mp hQ).2
    · rintro ⟨on,off⟩
      constructor
      · intro p l edge
        rw [← pEq]
        exact on l p ((hInc p l).mp edge)
      · intro Q card line
        rw [← nEq]
        exact off Q ((hQuad Q).mpr ⟨card,line⟩)
  obtain ⟨positive,negative⟩ := (splitTests C).mp good
  have model : IsAO2 26 C := by
    refine ⟨?_,hb,fun g hg => (strict g hg).1⟩
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm g hg).1
  let off (j : ℕ) : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
  by_cases downPossible : ∃ j < C.size, RightOnIncidentPairs singerLines3 (off j)
  · obtain ⟨j,hj,still⟩ := downPossible
    obtain ⟨E,em,eb,smaller,effect⟩ := lowerWire 26 C j model hj
    have ePos : RightOnIncidentPairs singerLines3 E := by
      intro l p e
      rw [(effect _ (inputLength {p} {l})).1]
      exact still l p e
    have eNeg : Reject E := by
      intro Q hQ
      cases bit : E.eval (neg Q) with
      | false => rfl
      | true =>
        have bad := (effect (neg Q) (inputLength Q (missLines singerLines3 Q))).2 bit
        exact Bool.noConfusion ((negative Q hQ).symm.trans bad)
    exact ⟨E,em,eb,(splitTests E).mpr ⟨ePos,eNeg⟩,smaller⟩
  by_cases upPossible : ∃ j < C.size, (gateAt C j).op = .and ∧
      ∃ u ∈ (gateAt C j).inputs, Reject (eraseGate 26 C j u)
  · obtain ⟨j,hj,hop,u,hu,still⟩ := upPossible
    obtain ⟨em,eb,smaller,effect⟩ := raiseWire 26 C j u hm hb hj hop hu
    have ePos : RightOnIncidentPairs singerLines3 (eraseGate 26 C j u) := by
      intro l p ep
      exact effect _ (inputLength {p} {l}) (positive l p ep)
    exact ⟨eraseGate 26 C j u,em,eb,(splitTests _).mpr ⟨ePos,still⟩,smaller⟩
  have blockedDown : ∀ j < C.size, ¬ RightOnIncidentPairs singerLines3 (off j) :=
    fun j hj h => downPossible ⟨j,hj,h⟩
  have blockedUp : ∀ j < C.size, (gateAt C j).op = .and → ∀ u ∈ (gateAt C j).inputs,
      ∃ Q ∈ quadrangles singerLines3, (eraseGate 26 C j u).eval (neg Q) = true := by
    intro j hj hop u hu
    by_contra none
    apply upPossible
    refine ⟨j,hj,hop,u,hu,?_⟩
    intro Q hQ
    cases bit : (eraseGate 26 C j u).eval (neg Q) with
    | false => rfl
    | true => exact (none ⟨Q,hQ,bit⟩).elim
  exact (noRemaining C model small (fun g hg => (strict g hg).2) pairs thin positive negative blockedDown blockedUp).elim
