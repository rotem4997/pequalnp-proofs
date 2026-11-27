import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4147_1
  (pointStar :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let isAnd := fun (C : Circuit) i => (gateAt C i).op = .and
    let inner := fun C i => isAnd C i ∧ ∃ j, isAnd C j ∧ InCone 26 C i j
    let K := fun (C : Circuit) i => (incidences S).filter fun e =>
      ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
    ∀ C, valid C →
      (∀ j, inner C j → (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+j) false = true) ∧
        2 ≤ (K C j).card) →
      ∀ i, inner C i → (∀ j, InCone 26 C j i → ¬ isAnd C j) →
      (∃ p, ∀ e ∈ K C i, e.1 = p) → 64 ≤ C.size)
  (lineStar :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let isAnd := fun (C : Circuit) i => (gateAt C i).op = .and
    let inner := fun C i => isAnd C i ∧ ∃ j, isAnd C j ∧ InCone 26 C i j
    let K := fun (C : Circuit) i => (incidences S).filter fun e =>
      ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
    ∀ C, valid C →
      (∀ j, inner C j → (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+j) false = true) ∧
        2 ≤ (K C j).card) →
      ∀ i, inner C i → (∀ j, InCone 26 C j i → ¬ isAnd C j) →
      (∃ l, ∀ e ∈ K C i, e.2 = l) → 64 ≤ C.size)
  (crossed :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let isAnd := fun (C : Circuit) i => (gateAt C i).op = .and
    let inner := fun C i => isAnd C i ∧ ∃ j, isAnd C j ∧ InCone 26 C i j
    let K := fun (C : Circuit) i => (incidences S).filter fun e =>
      ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
    ∀ C, valid C →
      (∀ j, inner C j → (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+j) false = true) ∧
        2 ≤ (K C j).card) →
      ∀ i, inner C i → (∀ j, InCone 26 C j i → ¬ isAnd C j) →
      (∃ e ∈ K C i, ∃ f ∈ K C i, e.1 ≠ f.1 ∧ e.2 ≠ f.2 ∧
        (e.1 ∈ S f.2 ∨ f.1 ∈ S e.2)) → 64 ≤ C.size)
  (uncrossed :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let isAnd := fun (C : Circuit) i => (gateAt C i).op = .and
    let inner := fun C i => isAnd C i ∧ ∃ j, isAnd C j ∧ InCone 26 C i j
    let K := fun (C : Circuit) i => (incidences S).filter fun e =>
      ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
    ∀ C, valid C →
      (∀ j, inner C j → (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+j) false = true) ∧
        2 ≤ (K C j).card) →
      ∀ i, inner C i → (∀ j, InCone 26 C j i → ¬ isAnd C j) →
      (∃ e ∈ K C i, ∃ f ∈ K C i, e.1 ≠ f.1 ∧ e.2 ≠ f.2 ∧
        e.1 ∉ S f.2 ∧ f.1 ∉ S e.2) → 64 ≤ C.size) :
  have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → (64 : ℕ) ≤ x6.size := by
  intro S row valid inner hard C hv hh
  let K := fun (D : Circuit) j => (incidences S).filter fun e =>
    ({D with gates := D.gates.set j ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
  have coneEarlier (n : ℕ) (C : Circuit) (i j : ℕ) :
      PEqualNP.EdgeOwnership.InCone n C i j → i < j := by
    let entry := fun (cs : List (List ℕ)) (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])
    let step := fun (cs : List (List ℕ)) (g : Gate) => cs ++ [entry cs g]
    have validAppend (cs : List (List ℕ)) (g : Gate)
        (hc : ∀ j i, i ∈ cs.getD j [] → i < j) :
        ∀ j i, i ∈ (step cs g).getD j [] → i < j := by
      intro j i hi
      change i ∈ (cs ++ [entry cs g]).getD j [] at hi
      rcases lt_trichotomy j cs.length with hj | rfl | hj
      · rw [List.getD_append _ _ _ _ hj] at hi
        exact hc j i hi
      · have hlast : (cs ++ [entry cs g]).getD cs.length [] = entry cs g := by simp
        rw [hlast] at hi
        change i ∈ (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) []) at hi
        obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hi
        have hwire : n ≤ w ∧ w < n + cs.length := of_decide_eq_true (List.mem_filter.mp hw).2
        have hidx : w - n < cs.length := by omega
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hidx
        · exact (hc (w - n) i hi).trans hidx
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        simp at hi
    have validFold (gs : List Gate) (cs : List (List ℕ))
        (hc : ∀ j i, i ∈ cs.getD j [] → i < j) :
        ∀ j i, i ∈ (gs.foldl step cs).getD j [] → i < j := by
      induction gs generalizing cs with
      | nil => exact hc
      | cons g gs ih => exact ih (step cs g) (validAppend cs g hc)
    intro hi
    change i ∈ (C.gates.foldl step []).getD j [] at hi
    exact validFold C.gates [] (by simp) j i hi
  have criticalShape (E : Finset (Fin 13 × Fin 13)) (h : 2 ≤ E.card) :
      (∃ p : Fin 13, ∀ e ∈ E, e.1 = p) ∨
      (∃ l : Fin 13, ∀ e ∈ E, e.2 = l) ∨
      ∃ e ∈ E, ∃ f ∈ E, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
    classical
    by_cases crossed : ∃ e ∈ E, ∃ f ∈ E, e.1 ≠ f.1 ∧ e.2 ≠ f.2
    · exact Or.inr (Or.inr crossed)
    obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
    have share (x y : Fin 13 × Fin 13) (hx : x ∈ E) (hy : y ∈ E)
        (hs : x.2 ≠ y.2) : x.1 = y.1 := by
      by_contra hd
      exact crossed ⟨x, hx, y, hy, hd, hs⟩
    by_cases different : ∃ f ∈ E, f.1 ≠ e.1
    · obtain ⟨f, hf, hfe⟩ := different
      have hfs : f.2 = e.2 := by
        by_contra hne
        exact hfe (share f e hf he hne)
      refine Or.inr (Or.inl ⟨e.2, fun g hg => ?_⟩)
      by_contra hgs
      have hge := share g e hg he hgs
      have hgf := share g f hg hf (by simpa only [hfs] using hgs)
      exact hfe (hgf.symm.trans hge)
    · refine Or.inl ⟨e.1, fun g hg => ?_⟩
      by_contra hgf
      exact different ⟨g, hg, hgf⟩
  classical
  obtain ⟨existsInner, conditions⟩ := hh
  let i := Nat.find existsInner
  have hi : inner C i := Nat.find_spec existsInner
  have first : ∀ j, InCone 26 C j i → (gateAt C j).op ≠ .and := by
    intro j hj hand
    exact Nat.find_min existsInner (coneEarlier 26 C j i hj) ⟨hand, i, hi.1, hj⟩
  have enough : 2 ≤ (K C i).card := (conditions i hi).2
  rcases criticalShape (K C i) enough with point | line | ⟨e, he, f, hf, hpoint, hline⟩
  · exact pointStar C hv conditions i hi first point
  · exact lineStar C hv conditions i hi first line
  · by_cases cross : e.1 ∈ S f.2 ∨ f.1 ∈ S e.2
    · exact crossed C hv conditions i hi first ⟨e, he, f, hf, hpoint, hline, cross⟩
    · exact uncrossed C hv conditions i hi first
        ⟨e, he, f, hf, hpoint, hline, fun h => cross (Or.inl h), fun h => cross (Or.inr h)⟩
