import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5755_53
    (prep : ∀ (C : Circuit) (xs : List ℕ), xs.length ≤ 2 → Monotone2 C → ReadsBack 27 C → let D : Circuit := ⟨⟨GateOp.or, xs.filter fun i => decide (i<26)⟩ :: C.gates, C.output⟩; Monotone2 D ∧ ReadsBack 26 D ∧ ∀ x : List Bool, x.length = 26 → D.eval x = C.eval (x ++ [xs.any fun i => x.getD i false]))
    (lower : ∀ D : Circuit, Monotone2 D → ReadsBack 26 D → (gateAt D 0).op = GateOp.or → RightOnIncidentPairs singerLines3 D → (∀ X, IsQuadrangle singerLines3 X → D.eval (incidenceInput X (missLines singerLines3 X)) = false) → (∃ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.and ∧ (D.gates.get j).op = GateOp.and ∧ 26+(j.val : ℕ) ∈ (D.gates.get i).inputs) → 64 ≤ D.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size) := by
  intro C xs hxs hm inputBack ds pair anti quad extend hits reject nested
  let D : Circuit := ⟨⟨GateOp.or, xs.filter fun i => decide (i<26)⟩ :: C.gates, C.output⟩
  have back : ReadsBack 27 C := by
    intro j hj i hi
    have eq : gateAt C j = C.gates.get ⟨j,hj⟩ :=
      List.getD_eq_get _ _ ⟨j,hj⟩
    rw [eq] at hi
    exact inputBack ⟨j,hj⟩ i hi
  obtain ⟨dm, db, de⟩ := prep C xs hxs hm back
  have hds : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ ds := by
    change ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13))
    decide +kernel
  have hPair : ∀ p l : Fin 13, incidenceInput {p} {l} = pair p l := by
    change ∀ p l : Fin 13, incidenceInput {p} {l} =
      (List.ofFn fun q : Fin 13 => decide (q=p)) ++ List.ofFn fun t : Fin 13 => decide (t=l)
    decide +kernel
  have len (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ L)).length = 26
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hAnti (X : Finset (Fin 13)) : incidenceInput X (missLines singerLines3 X) = anti X := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 X)) =
      ((List.ofFn fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn fun l : Fin 13 => decide (∀ p ∈ X, p-l ∉ ds))
    apply congrArg (fun suffix : List Bool => (List.ofFn fun p : Fin 13 => decide (p ∈ X)) ++ suffix)
    apply congrArg (fun f : Fin 13 → Bool => List.ofFn f)
    funext l
    have mem : l ∈ missLines singerLines3 X ↔ Disjoint (singerLines3 l) X := by
      change l ∈ Finset.univ.filter (fun l => Disjoint (singerLines3 l) X) ↔ _
      rw [Finset.mem_filter]
      exact and_iff_right (Finset.mem_univ _)
    have e : (l ∈ missLines singerLines3 X) ↔ (∀ p ∈ X, p-l ∉ ds) := by
      rw [mem, Finset.disjoint_left]
      exact ⟨fun h p hp hd => h ((hds p l).mpr hd) hp,
        fun h p hp hx => h p hx ((hds p l).mp hp)⟩
    by_cases hl : l ∈ missLines singerLines3 X
    · exact (decide_eq_true hl).trans (decide_eq_true (e.mp hl)).symm
    · exact (decide_eq_false hl).trans (decide_eq_false (fun h => hl (e.mpr h))).symm
  have hQuad (X : Finset (Fin 13)) (h : IsQuadrangle singerLines3 X) : quad X := by
    refine ⟨h.1,fun l => ?_⟩
    have e : X.filter (fun p => p-l ∈ ds) = X ∩ singerLines3 l := by
      ext p
      rw [Finset.mem_filter,Finset.mem_inter,hds]
    rw [e]
    exact h.2 l
  have hpos : RightOnIncidentPairs singerLines3 D := by
    intro l p hp
    rw [de _ (len _ _), hPair]
    exact hits p l ((hds p l).mp hp)
  have hneg : ∀ X, IsQuadrangle singerLines3 X →
      D.eval (incidenceInput X (missLines singerLines3 X)) = false := by
    intro X q
    rw [de _ (len _ _), hAnti]
    exact reject X (hQuad X q)
  obtain ⟨i,w, hw, oi, _, j, ej, oj⟩ := nested
  let i' : Fin D.gates.length := ⟨i.val+1, by change i.val+1 < C.gates.length + 1; omega⟩
  let j' : Fin D.gates.length := ⟨j.val+1, by change j.val+1 < C.gates.length + 1; omega⟩
  have hnested : ∃ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.and ∧ (D.gates.get j).op = GateOp.and ∧ 26+(j.val : ℕ) ∈ (D.gates.get i).inputs := by
    refine ⟨i',j',?_, ?_, ?_⟩
    · change (C.gates.get i).op = GateOp.and
      exact oi
    · change (C.gates.get j).op = GateOp.and
      exact oj
    · change 26+(j.val+1) ∈ (C.gates.get i).inputs
      have e : 26+(j.val+1)=w := by omega
      rwa [e]
  have hD := lower D dm db (by rfl) hpos hneg hnested
  change 64 ≤ D.gates.length at hD
  change 64 ≤ C.gates.length + 1 at hD
  change 63 ≤ C.gates.length
  omega
