import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadTwo PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4211_53
    (cleanCase : let clean := fun C : Circuit => ∀ j, isAnd C j → ∀ u v : Fin 26, gateVal 26 C j (pairInput u v) = true → ∃ p l : Fin 13, p ∈ singerLines3 l ∧ ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)); ∀ C : Circuit, Monotone2 C → clean C → RightOnIncidentPairs singerLines3 C → C.eval (List.replicate 13 true ++ List.replicate 13 false) = false → C.eval (List.replicate 13 false ++ List.replicate 13 true) = false → 64 ≤ C.size)
    (dirtyCase : let clean := fun C : Circuit => ∀ j, isAnd C j → ∀ u v : Fin 26, gateVal 26 C j (pairInput u v) = true → ∃ p l : Fin 13, p ∈ singerLines3 l ∧ ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)); ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → ¬ clean C → C.output + 1 = 26 + C.size → C.gates.getLast?.map Gate.op = some GateOp.or → RightOnIncidentPairs singerLines3 C → (∀ m ∈ ([8191,7668,6624,5584,3492,1408,7492,7316,6272,7472,4176,2084,6144,5120,4160,2304,2052,4112,4096,0] : List ℕ), ∀ t : Fin 13, let X : Finset (Fin 13) := Finset.univ.filter (fun p => m.testBit (p-t).val); C.eval (incidenceInput X (missLines singerLines3 X)) = false) → False) :
    (have x1 : Finset (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) (x5 : Fin (26 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (13 : ℕ) x3 ∨ x5 = Fin.natAdd (13 : ℕ) x4); have x4 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : Finset (Fin (13 : ℕ))) (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x6 ∈ x4, x5 = Fin.castAdd (13 : ℕ) x6) ∨ ∃ (x6 : Fin (13 : ℕ)), x5 = Fin.natAdd (13 : ℕ) x6 ∧ ∀ x7 ∈ x4, ¬∃ x9 ∈ x1, x7 = x6 + x9); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Fin (26 : ℕ) → Bool) => (x5.wires (List.ofFn x7)).getD x6 Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x6 →     x6.size ≤ (62 : ℕ) →       ∀ (x9 x10 : Fin ((26 : ℕ) + x6.size)),         x9 ≠ x10 →           (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x3 x12 x13), x5 x6 (↑x10) (x3 x12 x13)] = Bool.true) →             (∀ (x13 : ℕ) (x14 : Fin (13 : ℕ)),                 x13 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →                   have x16 : Finset (Fin (13 : ℕ)) := {x16 : Fin (13 : ℕ) | x13.testBit ↑(x16 - x14) = Bool.true};                   PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x4 x16), x5 x6 (↑x10) (x4 x16)] = Bool.false) →               False) := by
  intro ds incident pairInput' against get C mono budget a b distinct yes no
  let E : Circuit := ⟨C.gates ++ [(⟨GateOp.or, [a.val,b.val]⟩ : Gate)], 26 + C.size⟩
  have sizeE : E.size = C.size + 1 := by
    change (C.gates ++ [(⟨GateOp.or, [a.val,b.val]⟩ : Gate)]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  have monoE : Monotone2 E := by
    intro g hg
    change g ∈ C.gates ++ [(⟨GateOp.or,[a.val,b.val]⟩ : Gate)] at hg
    rcases List.mem_append.mp hg with h | h
    · exact mono g h
    · have h' := List.mem_singleton.mp h
      subst g
      simp
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_nil, List.length_cons]
      omega
  have eEval (x : Fin 26 → Bool) :
      E.eval (List.ofFn x) = GateOp.or.eval [get C a x,get C b x] := by
    have hlen : (C.wires (List.ofFn x)).length = 26 + C.size := by
      change (List.foldl step (List.ofFn x) C.gates).length = _
      rw [len, List.length_ofFn]
      rfl
    change ((C.gates ++ [(⟨GateOp.or,[a.val,b.val]⟩ : Gate)]).foldl step (List.ofFn x)).getD (26+C.size) false = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (C.wires (List.ofFn x) ++ [GateOp.or.eval [get C a x,get C b x]]).getD (26+C.size) false = _
    have last (xs : List Bool) (v : Bool) (n : ℕ) (h : xs.length = n) :
        (xs ++ [v]).getD n false = v := by
      subst n
      simp
    exact last _ _ _ hlen
  have dsEq (p l : Fin 13) : p ∈ singerLines3 l ↔ incident p l := by
    change p ∈ singerLines3 l ↔ ∃ d ∈ ([(0 : Fin 13),1,3,9]).toFinset, p = l+d
    revert p l
    decide +kernel
  have pairList (p l : Fin 13) : List.ofFn (pairInput' p l) = incidenceInput {p} {l} := by
    change List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = incidenceInput {p} {l}
    revert p l
    decide +kernel
  have right : RightOnIncidentPairs singerLines3 E := by
    intro l p hp
    rw [← pairList, eEval]
    exact yes p l ((dsEq p l).mp hp)
  have falseList (X : Finset (Fin 13)) :
      List.ofFn (against X) = incidenceInput X (missLines singerLines3 X) := by
    change List.ofFn (against X) =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 X))
    rw [← List.ofFn_fin_append]
    apply congrArg List.ofFn
    funext i
    refine Fin.addCases (m:=13) (n:=13) (motive := fun j =>
      against X j =
        Fin.append (fun q : Fin 13 => decide (q ∈ X))
          (fun l : Fin 13 => decide (l ∈ missLines singerLines3 X)) j) ?_ ?_ i
    · intro p
      have hs (q : Fin 13) (h : Fin.castAdd 13 p = Fin.castAdd 13 q) : p = q :=
        Fin.castAdd_injective 13 13 h
      rw [Fin.append_left]
      apply Bool.eq_iff_iff.mpr
      dsimp only [against]
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨q,hq,he⟩ | ⟨l,he,_⟩)
        · exact (hs q he).symm ▸ hq
        · have hv := congrArg Fin.val he
          simp at hv
          omega
      · exact fun h => Or.inl ⟨p,h,rfl⟩
    · intro l
      rw [Fin.append_right]
      apply Bool.eq_iff_iff.mpr
      dsimp only [against]
      simp only [decide_eq_true_eq]
      have mem := fun t : Fin 13 =>  Finset.mem_filter (s := (Finset.univ : Finset (Fin 13)))
        (p := fun l => Disjoint (singerLines3 l) X) (a := t)
      constructor
      · rintro (⟨q,_,he⟩ | ⟨t,he,ht⟩)
        · have hv := congrArg Fin.val he
          simp at hv
          omega
        · have hlt : l = t := (Fin.natAddEmb 13).injective he
          subst t
          exact (mem l).mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr (fun p hp hpx => ht p hpx ((dsEq p l).mp hp))⟩
      · intro hd
        have hD : Disjoint (singerLines3 l) X := ((mem l).mp hd).2
        exact Or.inr ⟨l,rfl,fun p hpX hp => Finset.disjoint_left.mp hD ((dsEq p l).mpr hp) hpX⟩
  have samples (m : ℕ) (hm : m ∈ ([8191,7668,6624,5584,3492,1408,7492,7316,6272,7472,4176,2084,6144,5120,4160,2304,2052,4112,4096,0] : List ℕ))
      (t : Fin 13) :
      E.eval (incidenceInput (Finset.univ.filter fun p => m.testBit (p-t).val)
        (missLines singerLines3 (Finset.univ.filter fun p => m.testBit (p-t).val))) = false := by
    rw [← falseList, eEval]
    exact no m t (List.mem_toFinset.mpr hm)
  have allP : E.eval (incidenceInput (Finset.univ : Finset (Fin 13)) (∅ : Finset (Fin 13))) = false := by
    have h : (Finset.univ.filter fun p : Fin 13 => (8191 : ℕ).testBit (p-0).val) = Finset.univ := by decide +kernel
    have h' : missLines singerLines3 (Finset.univ : Finset (Fin 13)) = ∅ := by decide +kernel
    simpa only [h,h'] using samples 8191 (by decide) 0
  have allL : E.eval (incidenceInput (∅ : Finset (Fin 13)) (Finset.univ : Finset (Fin 13))) = false := by
    have h : (Finset.univ.filter fun p : Fin 13 => (0 : ℕ).testBit (p-0).val) = ∅ := by decide +kernel
    have h' : missLines singerLines3 (∅ : Finset (Fin 13)) = Finset.univ := by decide +kernel
    simpa only [h,h'] using samples 0 (by decide) 0
  by_cases hc : ∀ j, isAnd E j → ∀ u v : Fin 26,
      gateVal 26 E j (pairInput u v) = true →
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
           (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l))
  · have rP : E.eval (List.replicate 13 true ++ List.replicate 13 false) = false := by
      have h : incidenceInput (Finset.univ : Finset (Fin 13)) (∅ : Finset (Fin 13)) =
          List.replicate 13 true ++ List.replicate 13 false := by decide +kernel
      rwa [← h]
    have rL : E.eval (List.replicate 13 false ++ List.replicate 13 true) = false := by
      have h : incidenceInput (∅ : Finset (Fin 13)) (Finset.univ : Finset (Fin 13)) =
          List.replicate 13 false ++ List.replicate 13 true := by decide +kernel
      rwa [← h]
    have big := cleanCase E monoE hc right rP rL
    omega
  · exact dirtyCase E monoE (by omega) hc (by change 26+C.size+1 = 26+E.size; omega)
      (by simp [E]) right samples
