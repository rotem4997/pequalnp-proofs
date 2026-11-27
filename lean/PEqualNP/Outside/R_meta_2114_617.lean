import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2114_617
    (hperm : ∀ (n : ℕ) (C : Circuit) (s : Equiv.Perm (Fin n)),
      ∃ (D : Circuit) (q : Fin C.size ≃ Fin D.size),
        D.size = C.size ∧
        (IsMinimalCircuit n C -> IsMinimalCircuit n D) ∧
        (∀ x : Fin n -> Bool, circuitFun n D x = circuitFun n C (x ∘ s)) ∧
        ∀ i : Fin C.size,
          let g := C.gates.get i
          let g' := D.gates.get (q i)
          g'.op = g.op ∧ g'.inputs.length = g.inputs.length ∧
          (g.inputs.Nodup -> g'.inputs.Nodup) ∧
          ((∀ w ∈ g.inputs, w < n + i.val) -> ∀ w ∈ g'.inputs, w < n + (q i).val) ∧
          (∀ v : Fin n, (s v).val ∈ g'.inputs ↔ v.val ∈ g.inputs))

    (hbudget :
      let f (x : Fin 9 -> Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let r (C : Circuit) : Finset (Fin C.size) := {i : Fin C.size | 4 ∈ (C.gates.get i).inputs}
      ∀ C : Circuit, FanInTwo C -> circuitFun 9 C = f ->
        (r C).card = 2 ->
        (∀ i : Fin C.size, let g := C.gates.get i
          4 ∈ g.inputs -> g.op = GateOp.or ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
            ∀ w ∈ g.inputs, w < 9 + i.val) ->
        15 ≤ C.size)
    (hfixed :
      let f (x : Fin 9 -> Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let r (C : Circuit) (v : Fin 9) : Finset (Fin C.size) :=
        {i : Fin C.size | v.val ∈ (C.gates.get i).inputs}
      ∀ C : Circuit, IsMinimalCircuit 9 C -> C.size = 15 -> circuitFun 9 C = f ->
        (∀ i : Fin C.size, let g := C.gates.get i
          (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
            (g.op = GateOp.not ∧ g.inputs.length = 1∨
              g.op ≠ GateOp.not ∧ g.inputs.length = 2)) ->
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or) ->
        (r C 4).card = 2 -> False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  classical
  dsimp only
  intro C hC hOr hDouble

  let f (x : Fin 9 -> Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let lows : List (Fin 9) := [4, 6, 7]
  let r (D : Circuit) (v : Fin 9) : Finset (Fin D.size) :=
    {i : Fin D.size | v.val ∈ (D.gates.get i).inputs}
  let clean (D : Circuit) := ∀ i : Fin D.size, let g := D.gates.get i
    (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
      (g.op = GateOp.not ∧ g.inputs.length = 1 ∨
        g.op ≠ GateOp.not ∧ g.inputs.length = 2)
  obtain ⟨v, hv, hvTwo⟩ := hDouble
  change v ∈ lows at hv
  change (r C v).card = 2 at hvTwo
  have hCclean : clean C := hC.2.2.2.1
  have hCfun : circuitFun 9 C = f := hC.2.2.1
  let rot : Equiv.Perm (Fin 9) :=
    ⟨![1, 2, 3, 8, 6, 0, 7, 4, 5], ![5, 0, 1, 2, 7, 8, 4, 6, 3],
      by intro i; fin_cases i <;> decide, by intro i; fin_cases i <;> decide⟩

  have hrotF (x : Fin 9 -> Bool) : f (x ∘ rot) = f x := by
    change (x 1 && x 2 || x 2 && x 3 || x 3 && x 8 || x 8 && x 6 || x 6 && x 1 ||
      x 1 && x 0 || x 2 && x 7 || x 3 && x 4 || x 8 && x 5 || x 0 && x 4 ||
      x 7 && x 5 || x 5 && x 0) = _
    unfold f
    ac_rfl
  have hrotL (u : Fin 9) : rot u ∈ lows ↔ u ∈ lows := by
    fin_cases u <;> decide
  have hchoose : ∃ s : Equiv.Perm (Fin 9), s v = 4 ∧
      (∀ u, s u ∈ lows ↔ u ∈ lows) ∧ (∀ x, f (x ∘ s) = f x) := by
    change v ∈ ([4, 6, 7] : List (Fin 9)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · subst v
      exact ⟨Equiv.refl _, rfl, fun _ => Iff.rfl, fun _ => rfl⟩
    · subst v
      refine ⟨rot.trans rot, by decide, fun u => (hrotL (rot u)).trans (hrotL u), ?_⟩
      intro x
      change f ((x ∘ rot) ∘ rot) = f x
      rw [hrotF, hrotF]
    · subst v
      exact ⟨rot, by decide, hrotL, hrotF⟩

  obtain ⟨s, hsv, hsL, hsF⟩ := hchoose
  obtain ⟨D, q, hsize, hmin, hfun, hgate⟩ := hperm 9 C s
  have hDmin := hmin hC.1
  have hDfun : circuitFun 9 D = f := by
    funext x
    rw [hfun, hCfun, hsF]
  have hDclean : clean D := by
    intro j
    obtain ⟨i, rfl⟩ := q.surjective j
    obtain ⟨hap, hlen, hnd, hback, _⟩ := hgate i
    obtain ⟨hi, hin, hkind⟩ := hCclean i
    refine ⟨hback hi, hnd hin, ?_⟩
    simpa only [hap, hlen] using hkind
  have hmap (u : Fin 9) : (r C u).map q.toEmbedding = r D (s u) := by
    ext j
    obtain ⟨i, rfl⟩ := q.surjective j
    change q.toEmbedding i ∈ (r C u).map q.toEmbedding ↔ q i ∈ r D (s u)
    rw [Finset.mem_map']
    simp [r, (hgate i).2.2.2.2 u]
  have hDtwo : (r D 4).card = 2 := by
    rw [← hsv, ← hmap, Finset.card_map, hvTwo]

  have hDr (u : Fin 9) (hu : u ∈ lows) :
      (r D u).Nonempty ∧ (r D u).card ≤ 2 ∧ ∀ j ∈ r D u, (D.gates.get j).op = GateOp.or := by
    let w := s.symm u
    have hsw : s w = u := s.apply_symm_apply u
    have hw : w ∈ lows := (hsL w).mp (hsw.symm ▸ hu)
    have hCcount : (r C w).Nonempty ∧ (r C w).card ≤ 2 :=
      ⟨(hC.2.2.2.2 w hw).1, (hC.2.2.2.2 w hw).2.1⟩
    rw [← hsw, ← hmap]
    refine ⟨hCcount.1.map, by simpa only [Finset.card_map] using hCcount.2, ?_⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact (hgate i).1.trans (hOr w hw i hi)
  have hDsize : D.size = 15 := by
    apply Nat.le_antisymm (hsize.trans_le hC.2.1)
    refine hbudget D hDmin.1 hDfun hDtwo ?_
    intro j
    dsimp only
    intro hj
    have hjr : j ∈ r D 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hop := (hDr 4 (by decide)).2.2 j hjr
    obtain ⟨hback, hnd, hk⟩ := hDclean j
    refine ⟨hop, ?_, hnd, hback⟩
    rcases hk with hk | hk
    · rw [hop] at hk
      exact (GateOp.noConfusion hk.1)
    · exact hk.2
  exact hfixed D hDmin hDsize hDfun hDclean hDr hDtwo
