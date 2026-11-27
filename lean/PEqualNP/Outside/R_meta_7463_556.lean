import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7463_556
    (noCentreless :
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let D := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        C.size ≤ 21 → 3 ≤ (junk G C).card → 4 ≤ U.card → D < 2 * U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card + D ≤ 6 + U.card) →
        centreless G C = ∅ → 1 ≤ (orN G C \ lam G C).card → 4 ≤ D →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
          ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true) → False)
    (hasCentreless :
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let D := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        C.size ≤ 21 → 3 ≤ (junk G C).card → 4 ≤ U.card → D < 2 * U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card + D ≤ 6 + U.card) →
        1 ≤ (centreless G C).card → 5 ≤ D →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
          ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true) → False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;       x2.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (4 : ℕ) ≤ x5.card → x6 < (2 : ℕ) * x5.card → (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x5) x11 → x11.card + x6 ≤ (6 : ℕ) + x5.card) → False) := by
  classical
  intro G C hleast htop U D hsize hjcard hU4 hdbl hcover
  have hAO : IsAO2 11 C := hleast.1
  have hfun : circuitFun 11 C = graphFun G ∅ := hleast.2.1
  let stepWire : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) i hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  have gateAt_def : ∀ j : ℕ, gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 11 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
        (fun w => (w - 11) :: cs.getD (w - 11) [])] := fun _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate), orStep 11 cs g =
      cs ++ [cs.length :: @ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
        ((g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
          (fun w => cs.getD (w - 11) [])) []] := fun _ _ => rfl
  let _ : DecidableEq GateOp := gateOpDecEq
  have mem_orIn : ∀ (w : ℕ) (i : Fin 11), i ∈ orIn 11 C w ↔ (i : ℕ) = w ∨
      ∃ k < C.gates.length, OrReaches 11 C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs :=
    fun _ _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have opnd_def : ∀ (a : ℕ) (b : Fin 2), opnd C a b = (gateAt C a).inputs.getD b 0 := fun _ _ => rfl
  have pairInput_def : ∀ u v : Fin 11, pairInput u v = fun w => decide (w = u ∨ w = v) :=
    fun _ _ => rfl
  have mem_orN : ∀ j : ℕ, j ∈ orN G C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j :=
    fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
  have mem_tops : ∀ j : ℕ, j ∈ tops G C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ BelowF G C j :=
    fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
  have evA : ∀ l : List Bool, GateOp.eval GateOp.and l = l.all id := fun _ => rfl
  have evO : ∀ l : List Bool, GateOp.eval GateOp.or l = l.any id := fun _ => rfl
  let val : List Bool → ℕ → Bool := fun x u => (C.wires x).getD u false
  have gateAt_eq : ∀ {j : ℕ} (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    simp [gateAt_def, List.getD_eq_getElem?_getD, hj]
  have gateAt_mem : ∀ {j : ℕ}, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    rw [gateAt_eq hj]
    exact List.getElem_mem hj
  have val_input : ∀ {x : List Bool} (_ : x.length = 11) {u : ℕ}, u < 11 →
      val x u = x.getD u false := by
    intro x hx u hu
    change (C.gates.foldl stepWire x).getD u false = x.getD u false
    exact foldl_getD_lt _ _ _ (by omega)
  have val_ge : ∀ {x : List Bool} (_ : x.length = 11) {u : ℕ}, 11 + C.gates.length ≤ u →
      val x u = false := by
    intro x hx u hu
    change (C.gates.foldl stepWire x).getD u false = false
    apply getD_ge
    rw [foldl_len]
    omega
  have val_gate : ∀ {x : List Bool} (_ : x.length = 11) {j : ℕ} (_ : j < C.gates.length),
      val x (11 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < 11 + j then val x i else false) := by
    intro x hx j hj
    change (C.gates.foldl stepWire x).getD (11 + j) false = _
    have h1 := foldl_getD_gate C.gates x j hj
    rw [hx] at h1
    rw [h1, gateAt_eq hj]
    rfl
  have val_and : ∀ {x : List Bool} (_ : x.length = 11) {j : ℕ} (_ : j < C.gates.length),
      (gateAt C j).op = GateOp.and →
      (val x (11 + j) = true ↔ ∀ i ∈ (gateAt C j).inputs, i < 11 + j ∧ val x i = true) := by
    intro x hx j hj hop
    rw [val_gate hx hj, hop]
    simp only [evA, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h i hi
      specialize h i hi
      by_cases hlt : i < 11 + j
      · exact ⟨hlt, by simpa [hlt] using h⟩
      · simp [hlt] at h
    · intro h i hi
      obtain ⟨hlt, hv⟩ := h i hi
      simp [hlt, hv]
  have val_or : ∀ {x : List Bool} (_ : x.length = 11) {j : ℕ} (_ : j < C.gates.length),
      (gateAt C j).op = GateOp.or →
      (val x (11 + j) = true ↔ ∃ i ∈ (gateAt C j).inputs, i < 11 + j ∧ val x i = true) := by
    intro x hx j hj hop
    rw [val_gate hx hj, hop]
    simp only [evO, List.any_eq_true, List.mem_map, id_eq]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩
      by_cases hlt : i < 11 + j
      · exact ⟨i, hi, hlt, by simpa [hlt] using hv⟩
      · simp [hlt] at hv
    · rintro ⟨i, hi, hlt, hv⟩
      exact ⟨true, ⟨i, hi, by simp [hlt, hv]⟩, rfl⟩
  let OrStep : ℕ → ℕ → Prop := fun w w' =>
    ∃ k, k < C.gates.length ∧ w = 11 + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < 11 + k
  have orStep_le : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' → w' ≤ w := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_rfl
    | head hs _ ih =>
      obtain ⟨k, _, rfl, _, _, hlt⟩ := hs
      omega
  have orStep_val : ∀ {x : List Bool} (_ : x.length = 11) {w w' : ℕ},
      Relation.ReflTransGen OrStep w w' → val x w' = true → val x w = true := by
    intro x hx w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro hv; exact hv
    | head hs _ ih =>
      intro hv
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hs
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih hv⟩
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [coneStep_def]
      omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep 11) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
          11 ≤ w ∧ w < 11 + j ∧
          (i = w - 11 ∨ i ∈ (gs.foldl (coneStep 11) []).getD (w - 11) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 11) []).length = gs.length := by
        rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep 11 (gs.foldl (coneStep 11) []) g).getD k [] =
            (gs.foldl (coneStep 11) []).getD k [] := by
        intro k hk
        simp only [coneStep_def, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep 11 (gs.foldl (coneStep 11) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + gs.length))).flatMap
              (fun w => (w - 11) :: (gs.foldl (coneStep 11) []).getD (w - 11) []) := by
          simp only [coneStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 11) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep 11 (gs.foldl (coneStep 11) []) g).getD j [] = [] := by
          simp only [coneStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have inCone_iff : ∀ i j : ℕ, InCone 11 C i j ↔
      j < C.gates.length ∧ ∃ k, k < j ∧ 11 + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone 11 C i k) := by
    intro i j
    have h := cones_char C.gates i j
    unfold InCone cones gateAt
    rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - 11, by omega, ?_, h3⟩
      have : 11 + (w - 11) = w := by omega
      rw [this]
      exact hw
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, 11 + k, hw, by omega, by omega, ?_⟩
      have : 11 + k - 11 = k := by omega
      rw [this]
      exact h3
  have orStep_cone : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
      ∀ k h', w = 11 + k → w' = 11 + h' → h' = k ∨ InCone 11 C h' k := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hs hr ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hs
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hr
      obtain ⟨k1, hk1⟩ : ∃ k1, c = 11 + k1 := ⟨c - 11, by omega⟩
      subst hk1
      right
      rw [inCone_iff]
      exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [orStep_def]
      omega
  have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (orStep 11) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 11 ≤ w ∧ w < 11 + j ∧
            i ∈ (gs.foldl (orStep 11) []).getD (w - 11) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 11) []).length = gs.length := by
        rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep 11 (gs.foldl (orStep 11) []) g).getD k [] =
            (gs.foldl (orStep 11) []).getD k [] := by
        intro k hk
        simp only [orStep_def, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - 11) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - 11) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep 11 (gs.foldl (orStep 11) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + gs.length))).flatMap
                (fun w => (gs.foldl (orStep 11) []).getD (w - 11) []) := by
            simp only [orStep_def, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - 11) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - 11) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep 11 (gs.foldl (orStep 11) []) g).getD gs.length [] = [gs.length] := by
            simp only [orStep_def, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep 11 (gs.foldl (orStep 11) []) g).getD j [] = [] := by
          simp only [orStep_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have orReaches_iff : ∀ k g : ℕ, OrReaches 11 C (11 + k) g ↔
      k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < 11 + k ∧ OrReaches 11 C i g)) := by
    intro k g
    have h := orSets_char C.gates g k
    unfold OrReaches orSets gateAt
    have e : 11 + k - 11 = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
  have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStep w w2 →
      ∀ g, w2 = 11 + g → g < C.gates.length → OrReaches 11 C w g := by
    intro w w2 h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
    | head hs _ ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hs
      exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, _, hin, hlt, ih g h1 hg⟩⟩
  have orReaches_reach : ∀ g w : ℕ, OrReaches 11 C w g →
      Relation.ReflTransGen OrStep w (11 + g) ∧ g < C.gates.length := by
    intro g w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      have hnw : 11 ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
  have mem_orIn_reach : ∀ {p : ℕ} (u : Fin 11), u ∈ orIn 11 C p →
      Relation.ReflTransGen OrStep p u.val := by
    intro p u hu
    rw [mem_orIn] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn : ∀ {p : ℕ} (u : Fin 11), Relation.ReflTransGen OrStep p u.val →
      u ∈ orIn 11 C p := by
    intro p u hr
    rw [mem_orIn]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hs⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hs
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have binaryInputs : ∀ {a : ℕ}, a < C.gates.length → ∃ p q, (gateAt C a).inputs = [p, q] := by
    intro a ha
    exact List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  have opndMem : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b ∈ (gateAt C a).inputs := by
    intro a ha b
    obtain ⟨p, q, hpq⟩ := binaryInputs ha
    fin_cases b <;> simp [opnd_def, hpq]
  have inputsAsOpnd : ∀ {m z : ℕ}, m < C.gates.length → z ∈ (gateAt C m).inputs →
      ∃ b : Fin 2, z = opnd C m b := by
    intro m z hm hz
    obtain ⟨p, q, hpq⟩ := binaryInputs hm
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by simp [opnd_def, hpq]⟩
    · exact ⟨1, by simpa [opnd_def, hpq] using List.mem_singleton.mp hq⟩
  have graphFun_pair : ∀ u v : Fin 11, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    unfold graphFun
    simp only [pairInput_def, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.ne_of_adj hab rfl).elim
      · exact hab
      · exact hab.symm
      · exact (G.ne_of_adj hab rfl).elim
    · intro hab
      exact ⟨u, v, hab, Or.inl rfl, Or.inr rfl⟩
  have trace_wire : ∀ (x : Fin 11 → Bool) (w : ℕ), val (List.ofFn x) w = true →
      (∃ t : Fin 11, x t = true ∧ Relation.ReflTransGen OrStep w t.val) ∨
        ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
          Relation.ReflTransGen OrStep w (11 + j) ∧ gateVal 11 C j x = true := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < 11
      · left
        let t : Fin 11 := ⟨w, hw⟩
        have hx : val (List.ofFn x) w = x t := by
          rw [val_input (by simp) hw, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [t, hw]
        rw [hx] at hv
        exact ⟨t, hv, Relation.ReflTransGen.refl⟩
      · by_cases hlen : w < 11 + C.gates.length
        · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
          have hk : k < C.gates.length := by omega
          rcases hAO.1 _ (gateAt_mem hk) with hand | hor
          · right
            exact ⟨k, hk, hand, Relation.ReflTransGen.refl, hv⟩
          · obtain ⟨i, hi, hlt, hvi⟩ := (val_or (by simp) hk hor).mp hv
            rcases ih i hlt hvi with ⟨t, hxt, hr⟩ | ⟨j, hj, hand, hr, hvj⟩
            · exact Or.inl ⟨t, hxt, Relation.ReflTransGen.head ⟨k, hk, rfl, hor, hi, hlt⟩ hr⟩
            · exact Or.inr ⟨j, hj, hand, Relation.ReflTransGen.head ⟨k, hk, rfl, hor, hi, hlt⟩ hr, hvj⟩
        · have hf := val_ge (x := List.ofFn x) (by simp) (by omega : 11 + C.gates.length ≤ w)
          rw [hf] at hv
          cases hv
  have andRawEmpty : ∀ {j : ℕ}, (gateAt C j).op = GateOp.and → orIn 11 C (11 + j) = ∅ := by
    intro j hj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rw [mem_orIn] at hv
    rcases hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt; omega
    · rcases (orReaches_iff j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
      · subst k; rw [hj] at ho; cases ho
      · rw [hj] at hof; cases hof
  have lastOrBefore : ∀ {j w : ℕ}, Relation.ReflTransGen OrStep w (11 + j) →
      w = 11 + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
        11 + j ∈ (gateAt C m).inputs ∧ 11 + j < 11 + m ∧
        Relation.ReflTransGen OrStep w (11 + m) := by
    intro j w hr
    rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hs⟩
    · exact Or.inl eq.symm
    · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hs
      exact Or.inr ⟨m, hm, ho, hi, hb, hz⟩
  have dirtyOrOutside : ∀ {k m : ℕ}, ¬ BelowF G C k → orIn 11 C (11 + k) = ∅ →
      m < C.gates.length → (gateAt C m).op = GateOp.or →
      11 + k ∈ (gateAt C m).inputs → 11 + k < 11 + m →
      m ∈ orN G C \ lam G C := by
    intro k m hnb hemp hm ho hi hb
    have hNotBelow : ¬ BelowF G C m := by
      intro hbm
      apply hnb
      intro x hxk
      exact hbm x ((val_or (by simp) hm ho).mpr ⟨11 + k, hi, hb, hxk⟩)
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · exact (mem_orN m).mpr (And.intro hm (And.intro ho hNotBelow))
    · intro hl
      have hlam := Finset.mem_filter.mp hl
      obtain ⟨b, hb'⟩ := inputsAsOpnd hm hi
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · have hne := hlam.2.1
        rw [← hb', hemp] at hne
        exact Finset.not_nonempty_empty hne
      · have hne := hlam.2.2.1
        rw [← hb', hemp] at hne
        exact Finset.not_nonempty_empty hne
  have residualTrace : ∀ {u v : Fin 11}, s(u, v) ∈ Ustar G C →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
        Relation.ReflTransGen OrStep (opnd C a b) (11 + j) ∧
        gateVal 11 C j (pairInput u v) = true := by
    intro u v huv
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp huv).1
    have hout : ∀ x : Fin 11 → Bool, val (List.ofFn x) C.output = graphFun G ∅ x :=
      fun x => congrFun hfun x
    have hvout : val (List.ofFn (pairInput u v)) C.output = true := by
      rw [hout, graphFun_pair]
      exact hadj
    obtain ⟨a, ha, hand, hro, hva⟩ : ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        Relation.ReflTransGen OrStep C.output (11 + a) ∧ gateVal 11 C a (pairInput u v) = true := by
      rcases trace_wire (pairInput u v) C.output hvout with ⟨t, hxt, hrt⟩ | h
      · exfalso
        have hfalse : graphFun G ∅ (pairInput t t) = false := by
          cases hf : graphFun G ∅ (pairInput t t)
          · rfl
          · exact (G.ne_of_adj ((graphFun_pair t t).mp hf) rfl).elim
        have htrue : val (List.ofFn (pairInput t t)) C.output = true := by
          apply orStep_val (by simp) hrt
          rw [val_input (by simp) t.isLt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [pairInput_def, t.isLt]
        rw [hout] at htrue
        rw [hfalse] at htrue
        cases htrue
      · exact h
    have hba : BelowF G C a := by
      intro x hx
      rw [← hout x]
      exact orStep_val (by simp) hro hx
    have hatop : a ∈ tops G C := by
      exact (mem_tops a).mpr (And.intro ha (And.intro hand hba))
    have hboth := (val_and (by simp) ha hand).mp hva
    have hv0 : val (List.ofFn (pairInput u v)) (opnd C a 0) = true :=
      (hboth _ (opndMem ha 0)).2
    have hv1 : val (List.ofFn (pairInput u v)) (opnd C a 1) = true :=
      (hboth _ (opndMem ha 1)).2
    have hside : ∀ b : Fin 2,
        (∃ t ∈ side (n := 11) C a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk G C, Relation.ReflTransGen OrStep (opnd C a b) (11 + j) ∧
          gateVal 11 C j (pairInput u v) = true := by
      intro b
      have hvb : val (List.ofFn (pairInput u v)) (opnd C a b) = true := by
        fin_cases b <;> assumption
      rcases trace_wire (pairInput u v) (opnd C a b) hvb with ⟨t, hxt, hrt⟩ | ⟨j, hj, hjand, hrj, hvj⟩
      · left
        refine ⟨t, reach_mem_orIn t hrt, ?_⟩
        simpa [pairInput_def] using hxt
      · right
        have hle := orStep_le hrj
        obtain ⟨k1, hk1⟩ : ∃ k1, opnd C a b = 11 + k1 := ⟨opnd C a b - 11, by omega⟩
        have hlt1 : opnd C a b < 11 + a := hAO.2.1 a ha _ (opndMem ha b)
        have hcone : InCone 11 C j a := by
          rw [inCone_iff]
          exact ⟨ha, k1, by omega, hk1 ▸ opndMem ha b, orStep_cone hrj k1 j hk1 rfl⟩
        have hnb : ¬ BelowF G C j := fun hb => htop j hj a ha hjand hb hand hcone
        have hdirty : ∃ x : Fin 11 → Bool, gateVal 11 C j x = true ∧ graphFun G ∅ x = false := by
          by_contra hne
          apply hnb
          intro x hx
          by_contra hf
          exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
        have hjj : j ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjand, hj, hdirty⟩
        exact ⟨j, hjj, hrj, hvj⟩
    rcases hside 0 with ⟨t0, ht0, htu0⟩ | ⟨j, hj, hrj, hvj⟩
    · rcases hside 1 with ⟨t1, ht1, htu1⟩ | ⟨j, hj, hrj, hvj⟩
      · exfalso
        have hnotstar : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp huv).2
        have hmem_star : s(t0, t1) ∈ starEdges G C := by
          unfold starEdges
          refine Finset.mem_biUnion.mpr ⟨a, hatop, Finset.mem_image.mpr ?_⟩
          exact ⟨(t0, t1), Finset.mem_product.mpr ⟨ht0, ht1⟩, rfl⟩
        have hadj01 : G.Adj t0 t1 := by
          have hv01 : gateVal 11 C a (pairInput t0 t1) = true := by
            apply (val_and (by simp) ha hand).mpr
            intro i hi
            refine ⟨hAO.2.1 a ha i hi, ?_⟩
            obtain ⟨b, rfl⟩ := inputsAsOpnd ha hi
            rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
            · apply orStep_val (by simp) (mem_orIn_reach t0 ht0)
              rw [val_input (by simp) t0.isLt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              simp [pairInput_def, t0.isLt]
            · apply orStep_val (by simp) (mem_orIn_reach t1 ht1)
              rw [val_input (by simp) t1.isLt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
              simp [pairInput_def, t1.isLt]
          exact (graphFun_pair t0 t1).mp (hba _ hv01)
        rcases htu0 with rfl | rfl <;> rcases htu1 with rfl | rfl
        · exact G.ne_of_adj hadj01 rfl
        · exact hnotstar hmem_star
        · exact hnotstar (Sym2.eq_swap ▸ hmem_star)
        · exact G.ne_of_adj hadj01 rfl
      · exact ⟨a, hatop, 1, j, hj, hrj, hvj⟩
    · exact ⟨a, hatop, 0, j, hj, hrj, hvj⟩
  have hcov : ∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
      ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true := by
    intro u v he
    obtain ⟨_, _, _, j, hj, _, hvj⟩ := residualTrace he
    exact ⟨j, hj, hvj⟩
  have hCR : 1 ≤ (centreless G C).card + (orN G C \ lam G C).card := by
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hUne
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, hatop, b, j, hj, hrj, _⟩ := residualTrace he
      have hjand : (gateAt C j).op = GateOp.and := (Finset.mem_filter.mp hj).2.1
      rcases lastOrBefore hrj with hEq | ⟨m, hm, hmo, hmi, hmb, _⟩
      · have hac : a ∈ centreless G C := by
          apply Finset.mem_filter.mpr
          refine ⟨hatop, ?_⟩
          rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
          · left; change orIn 11 C (opnd C a 0) = ∅; rw [hEq]; exact andRawEmpty hjand
          · right; change orIn 11 C (opnd C a 1) = ∅; rw [hEq]; exact andRawEmpty hjand
        have hc1 : 1 ≤ (centreless G C).card := Finset.card_pos.mpr ⟨a, hac⟩
        omega
      · have hnbj : ¬ BelowF G C j := by
          obtain ⟨_, _, _, x, hx1, hx2⟩ := Finset.mem_filter.mp hj
          intro hb
          have := hb x hx1
          rw [hx2] at this
          cases this
        have hm_mem : m ∈ orN G C \ lam G C :=
          dirtyOrOutside hnbj (andRawEmpty hjand) hm hmo hmi hmb
        have hr1 : 1 ≤ (orN G C \ lam G C).card := Finset.card_pos.mpr ⟨m, hm_mem⟩
        omega
  by_cases hEmpty : centreless G C = ∅
  · have hzero : (centreless G C).card = 0 := Finset.card_eq_zero.mpr hEmpty
    have hor : 1 ≤ (orN G C \ lam G C).card := by omega
    have hD4 : 4 ≤ D := by
      change 4 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      omega
    exact noCentreless C hleast htop hsize hjcard hU4 hdbl hcover hEmpty hor hD4 hcov
  · have hpos : 1 ≤ (centreless G C).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    have hD5 : 5 ≤ D := by
      change 5 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      omega
    exact hasCentreless C hleast htop hsize hjcard hU4 hdbl hcover hpos hD5 hcov

