import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_8069_2
    (pureMixing :
      let G := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let R := orN G C \ lam G C
        let M := mixing G C
        centreless G C = ∅ → 2 ≤ J.card → 1 ≤ M.card → M ⊆ R →
        4 ≤ U.card → J.card + R.card < U.card →
        (∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ InCone 11 C a b) →
        (∀ u v : Fin 11, s(u, v) ∈ U →
          ∃ t ∈ tops G C, ∃ b : Fin 2, ∃ m ∈ M, ∃ j ∈ J,
            OrReaches 11 C (opnd C t b) m ∧ OrReaches 11 C (opnd C t b) j ∧
            gateVal 11 C j (pairInput u v) = true ∧ gateVal 11 C t (pairInput u v) = true ∧
            (orIn 11 C (opnd C t (1 - b))).Nonempty ∧ side C t (1 - b) ⊆ wmax G C j) → False)
    (pureCentreless :
      let G := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let T0 := centreless G C
        let R := orN G C \ lam G C
        1 ≤ T0.card → 2 ≤ J.card → 5 ≤ U.card →
        2 * T0.card + J.card + R.card < U.card →
        (∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ InCone 11 C a b) →
        (∀ u v : Fin 11, s(u, v) ∈ U →
          ∃ t ∈ T0, gateVal 11 C t (pairInput u v) = true) → False)
    (hybridCover :
      let G := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let T0 := centreless G C
        let R := orN G C \ lam G C
        let M := mixing G C
        1 ≤ T0.card → 2 ≤ J.card → 1 ≤ M.card → M ⊆ R →
        6 ≤ U.card → 2 * T0.card + J.card + R.card < U.card →
        (∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ InCone 11 C a b) →
        (∀ u v : Fin 11, s(u, v) ∈ U →
          (∃ t ∈ T0, gateVal 11 C t (pairInput u v) = true) ∨
          (∃ t ∈ tops G C \ T0, ∃ b : Fin 2, ∃ m ∈ M, ∃ j ∈ J,
            OrReaches 11 C (opnd C t b) m ∧ OrReaches 11 C (opnd C t b) j ∧
            gateVal 11 C j (pairInput u v) = true ∧ gateVal 11 C t (pairInput u v) = true ∧
            side C t (1 - b) ⊆ wmax G C j)) → False) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let _ : DecidableEq GateOp := gateOpDecEq
  intro G C hsz hleast htop hjunk hnested _ hU3 _
  by_contra hlt_not
  have hlt : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
      (Ustar G C).card := by omega
  have hnested' : ∃ a ∈ junk G C, ∃ b ∈ junk G C, a ≠ b ∧ InCone 11 C a b := by
    obtain ⟨a, b, ha, hb, hne, hab | hba⟩ := hnested
    · exact ⟨a, ha, b, hb, hne, hab⟩
    · exact ⟨b, hb, a, ha, hne.symm, hba⟩
  obtain ⟨hao2, hfun, hmin⟩ := hleast
  obtain ⟨hao, hrb, hlen2⟩ := hao2

  -- Helper 1: Wire evaluation without unfolding Circuit.wires / GateOp.eval via simp
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq (x : List Bool) : C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_len (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt' : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt']
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
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
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {x : List Bool} (hx : x.length = 11) {u : ℕ} (hu : u < 11) :
      val x u = x.getD u false := by
    change (C.wires x).getD u false = x.getD u false
    rw [wires_eq]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {x : List Bool} (hx : x.length = 11) {u : ℕ} (hu : 11 + C.gates.length ≤ u) :
      val x u = false := by
    change (C.wires x).getD u false = false
    apply getD_ge; rw [wires_eq, foldl_len]; omega

  have val_gate {x : List Bool} (hx : x.length = 11) {j : ℕ} (hj : j < C.gates.length) :
      val x (11 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < 11 + j then val x i else false) := by
    change (C.wires x).getD (11 + j) false = _
    rw [wires_eq, gateAt_eq hj]
    have key := foldl_getD_gate C.gates x j hj
    rw [hx] at key
    exact key

  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl

  have val_or {x : List Bool} (hx : x.length = 11) {r : ℕ} (hr : r < C.gates.length)
      (hop : (gateAt C r).op = GateOp.or) :
      val x (11 + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < 11 + r ∧ val x i = true := by
    rw [val_gate hx hr, hop]
    simp only [eval_or, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt' : i < 11 + r
      · rw [ite_eq_left hlt'] at h; exact ⟨i, hi, hlt', h⟩
      · rw [ite_eq_right hlt'] at h; cases h
    · rintro ⟨i, hi, hlt', h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt']; exact h⟩

  have val_and {x : List Bool} (hx : x.length = 11) {r : ℕ} (hr : r < C.gates.length)
      (hop : (gateAt C r).op = GateOp.and) :
      val x (11 + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < 11 + r ∧ val x i = true := by
    rw [val_gate hx hr, hop]
    simp only [eval_and, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt' : i < 11 + r
      · rw [ite_eq_left hlt'] at h'; exact ⟨hlt', h'⟩
      · rw [ite_eq_right hlt'] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_ofFn (x : Fin 11 → Bool) (u : Fin 11) : val (List.ofFn x) u.val = x u := by
    rw [val_input (by simp) u.isLt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp

  have gateVal_eq (j : ℕ) (x : Fin 11 → Bool) :
      gateVal 11 C j x = val (List.ofFn x) (11 + j) := rfl

  have out_eq (x : Fin 11 → Bool) : val (List.ofFn x) C.output = graphFun G ∅ x := by
    have h1 := congrFun hfun x
    exact h1

  have inputs_two {j : ℕ} (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hl : (gateAt C j).inputs.length = 2 := hlen2 (gateAt C j) (gateAt_mem hj)
    rcases hs : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · rw [hs] at hl; simp at hl
    · rw [hs] at hl; simp at hl
    · change [a, b] = [((gateAt C j).inputs).getD 0 0, ((gateAt C j).inputs).getD 1 0]
      rw [hs]; rfl
    · rw [hs] at hl; simp at hl

  have opnd_lt {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) : opnd C j b < 11 + j := by
    have hmem : opnd C j b ∈ (gateAt C j).inputs := by
      rw [inputs_two hj]
      fin_cases b <;> simp
    exact hrb j hj (opnd C j b) hmem

  -- Helper 2: OrSets and Cones via custom step functions (no equation lemmas on defs)
  let stepOr (cs : List (List ℕ)) (g : Gate) : List (List ℕ) :=
    cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
        (fun w => cs.getD (w - 11) [])
      else [])]

  have orSets_eq : orSets 11 C = C.gates.foldl stepOr [] := rfl

  have orFold_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl stepOr cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepOr]; omega

  have orFold_getD_lt (gs : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
      (gs.foldl stepOr cs).getD i [] = cs.getD i [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt' : i < (stepOr cs g).length := by simp [stepOr]; omega
      rw [ih (stepOr cs g) hlt']
      simp [stepOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have orFold_getD_gate (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepOr cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if (gs[j]).op = GateOp.or then
          ((gs[j]).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + (cs.length + j)))).flatMap
            (fun w => (gs.foldl stepOr cs).getD (w - 11) [])
          else []) := by
    induction gs generalizing cs j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : cs.length < (stepOr cs g).length := by simp [stepOr]
        rw [Nat.add_zero, orFold_getD_lt gs (stepOr cs g) cs.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepOr cs g).getD cs.length [] =
            cs.length :: (if g.op = GateOp.or then
              (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
                (fun w => cs.getD (w - 11) [])
              else []) := by
          simp [stepOr, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        split_ifs
        · apply List.flatMap_congr
          intro w hw
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          have hlt' : w - 11 < cs.length := by omega
          rw [orFold_getD_lt gs (stepOr cs g) (w - 11) (by simp [stepOr]; omega)]
          simp [stepOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
        · rfl
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepOr cs g) j hj'
        have hl : (stepOr cs g).length = cs.length + 1 := by simp [stepOr]
        rw [hl] at key
        have e : cs.length + (j + 1) = cs.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  have orSets_getD {j : ℕ} (hj : j < C.gates.length) :
      (orSets 11 C).getD j [] =
        j :: (if (gateAt C j).op = GateOp.or then
          ((gateAt C j).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + j))).flatMap
            (fun w => (orSets 11 C).getD (w - 11) [])
          else []) := by
    rw [orSets_eq, gateAt_eq hj]
    have key := orFold_getD_gate C.gates [] j hj
    simpa using key

  have orSets_getD_ge {j : ℕ} (hj : C.gates.length ≤ j) : (orSets 11 C).getD j [] = [] := by
    rw [orSets_eq]
    have hlen : (C.gates.foldl stepOr []).length = C.gates.length := by
      rw [orFold_len]; simp
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl stepOr []).length ≤ j)]

  have orReaches_self {j : ℕ} (hj : j < C.gates.length) : OrReaches 11 C (11 + j) j := by
    refine ⟨by omega, ?_⟩
    have e : 11 + j - 11 = j := by omega
    rw [e, orSets_getD hj]
    simp

  have orReaches_lt_len {w g : ℕ} (h : OrReaches 11 C w g) : w - 11 < C.gates.length := by
    by_contra hge
    have h1 := orSets_getD_ge (by omega : C.gates.length ≤ w - 11)
    have h2 := h.2
    rw [h1] at h2
    simp at h2

  have orReaches_step {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
      {w g : ℕ} (hw : w ∈ (gateAt C k).inputs) (hwlt : w < 11 + k) (h : OrReaches 11 C w g) :
      OrReaches 11 C (11 + k) g := by
    refine ⟨by omega, ?_⟩
    have e : 11 + k - 11 = k := by omega
    rw [e, orSets_getD hk, ite_eq_left hop]
    apply List.mem_cons_of_mem
    rw [List.mem_flatMap]
    exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [h.1, hwlt]⟩, h.2⟩

  have orReaches_iff {k g : ℕ} (hk : k < C.gates.length) :
      OrReaches 11 C (11 + k) g ↔
        g = k ∨ ((gateAt C k).op = GateOp.or ∧
          ∃ w ∈ (gateAt C k).inputs, w < 11 + k ∧ OrReaches 11 C w g) := by
    constructor
    · intro h
      have h2 := h.2
      have e : 11 + k - 11 = k := by omega
      rw [e, orSets_getD hk] at h2
      rcases List.mem_cons.mp h2 with rfl | hmem
      · exact Or.inl rfl
      · by_cases hop : (gateAt C k).op = GateOp.or
        · rw [ite_eq_left hop, List.mem_flatMap] at hmem
          obtain ⟨w, hwf, hwg⟩ := hmem
          simp only [List.mem_filter, decide_eq_true_eq] at hwf
          exact Or.inr ⟨hop, w, hwf.1, hwf.2.2, hwf.2.1, hwg⟩
        · rw [ite_eq_right hop] at hmem; simp at hmem
    · rintro (rfl | ⟨hop, w, hw, hwlt, hwg⟩)
      · exact orReaches_self hk
      · exact orReaches_step hk hop hw hwlt hwg

  have orReaches_trans : ∀ w : ℕ, ∀ k g : ℕ,
      OrReaches 11 C w k → OrReaches 11 C (11 + k) g → OrReaches 11 C w g := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro k g hwk hkg
      have hw11 : 11 ≤ w := hwk.1
      have hwlen : w - 11 < C.gates.length := orReaches_lt_len hwk
      obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases (orReaches_iff hj).mp hwk with rfl | ⟨hop, w', hw', hw'lt, hw'k⟩
      · exact hkg
      · exact orReaches_step hj hop hw' hw'lt (ih w' hw'lt k g hw'k hkg)

  have orReaches_val : ∀ w : ℕ, ∀ g : ℕ, ∀ x : Fin 11 → Bool,
      OrReaches 11 C w g → gateVal 11 C g x = true → val (List.ofFn x) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g x hwg hgv
      have hw11 : 11 ≤ w := hwg.1
      have hwlen : w - 11 < C.gates.length := orReaches_lt_len hwg
      obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases (orReaches_iff hj).mp hwg with rfl | ⟨hop, w', hw', hw'lt, hw'g⟩
      · exact hgv
      · exact (val_or (by simp) hj hop).mpr ⟨w', hw', hw'lt, ih w' hw'lt g x hw'g hgv⟩

  have orReaches_le : ∀ w : ℕ, ∀ g : ℕ, OrReaches 11 C w g → g ≤ w - 11 ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hwg
      have hw11 : 11 ≤ w := hwg.1
      have hwlen : w - 11 < C.gates.length := orReaches_lt_len hwg
      obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases (orReaches_iff hj).mp hwg with rfl | ⟨_, w', _, hw'lt, hw'g⟩
      · exact ⟨by omega, hj⟩
      · obtain ⟨h1, h2⟩ := ih w' hw'lt g hw'g
        exact ⟨by omega, h2⟩

  -- Cones step without unfolding coneStep / cones
  let stepCone (cs : List (List ℕ)) (g : Gate) : List (List ℕ) :=
    cs ++ [(g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
      (fun w => (w - 11) :: cs.getD (w - 11) [])]

  have cones_eq : cones 11 C = C.gates.foldl stepCone [] := rfl

  have coneFold_getD_lt (gs : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
      (gs.foldl stepCone cs).getD i [] = cs.getD i [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt' : i < (stepCone cs g).length := by simp [stepCone]; omega
      rw [ih (stepCone cs g) hlt']
      simp [stepCone, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have coneFold_getD_gate (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepCone cs).getD (cs.length + j) [] =
        ((gs[j]).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + (cs.length + j)))).flatMap
          (fun w => (w - 11) :: (gs.foldl stepCone cs).getD (w - 11) []) := by
    induction gs generalizing cs j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : cs.length < (stepCone cs g).length := by simp [stepCone]
        rw [Nat.add_zero, coneFold_getD_lt gs (stepCone cs g) cs.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepCone cs g).getD cs.length [] =
            (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
              (fun w => (w - 11) :: cs.getD (w - 11) []) := by
          simp [stepCone, List.getD_eq_getElem?_getD]
        rw [h2]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hlt' : w - 11 < cs.length := by omega
        congr 1
        rw [coneFold_getD_lt gs (stepCone cs g) (w - 11) (by simp [stepCone]; omega)]
        simp [stepCone, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepCone cs g) j hj'
        have hl : (stepCone cs g).length = cs.length + 1 := by simp [stepCone]
        rw [hl] at key
        have e : cs.length + (j + 1) = cs.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  have cones_getD {j : ℕ} (hj : j < C.gates.length) :
      (cones 11 C).getD j [] =
        ((gateAt C j).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + j))).flatMap
          (fun w => (w - 11) :: (cones 11 C).getD (w - 11) []) := by
    rw [cones_eq, gateAt_eq hj]
    have key := coneFold_getD_gate C.gates [] j hj
    simpa using key

  have inCone_direct {i j : ℕ} (hj : j < C.gates.length)
      (hmem : 11 + i ∈ (gateAt C j).inputs) (hlt' : i < j) : InCone 11 C i j := by
    change i ∈ (cones 11 C).getD j []
    rw [cones_getD hj, List.mem_flatMap]
    exact ⟨11 + i, List.mem_filter.mpr ⟨hmem, by simp; omega⟩, by simp⟩

  have inCone_step {i k j : ℕ} (hj : j < C.gates.length)
      (hmem : 11 + k ∈ (gateAt C j).inputs) (hlt' : k < j) (hik : InCone 11 C i k) :
      InCone 11 C i j := by
    change i ∈ (cones 11 C).getD j []
    rw [cones_getD hj, List.mem_flatMap]
    refine ⟨11 + k, List.mem_filter.mpr ⟨hmem, by simp; omega⟩, ?_⟩
    apply List.mem_cons_of_mem
    have e : 11 + k - 11 = k := by omega
    rw [e]
    exact hik

  have orReaches_inCone : ∀ w : ℕ, ∀ g : ℕ, OrReaches 11 C w g →
      ∀ j < C.gates.length, w ∈ (gateAt C j).inputs → w < 11 + j → InCone 11 C g j := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hwg j hj hmem hwlt
      have hw11 : 11 ≤ w := hwg.1
      have hwlen : w - 11 < C.gates.length := orReaches_lt_len hwg
      obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkj : k < j := by omega
      rcases (orReaches_iff hk).mp hwg with rfl | ⟨_, w', hw', hw'lt, hw'g⟩
      · exact inCone_direct hj hmem hkj
      · exact inCone_step hj hmem hkj (ih w' hw'lt g hw'g k hk hw' hw'lt)

  -- Helper 3: OR-tracing a true wire at input x reaches either an input i with x i = true
  -- (so i ∈ orIn 11 C w) or an AND gate j with OrReaches 11 C w j and gateVal j x = true!
  have or_trace_val : ∀ w : ℕ, ∀ x : Fin 11 → Bool, val (List.ofFn x) w = true →
      (∃ i : Fin 11, i ∈ orIn 11 C w ∧ x i = true) ∨
      (∃ j < C.gates.length, OrReaches 11 C w j ∧ (gateAt C j).op = GateOp.and ∧
        gateVal 11 C j x = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro x hv
      by_cases hw : w < 11
      · refine Or.inl ⟨⟨w, hw⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
        · have := val_ofFn x ⟨w, hw⟩; rw [← this]; exact hv
      · by_cases hlen : 11 + C.gates.length ≤ w
        · rw [val_ge (by simp) hlen] at hv; cases hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
          have hk : k < C.gates.length := by omega
          rcases hao (gateAt C k) (gateAt_mem hk) with hand | hor
          · exact Or.inr ⟨k, hk, orReaches_self hk, hand, hv⟩
          · obtain ⟨w', hw', hw'lt, hv'⟩ := (val_or (by simp) hk hor).mp hv
            rcases ih w' hw'lt x hv' with ⟨i, hi, hxi⟩ | ⟨j, hj, hrj, hand, hgj⟩
            · refine Or.inl ⟨i, ?_, hxi⟩
              obtain ⟨_, hi'⟩ := Finset.mem_filter.mp hi
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
              rcases hi' with heq | ⟨m, hm, hrm, horm, him⟩
              · exact ⟨k, hk, orReaches_self hk, hor, heq ▸ hw'⟩
              · exact ⟨m, hm, orReaches_step hk hor hw' hw'lt hrm, horm, him⟩
            · exact Or.inr ⟨j, hj, orReaches_step hk hor hw' hw'lt hrj, hand, hgj⟩

  -- Helper 4: orIn monotonicity: if i ∈ orIn 11 C w and x i = true, then val (List.ofFn x) w = true
  have orIn_val {w : ℕ} {i : Fin 11} (hi : i ∈ orIn 11 C w) {x : Fin 11 → Bool} (hxi : x i = true) :
      val (List.ofFn x) w = true := by
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hi
    rcases hcase with heq | ⟨k, hk, hrk, hork, hik⟩
    · rw [← heq, val_ofFn]; exact hxi
    · have hkv : gateVal 11 C k x = true := by
        rw [gateVal_eq]
        exact (val_or (by simp) hk hork).mpr ⟨i.val, hik, by omega, by rw [val_ofFn]; exact hxi⟩
      exact orReaches_val w k x hrk hkv

  -- Helper 5: graphFun at single vertex is false; at an edge s(u,v) is true
  have graphFun_single (u : Fin 11) : graphFun G ∅ (pairInput u u) = false := by
    by_contra h
    have htrue : graphFun G ∅ (pairInput u u) = true := by
      cases hgf : graphFun G ∅ (pairInput u u)
      · exact absurd hgf h
      · rfl
    change decide (∃ a b : Fin 11, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true) = true at htrue
    rw [decide_eq_true_eq] at htrue
    obtain ⟨a, b, hab, ha, hb⟩ := htrue
    change decide (a = u ∨ a = u) = true at ha
    change decide (b = u ∨ b = u) = true at hb
    simp only [or_self, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    exact G.ne_of_adj hab rfl

  have graphFun_edge {u v : Fin 11} (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
    change decide (∃ a b : Fin 11, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true) = true
    rw [decide_eq_true_eq]
    refine ⟨u, v, huv, ?_, ?_⟩
    · change decide (u = u ∨ u = v) = true; simp
    · change decide (v = u ∨ v = v) = true; simp

  -- Helper 6: mixing G C ⊆ orN G C \ lam G C
  have hM_sub_R : mixing G C ⊆ orN G C \ lam G C := by
    intro m hm
    obtain ⟨hmor, hmix⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_sdiff.mpr ⟨hmor, ?_⟩
    intro hlam
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
    have h0' : orIn 11 C (opnd C m 0) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h0
    have h1' : orIn 11 C (opnd C m 1) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h1
    exact hmix (propext ⟨fun h => absurd h h0', fun h => absurd h h1'⟩)

  -- Helper 7: orIn of an AND gate wire is empty
  have orIn_and_empty {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
      orIn 11 C (11 + j) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hi
    rcases hcase with heq | ⟨k, _, hrk, hork, _⟩
    · omega
    · rcases (orReaches_iff hj).mp hrk with rfl | ⟨hor, _⟩
      · rw [hand] at hork; cases hork
      · rw [hand] at hor; cases hor

  -- Helper 8: orIn of an OR gate is union of orIn of its two operands
  have orIn_or_nonempty {k : ℕ} (hk : k < C.gates.length) (hork : (gateAt C k).op = GateOp.or)
      (hne : (orIn 11 C (11 + k)).Nonempty) :
      (orIn 11 C (opnd C k 0)).Nonempty ∨ (orIn 11 C (opnd C k 1)).Nonempty := by
    obtain ⟨i, hi⟩ := hne
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hi
    rcases hcase with heq | ⟨m, hm, hrm, horm, him⟩
    · omega
    · rcases (orReaches_iff hk).mp hrm with rfl | ⟨_, w, hw, _, hwm⟩
      · rw [inputs_two hk] at him
        simp only [List.mem_cons, List.not_mem_nil, or_false] at him
        rcases him with h0 | h1
        · exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h0⟩⟩
        · exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h1⟩⟩
      · rw [inputs_two hk] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨m, hm, hwm, horm, him⟩⟩⟩
        · exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨m, hm, hwm, horm, him⟩⟩⟩

  -- Helper 9: Extract a mixing gate along any OR-path from a nonempty-orIn wire to a junk gate!
  have extract_mixing : ∀ w : ℕ, ∀ j ∈ junk G C,
      OrReaches 11 C w j → (orIn 11 C w).Nonempty →
      ∃ m ∈ mixing G C, OrReaches 11 C w m := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro j hj hrej hne
      have hj_data := (Finset.mem_filter.mp hj).2
      have hj_lt : j < C.gates.length := hj_data.2.1
      have hj_and : (gateAt C j).op = GateOp.and := hj_data.1
      have hw11 : 11 ≤ w := hrej.1
      have hwlen : w - 11 < C.gates.length := orReaches_lt_len hrej
      obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases (orReaches_iff hk).mp hrej with rfl | ⟨hork, w', hw', hw'lt, hw'j⟩
      · rw [orIn_and_empty hj_lt hj_and] at hne
        exact absurd hne (by simp)
      · by_cases hne' : (orIn 11 C w').Nonempty
        · obtain ⟨m, hm, hrm⟩ := ih w' hw'lt j hj hw'j hne'
          exact ⟨m, hm, orReaches_step hk hork hw' hw'lt hrm⟩
        · have hempty' : orIn 11 C w' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
          have hnotbf : ¬ BelowF G C k := by
            intro hbf
            obtain ⟨x, hgx, hgfx⟩ := hj_data.2.2
            have hkx : gateVal 11 C k x = true := orReaches_val (11 + k) j x hrej hgx
            have := hbf x hkx
            rw [hgfx] at this; cases this
          have hkorN : k ∈ orN G C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hork, hnotbf⟩
          rw [inputs_two hk] at hw'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
          have hboth := orIn_or_nonempty hk hork hne
          have hmix : k ∈ mixing G C := by
            refine Finset.mem_filter.mpr ⟨hkorN, ?_⟩
            rcases hw' with rfl | rfl
            · rcases hboth with h0 | h1
              · rw [hempty'] at h0; exact absurd h0 (by simp)
              · intro heq
                have h1e : orIn 11 C (opnd C k 1) = ∅ := heq.mp hempty'
                rw [h1e] at h1; exact absurd h1 (by simp)
            · rcases hboth with h0 | h1
              · intro heq
                have h0e : orIn 11 C (opnd C k 0) = ∅ := heq.mpr hempty'
                rw [h0e] at h0; exact absurd h0 (by simp)
              · rw [hempty'] at h1; exact absurd h1 (by simp)
          exact ⟨k, hmix, orReaches_self hk⟩

  -- Helper 10: Every edge s(u, v) ∈ Ustar G C is covered by a centreless top OR
  -- by a non-centreless top via a mixing gate m ∈ mixing G C and a junk gate j ∈ junk G C!
  have ustar_witness : ∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
      (∃ t ∈ centreless G C, gateVal 11 C t (pairInput u v) = true) ∨
      (∃ t ∈ tops G C \ centreless G C, ∃ b : Fin 2, ∃ m ∈ mixing G C, ∃ j ∈ junk G C,
        OrReaches 11 C (opnd C t b) m ∧ OrReaches 11 C (opnd C t b) j ∧
        gateVal 11 C j (pairInput u v) = true ∧ gateVal 11 C t (pairInput u v) = true ∧
        side C t (1 - b) ⊆ wmax G C j) := by
    intro u v huvU
    obtain ⟨huvG, huvNotStar⟩ := Finset.mem_sdiff.mp huvU
    have huvAdj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp huvG
    have hout : val (List.ofFn (pairInput u v)) C.output = true := by
      rw [out_eq]; exact graphFun_edge huvAdj
    rcases or_trace_val C.output (pairInput u v) hout with ⟨i, hi, hxi⟩ | ⟨t, ht, hrt, htand, htv⟩
    · -- Output cannot reach an input wire through OR gates (single vertex input makes graphFun false)
      have h1 : val (List.ofFn (pairInput i i)) C.output = true :=
        orIn_val hi (by change decide (i = i ∨ i = i) = true; simp)
      rw [out_eq, graphFun_single i] at h1
      cases h1
    · -- t is an AND gate with OrReaches C.output t, hence BelowF G C t, so t ∈ tops G C!
      have htbf : BelowF G C t := by
        intro x htx
        have hxout : val (List.ofFn x) C.output = true := orReaches_val C.output t x hrt htx
        rw [out_eq] at hxout; exact hxout
      have htTop : t ∈ tops G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, htand, htbf⟩
      by_cases htC : t ∈ centreless G C
      · exact Or.inl ⟨t, htC, htv⟩
      · -- t ∉ centreless G C: both operands are true at pairInput u v, both sides nonempty
        have hboth_op : ∀ b : Fin 2, val (List.ofFn (pairInput u v)) (opnd C t b) = true := by
          intro b
          have hmem : opnd C t b ∈ (gateAt C t).inputs := by
            rw [inputs_two ht]; fin_cases b <;> simp
          exact ((val_and (by simp) ht htand).mp htv (opnd C t b) hmem).2
        have h0tr := or_trace_val (opnd C t 0) (pairInput u v) (hboth_op 0)
        have h1tr := or_trace_val (opnd C t 1) (pairInput u v) (hboth_op 1)
        -- At least one side must trace to an AND gate (otherwise s(u,v) ∈ starEdges!)
        have hexJ : ∃ b : Fin 2, ∃ j < C.gates.length, OrReaches 11 C (opnd C t b) j ∧
            (gateAt C j).op = GateOp.and ∧ gateVal 11 C j (pairInput u v) = true := by
          rcases h0tr with ⟨i0, hi0, hxi0⟩ | ⟨j, hj, hrj, hjand, hjv⟩
          · rcases h1tr with ⟨i1, hi1, hxi1⟩ | ⟨j, hj, hrj, hjand, hjv⟩
            · -- Both sides reach inputs i0, i1 ∈ {u, v}!
              change decide (i0 = u ∨ i0 = v) = true at hxi0
              change decide (i1 = u ∨ i1 = v) = true at hxi1
              simp only [decide_eq_true_eq] at hxi0 hxi1
              by_cases heq : i0 = i1
              · subst heq
                have hv0 : val (List.ofFn (pairInput i0 i0)) (opnd C t 0) = true :=
                  orIn_val hi0 (by change decide (i0 = i0 ∨ i0 = i0) = true; simp)
                have hv1 : val (List.ofFn (pairInput i0 i0)) (opnd C t 1) = true :=
                  orIn_val hi1 (by change decide (i0 = i0 ∨ i0 = i0) = true; simp)
                have hts : gateVal 11 C t (pairInput i0 i0) = true := by
                  rw [gateVal_eq]
                  refine (val_and (by simp) ht htand).mpr ?_
                  intro w hw
                  rw [inputs_two ht] at hw
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                  rcases hw with rfl | rfl
                  · exact ⟨opnd_lt ht 0, hv0⟩
                  · exact ⟨opnd_lt ht 1, hv1⟩
                have hgf := htbf (pairInput i0 i0) hts
                rw [graphFun_single i0] at hgf; cases hgf
              · have hs : s(i0, i1) = s(u, v) := by
                  rcases hxi0 with rfl | rfl <;> rcases hxi1 with rfl | rfl
                  · exact absurd rfl heq
                  · rfl
                  · exact Sym2.eq_swap
                  · exact absurd rfl heq
                exfalso
                apply huvNotStar
                rw [← hs]
                exact Finset.mem_biUnion.mpr ⟨t, htTop,
                  Finset.mem_image.mpr ⟨(i0, i1), Finset.mem_product.mpr ⟨hi0, hi1⟩, rfl⟩⟩
            · exact ⟨1, j, hj, hrj, hjand, hjv⟩
          · exact ⟨0, j, hj, hrj, hjand, hjv⟩
        obtain ⟨b, j, hj, hrj, hjand, hjv⟩ := hexJ
        -- By TopForm, j cannot be BelowF, hence j ∈ junk G C!
        have hmem_b : opnd C t b ∈ (gateAt C t).inputs := by
          rw [inputs_two ht]; fin_cases b <;> simp
        have hic : InCone 11 C j t := orReaches_inCone (opnd C t b) j hrj t ht hmem_b (opnd_lt ht b)
        have hjNotBf : ¬ BelowF G C j := fun hjbf => htop j hj t ht hjand hjbf htand hic
        have hjJunk : j ∈ junk G C := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjand, hj, ?_⟩
          by_contra hno
          apply hjNotBf
          intro x hgx
          by_contra hgf
          have hgf' : graphFun G ∅ x = false := by
            cases hq : graphFun G ∅ x
            · rfl
            · exact absurd hq hgf
          exact hno ⟨x, hgx, hgf'⟩
        -- Both sides of t are nonempty since t ∉ centreless G C
        have hne_both : (side (n := 11) C t 0).Nonempty ∧ (side (n := 11) C t 1).Nonempty := by
          have hnot : ¬ (side (n := 11) C t 0 = ∅ ∨ side (n := 11) C t 1 = ∅) := by
            intro hdisj
            exact htC (Finset.mem_filter.mpr ⟨htTop, hdisj⟩)
          exact ⟨Finset.nonempty_iff_ne_empty.mpr (fun h => hnot (Or.inl h)),
                 Finset.nonempty_iff_ne_empty.mpr (fun h => hnot (Or.inr h))⟩
        have hneb : (orIn 11 C (opnd C t b)).Nonempty := by
          fin_cases b
          · exact hne_both.1
          · exact hne_both.2
        obtain ⟨m, hm, hrm⟩ := extract_mixing (opnd C t b) j hjJunk hrj hneb
        -- Also side C t (1 - b) ⊆ wmax G C j!
        have hwmax : side C t (1 - b) ⊆ wmax G C j := by
          intro w hw
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro x hgx hxw
          have hvb : val (List.ofFn x) (opnd C t b) = true :=
            orReaches_val (opnd C t b) j x hrj hgx
          have hv1b : val (List.ofFn x) (opnd C t (1 - b)) = true :=
            orIn_val hw hxw
          have htx : gateVal 11 C t x = true := by
            rw [gateVal_eq]
            refine (val_and (by simp) ht htand).mpr ?_
            intro y hy
            rw [inputs_two ht] at hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            fin_cases b
            · rcases hy with rfl | rfl
              · exact ⟨opnd_lt ht 0, hvb⟩
              · exact ⟨opnd_lt ht 1, hv1b⟩
            · rcases hy with rfl | rfl
              · exact ⟨opnd_lt ht 0, hv1b⟩
              · exact ⟨opnd_lt ht 1, hvb⟩
          exact htbf x htx
        exact Or.inr ⟨t, Finset.mem_sdiff.mpr ⟨htTop, htC⟩, b, m, hm, j, hjJunk, hrm, hrj, hjv, htv, hwmax⟩

  -- Final 3-way split into pureMixing, pureCentreless, hybridCover!
  have hM_card_le : (mixing G C).card ≤ (orN G C \ lam G C).card := Finset.card_le_card hM_sub_R
  by_cases hT0 : centreless G C = ∅
  · -- Child 1: pureMixing
    have hU_ne : (Ustar G C).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hU_ne
    have hM_ne : (mixing G C).Nonempty := by
      induction e using Sym2.inductionOn with
      | _ u v =>
        rcases ustar_witness u v he with ⟨t, htC, _⟩ | ⟨_, _, _, m, hm, _⟩
        · rw [hT0] at htC; simp at htC
        · exact ⟨m, hm⟩
    have hM1 : 1 ≤ (mixing G C).card := Finset.card_pos.mpr hM_ne
    have hT0c : (centreless G C).card = 0 := by rw [hT0]; simp
    have hJRlt : (junk G C).card + (orN G C \ lam G C).card < (Ustar G C).card := by omega
    have hU4 : 4 ≤ (Ustar G C).card := by omega
    refine pureMixing C hsz ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hT0 hjunk hM1 hM_sub_R hU4 hJRlt hnested' ?_
    intro u v huv
    rcases ustar_witness u v huv with ⟨t, htC, _⟩ | ⟨t, ht, b, m, hm, j, hj, hrm, hrj, hjv, htv, hwmax⟩
    · rw [hT0] at htC; simp at htC
    · obtain ⟨htTop, htNotC⟩ := Finset.mem_sdiff.mp ht
      have hne_both : (side (n := 11) C t 0).Nonempty ∧ (side (n := 11) C t 1).Nonempty := by
        have hnot : ¬ (side (n := 11) C t 0 = ∅ ∨ side (n := 11) C t 1 = ∅) := fun h =>
          htNotC (Finset.mem_filter.mpr ⟨htTop, h⟩)
        exact ⟨Finset.nonempty_iff_ne_empty.mpr (fun h => hnot (Or.inl h)),
               Finset.nonempty_iff_ne_empty.mpr (fun h => hnot (Or.inr h))⟩
      have hne1b : (side (n := 11) C t (1 - b)).Nonempty := by
        fin_cases b
        · exact hne_both.2
        · exact hne_both.1
      exact ⟨t, htTop, b, m, hm, j, hj, hrm, hrj, hjv, htv, hne1b, hwmax⟩
  · -- (centreless G C).Nonempty
    have hT01 : 1 ≤ (centreless G C).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT0)
    by_cases hAllC : ∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
        ∃ t ∈ centreless G C, gateVal 11 C t (pairInput u v) = true
    · -- Child 2: pureCentreless
      have hU5 : 5 ≤ (Ustar G C).card := by omega
      exact pureCentreless C hsz ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hT01 hjunk hU5 hlt hnested' hAllC
    · -- Child 3: hybridCover (some edge in U* is NOT covered by centreless, so mixing is nonempty!)
      have hM_ne : (mixing G C).Nonempty := by
        by_contra hMempty
        apply hAllC
        intro u v huv
        rcases ustar_witness u v huv with hc | ⟨_, _, _, m, hm, _⟩
        · exact hc
        · exact absurd ⟨m, hm⟩ hMempty
      have hM1 : 1 ≤ (mixing G C).card := Finset.card_pos.mpr hM_ne
      have hU6 : 6 ≤ (Ustar G C).card := by omega
      exact hybridCover C hsz ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hT01 hjunk hM1 hM_sub_R hU6 hlt hnested' ustar_witness
