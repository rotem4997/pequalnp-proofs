import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- In G11 (cover number 7) with exactly two incomparable junk ANDs j1, j2 sharing a top t,
-- both j1 and j2 reach operands of t purely through OR gates (by TopForm). Splitting on how
-- j1, j2 enter t (same side with empty orIn, same side with nonempty orIn, opposite sides of a
-- non-centreless top, or a centreless top) yields sharp lower bounds on |orN \ lam|, |centreless|,
-- and |U*| via tau(G11 \ U*) + |U*| >= 7, plus side(t, 1-b) ⊆ wmax(j1) ∩ wmax(j2) in the
-- empty-side case.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2262_4
    (sameSideMixing :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j1 j2 t : ℕ) (b : Fin 2),
        let T := tops G C
        let Z := centreless G C
        let U := Ustar G C
        let R := orN G C \ lam G C
        G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
        IsLeastAO G C → TopForm G C → C.size < 22 → j1 < j2 → junk G C = {j1, j2} →
        ¬ InCone 11 C j1 j2 → ¬ InCone 11 C j2 j1 → t ∈ T \ Z →
        OrReaches 11 C (opnd C t b) j1 → OrReaches 11 C (opnd C t b) j2 →
        2 ≤ R.card → 3 ≤ U.card →
        17 + (T \ Z).card + 2 * Z.card + R.card ≤ C.size + U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ Z).card) → False)
    (oppSidesCentred :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j1 j2 t : ℕ) (b : Fin 2),
        let T := tops G C
        let Z := centreless G C
        let U := Ustar G C
        let R := orN G C \ lam G C
        G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
        IsLeastAO G C → TopForm G C → C.size < 22 → j1 < j2 → junk G C = {j1, j2} →
        ¬ InCone 11 C j1 j2 → ¬ InCone 11 C j2 j1 → t ∈ T \ Z →
        OrReaches 11 C (opnd C t b) j1 → OrReaches 11 C (opnd C t (1 - b)) j2 →
        2 ≤ R.card → 3 ≤ U.card →
        17 + (T \ Z).card + 2 * Z.card + R.card ≤ C.size + U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ Z).card) → False)
    (centrelessSameSide :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j1 j2 t : ℕ) (b : Fin 2),
        let T := tops G C
        let Z := centreless G C
        let U := Ustar G C
        let R := orN G C \ lam G C
        G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
        IsLeastAO G C → TopForm G C → C.size < 22 → j1 < j2 → junk G C = {j1, j2} →
        ¬ InCone 11 C j1 j2 → ¬ InCone 11 C j2 j1 → t ∈ Z →
        OrReaches 11 C (opnd C t b) j1 → OrReaches 11 C (opnd C t b) j2 →
        orIn 11 C (opnd C t (1 - b)) ⊆ wmax G C j1 ∩ wmax G C j2 →
        1 ≤ Z.card → 1 ≤ R.card → 3 ≤ U.card →
        17 + (T \ Z).card + 2 * Z.card + R.card ≤ C.size + U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ Z).card) → False)
    (centrelessOppSides :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j1 j2 t : ℕ) (b : Fin 2),
        let T := tops G C
        let Z := centreless G C
        let U := Ustar G C
        let R := orN G C \ lam G C
        G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
        IsLeastAO G C → TopForm G C → C.size < 22 → j1 < j2 → junk G C = {j1, j2} →
        ¬ InCone 11 C j1 j2 → ¬ InCone 11 C j2 j1 → t ∈ Z →
        OrReaches 11 C (opnd C t b) j1 → OrReaches 11 C (opnd C t (1 - b)) j2 →
        1 ≤ Z.card → 3 ≤ U.card →
        17 + (T \ Z).card + 2 * Z.card + R.card ≤ C.size + U.card →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ Z).card) → False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  let _ : DecidableEq GateOp := gateOpDecEq
  let G0 := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  have hG0Adj :
      G0.Adj 1 4 ∧ G0.Adj 1 8 ∧ G0.Adj 4 8 ∧
      G0.Adj 3 6 ∧ G0.Adj 3 7 ∧ G0.Adj 6 7 ∧
      G0.Adj 0 10 ∧ G0.Adj 10 2 ∧ G0.Adj 2 5 ∧ G0.Adj 5 9 ∧ G0.Adj 9 0 := by decide
  intro G inst C j1 j2 hEqG hLeast htop T Z U cone _ _ hBudget hCover hlt12 hjunkEq hno12 hno21 hShared
  dsimp only [T, Z, U] at hBudget hCover
  by_contra hlt22
  have hsz : C.size < 22 := by omega
  obtain ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ := hLeast
  have hGAdj :
      G.Adj 1 4 ∧ G.Adj 1 8 ∧ G.Adj 4 8 ∧
      G.Adj 3 6 ∧ G.Adj 3 7 ∧ G.Adj 6 7 ∧
      G.Adj 0 10 ∧ G.Adj 10 2 ∧ G.Adj 2 5 ∧ G.Adj 5 9 ∧ G.Adj 9 0 := by
    rw [hEqG]; exact hG0Adj
  -- Proof of tau(G \ U*) + |U*| >= 7 via disjoint K3((1, 4, 8)) ⊔ K3((3, 6, 7)) ⊔ C5(0,10,2,5,9)
  have hTauPlusU : ∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K ∧
      7 ≤ K.card + (Ustar G C).card := by
    let U0 := Ustar G C
    let H := G.deleteEdges ↑U0
    classical
    let covers := (Finset.univ : Finset (Fin 11)).powerset.filter (fun S : Finset (Fin 11) => H.IsVertexCover (S : Set (Fin 11)))
    have hUnivCov : (Finset.univ : Finset (Fin 11)) ∈ covers := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩
      intro u v _; exact Or.inl (Finset.mem_univ u)
    obtain ⟨K, hKmem, hKmin⟩ := Finset.exists_min_image covers Finset.card ⟨Finset.univ, hUnivCov⟩
    have hKcov : H.IsVertexCover (K : Set (Fin 11)) := (Finset.mem_filter.mp hKmem).2
    have hKMin : IsMinCover H K := by
      refine ⟨hKcov, fun S hS => hKmin S (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hS⟩)⟩
    refine ⟨K, hKMin, ?_⟩
    have hPick (e : Sym2 (Fin 11)) : ∃ v : Fin 11, v ∈ e := by
      induction e using Sym2.inductionOn with
      | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩
    choose pick hpick using hPick
    let K' : Finset (Fin 11) := K ∪ U0.image pick
    have hK'card : K'.card ≤ K.card + U0.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
    have hK'cov : G.IsVertexCover (K' : Set (Fin 11)) := by
      intro u v huv
      by_cases hu : s(u, v) ∈ U0
      · have hp := hpick s(u, v)
        rw [Sym2.mem_iff] at hp
        rcases hp with h1 | h2
        · left; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s(u, v), hu, h1⟩)
        · right; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s(u, v), hu, h2⟩)
      · have hH : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, hu⟩
        rcases hKcov hH with h1 | h2
        · exact Or.inl (Finset.mem_union_left _ h1)
        · exact Or.inr (Finset.mem_union_left _ h2)
    have hK'ge7 : 7 ≤ K'.card := by
      obtain ⟨e14, e18, e48, e36, e37, e67, e0a, ea2, e25, e59, e90⟩ := hGAdj
      let f : Fin 11 → ℕ := fun v => if v ∈ K' then 1 else 0
      have hf_edge : ∀ u v : Fin 11, G.Adj u v → 1 ≤ f u + f v := by
        intro u v huv
        rcases hK'cov huv with hu | hv
        · have : f u = 1 := ite_eq_left hu; omega
        · have : f v = 1 := ite_eq_left hv; omega
      have hcard : K'.card = ∑ i : Fin 11, f i := by
        simp [f]
      have hsum : ∑ i : Fin 11, f i =
          f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
            Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
            Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
        change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + f 10))))))))) = _
        omega
      have h14 := hf_edge 1 4 e14
      have h18 := hf_edge 1 8 e18
      have h48 := hf_edge 4 8 e48
      have h36 := hf_edge 3 6 e36
      have h37 := hf_edge 3 7 e37
      have h67 := hf_edge 6 7 e67
      have h0a := hf_edge 0 10 e0a
      have ha2 := hf_edge 10 2 ea2
      have h25 := hf_edge 2 5 e25
      have h59 := hf_edge 5 9 e59
      have h90 := hf_edge 9 0 e90
      omega
    exact hK'ge7.trans hK'card
  obtain ⟨Kmin, hKmin, h7le⟩ := hTauPlusU
  have hKminLe : Kmin.card ≤ (tops G C \ centreless G C).card := hCover Kmin hKmin
  have hKeyBound : 3 + 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 2 * (Ustar G C).card := by
    omega
  -- Verified TopForm helpers from R_meta_8069_2
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

  -- Strengthened extract_mixing: also tracks OrReaches 11 C (11 + m) j!
  have extract_mixing : ∀ w : ℕ, ∀ j ∈ junk G C,
      OrReaches 11 C w j → (orIn 11 C w).Nonempty →
      ∃ m ∈ mixing G C, OrReaches 11 C w m ∧ OrReaches 11 C (11 + m) j := by
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
        · obtain ⟨m, hm, hrm, hmj⟩ := ih w' hw'lt j hj hw'j hne'
          exact ⟨m, hm, orReaches_step hk hork hw' hw'lt hrm, hmj⟩
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
          exact ⟨k, hmix, orReaches_self hk, hrej⟩
  -- Basic InCone helpers for cones_getD
  have inCone_lt_len (i k : ℕ) (h : InCone 11 C i k) : k < C.gates.length := by
    by_contra hge
    have hlen : (cones 11 C).length = C.gates.length := by
      have hfl : ∀ (gs : List Gate) (cs : List (List ℕ)), (gs.foldl stepCone cs).length = cs.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro cs; simp
        | cons g gs ih => intro cs; rw [List.foldl_cons, ih]; simp [stepCone]; omega
      rw [cones_eq, hfl]; simp
    have hnil : (cones 11 C).getD k [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (cones 11 C).length ≤ k)]
    change i ∈ (cones 11 C).getD k [] at h
    rw [hnil] at h
    exact List.not_mem_nil h
  have inCone_iff (i k : ℕ) (hk : k < C.gates.length) :
      InCone 11 C i k ↔ ∃ w ∈ (gateAt C k).inputs, 11 ≤ w ∧ w < 11 + k ∧
        (i = w - 11 ∨ InCone 11 C i (w - 11)) := by
    change i ∈ (cones 11 C).getD k [] ↔ _
    rw [cones_getD hk, List.mem_flatMap]
    constructor
    · rintro ⟨w, hwf, hi⟩
      obtain ⟨hw, hcond⟩ := List.mem_filter.mp hwf
      obtain ⟨h11, hlt⟩ := of_decide_eq_true hcond
      exact ⟨w, hw, h11, hlt, List.mem_cons.mp hi⟩
    · rintro ⟨w, hw, h11, hlt, hcase⟩
      exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h11, hlt⟩⟩, List.mem_cons.mpr hcase⟩
  have inCone_trans : ∀ k i j, InCone 11 C i j → InCone 11 C j k → InCone 11 C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i j hij hjk
      have hk := inCone_lt_len j k hjk
      obtain ⟨w, hw, h11, hlt, hcase⟩ := (inCone_iff j k hk).mp hjk
      refine (inCone_iff i k hk).mpr ⟨w, hw, h11, hlt, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 11) (by omega) i j hij hsub
  have inCone_lt : ∀ k i, InCone 11 C i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i h
      have hk := inCone_lt_len i k h
      obtain ⟨w, _, h11, hlt, hcase⟩ := (inCone_iff i k hk).mp h
      rcases hcase with rfl | hsub
      · omega
      · have := ih (w - 11) (by omega) i hsub; omega
  -- Key Lemma 1: for any top t and junk j in its cone, j reaches an operand of t via ORs!
  have hj1Junk : j1 ∈ junk G C := by rw [hjunkEq]; simp
  have hj2Junk : j2 ∈ junk G C := by rw [hjunkEq]; simp
  have inCone_to_orReaches (t : ℕ) (htTop : t ∈ tops G C) (j : ℕ) (hj : j ∈ junk G C) :
      ∀ k, (k = t ∨ InCone 11 C k t) → InCone 11 C j k →
      ∃ b : Fin 2, OrReaches 11 C (opnd C k b) j := by
    have htData := Finset.mem_filter.mp htTop
    have htLt : t < C.gates.length := Finset.mem_range.mp htData.1
    have htAnd : (gateAt C t).op = GateOp.and := htData.2.1
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkt hjk
      have hkLt := inCone_lt_len j k hjk
      obtain ⟨w, hw, h11, hlt, hcase⟩ := (inCone_iff j k hkLt).mp hjk
      have hwb : ∃ b : Fin 2, w = opnd C k b := by
        rw [inputs_two hkLt] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      obtain ⟨b, rfl⟩ := hwb
      rcases hcase with hEq | hSub
      · refine ⟨b, ?_⟩
        have hEqW : opnd C k b = 11 + j := by omega
        rw [hEqW]
        exact orReaches_self ((Finset.mem_filter.mp hj).2.2.1)
      · let m := opnd C k b - 11
        have hmLt : m < k := by omega
        have hEqW : opnd C k b = 11 + m := by omega
        have hmk : InCone 11 C m k :=
          inCone_direct hkLt (by rw [← hEqW, inputs_two hkLt]; fin_cases b <;> simp) hmLt
        have hmt : InCone 11 C m t := by
          rcases hkt with rfl | hkt'
          · exact hmk
          · exact inCone_trans t m k hmk hkt'
        have hmOr : (gateAt C m).op = GateOp.or := by
          rcases hao (gateAt C m) (gateAt_mem (by omega)) with hand | hor
          · exfalso
            by_cases hbf : BelowF G C m
            · exact htop m (by omega) t htLt hand hbf htAnd hmt
            · have hmJunk : m ∈ junk G C := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hand, by omega, ?_⟩
                by_contra hno
                apply hbf
                intro x hmx
                cases hgf : graphFun G ∅ x with
                | true => rfl
                | false => exact False.elim (hno ⟨x, hmx, hgf⟩)
              rw [hjunkEq] at hj hmJunk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj hmJunk
              have hltJM := inCone_lt m j hSub
              rcases hj with rfl | rfl <;> rcases hmJunk with rfl | rfl
              · omega
              · exact hno12 hSub
              · exact hno21 hSub
              · omega
          · exact hor
        obtain ⟨b', hb'⟩ := ih m hmLt (Or.inr hmt) hSub
        refine ⟨b, ?_⟩
        rw [hEqW]
        exact orReaches_step (by omega) hmOr
          (by rw [inputs_two (by omega)]; fin_cases b' <;> simp) (opnd_lt (by omega) b') hb'
  -- Key Lemma 2: same-side merger gives >= 1 gate in orN \ lam, and >= 2 if orIn w is nonempty!
  have sameSide_orN (w : ℕ) (hr1 : OrReaches 11 C w j1) (hr2 : OrReaches 11 C w j2) :
      1 ≤ (orN G C \ lam G C).card ∧
      ((orIn 11 C w).Nonempty → 2 ≤ (orN G C \ lam G C).card) := by
    have hj1Data := (Finset.mem_filter.mp hj1Junk).2
    have hj2Data := (Finset.mem_filter.mp hj2Junk).2
    have hw11 : 11 ≤ w := hr1.1
    have hwLen : w - 11 < C.gates.length := orReaches_lt_len hr1
    let M := (Finset.range C.gates.length).filter fun h =>
      OrReaches 11 C w h ∧ OrReaches 11 C (11 + h) j1 ∧ OrReaches 11 C (11 + h) j2
    have hMNE : M.Nonempty := by
      refine ⟨w - 11, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwLen, ?_, ?_, ?_⟩⟩
      · have hEq : 11 + (w - 11) = w := by omega
        conv_lhs => rw [← hEq]
        exact orReaches_self hwLen
      · have hEq : 11 + (w - 11) = w := by omega
        rw [hEq]; exact hr1
      · have hEq : 11 + (w - 11) = w := by omega
        rw [hEq]; exact hr2
    let m0 := M.min' hMNE
    have hm0Mem := Finset.mem_filter.mp (Finset.min'_mem M hMNE)
    have hm0Lt : m0 < C.gates.length := Finset.mem_range.mp hm0Mem.1
    have hm0W : OrReaches 11 C w m0 := hm0Mem.2.1
    have hm01 : OrReaches 11 C (11 + m0) j1 := hm0Mem.2.2.1
    have hm02 : OrReaches 11 C (11 + m0) j2 := hm0Mem.2.2.2
    have hm0Or : (gateAt C m0).op = GateOp.or := by
      rcases hao (gateAt C m0) (gateAt_mem hm0Lt) with hand | hor
      · rcases (orReaches_iff hm0Lt).mp hm01 with h1 | ⟨hbad, _⟩
        · rcases (orReaches_iff hm0Lt).mp hm02 with h2 | ⟨hbad, _⟩
          · omega
          · rw [hand] at hbad; cases hbad
        · rw [hand] at hbad; cases hbad
      · exact hor
    have hm0NotBf : ¬ BelowF G C m0 := by
      intro hbf
      obtain ⟨x, hgx, hgfx⟩ := hj1Data.2.2
      have hkx : gateVal 11 C m0 x = true := orReaches_val (11 + m0) j1 x hm01 hgx
      have := hbf x hkx; rw [hgfx] at this; cases this
    have hm0orN : m0 ∈ orN G C :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm0Lt, hm0Or, hm0NotBf⟩
    have hm0Min (b : Fin 2) : ¬ (OrReaches 11 C (opnd C m0 b) j1 ∧ OrReaches 11 C (opnd C m0 b) j2) := by
      rintro ⟨h1, h2⟩
      have h11 : 11 ≤ opnd C m0 b := h1.1
      have hlt : opnd C m0 b < 11 + m0 := opnd_lt hm0Lt b
      let h := opnd C m0 b - 11
      have hEq : opnd C m0 b = 11 + h := by omega
      have hMemM : h ∈ M := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, by rw [← hEq]; exact h1, by rw [← hEq]; exact h2⟩
        have hm0h : OrReaches 11 C (11 + m0) h :=
          orReaches_step hm0Lt hm0Or (by rw [inputs_two hm0Lt]; fin_cases b <;> simp) hlt
            (by rw [hEq]; exact orReaches_self (by omega))
        exact orReaches_trans w m0 h hm0W hm0h
      have hle := Finset.min'_le M h hMemM
      omega
    have hReachOpnd (j : ℕ) (hj : j ∈ junk G C) (hm0j : OrReaches 11 C (11 + m0) j) :
        ∃ b : Fin 2, OrReaches 11 C (opnd C m0 b) j := by
      rcases (orReaches_iff hm0Lt).mp hm0j with rfl | ⟨_, u, hu, _, huj⟩
      · have hjAnd := (Finset.mem_filter.mp hj).2.1
        rw [hm0Or] at hjAnd; cases hjAnd
      · rw [inputs_two hm0Lt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨0, huj⟩
        · exact ⟨1, huj⟩
    obtain ⟨b1, hb1⟩ := hReachOpnd j1 hj1Junk hm01
    obtain ⟨b2, hb2⟩ := hReachOpnd j2 hj2Junk hm02
    have hb12Ne : b1 ≠ b2 := fun heq => hm0Min b1 ⟨hb1, heq ▸ hb2⟩
    have hNotOther1 : ¬ OrReaches 11 C (opnd C m0 b1) j2 := fun h => hm0Min b1 ⟨hb1, h⟩
    have hNotOther2 : ¬ OrReaches 11 C (opnd C m0 b2) j1 := fun h => hm0Min b2 ⟨h, hb2⟩
    by_cases hne1 : (orIn 11 C (opnd C m0 b1)).Nonempty
    · by_cases hne2 : (orIn 11 C (opnd C m0 b2)).Nonempty
      · -- Both operands nonempty: two distinct mixing gates!
        obtain ⟨m1, hm1, hr1m, hm1j1⟩ := extract_mixing (opnd C m0 b1) j1 hj1Junk hb1 hne1
        obtain ⟨m2, hm2, hr2m, hm2j2⟩ := extract_mixing (opnd C m0 b2) j2 hj2Junk hb2 hne2
        have h12Ne : m1 ≠ m2 := by
          intro heq; subst heq
          exact hNotOther1 (orReaches_trans (opnd C m0 b1) m1 j2 hr1m hm2j2)
        have hSub : ({m1, m2} : Finset ℕ) ⊆ orN G C \ lam G C := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hM_sub_R hm1
          · exact hM_sub_R hm2
        have h2 : 2 ≤ (orN G C \ lam G C).card := by
          have := Finset.card_le_card hSub
          rw [Finset.card_pair h12Ne] at this; exact this
        exact ⟨by omega, fun _ => h2⟩
      · -- opnd b1 nonempty, opnd b2 empty: m0 ∈ orN \ lam AND m1 ∈ mixing below m0!
        have hm0NotLam : m0 ∉ lam G C := by
          intro hlam
          obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
          fin_cases b2
          · exact hne2 h0
          · exact hne2 h1
        have hm0R : m0 ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hm0orN, hm0NotLam⟩
        obtain ⟨m1, hm1, hr1m, _⟩ := extract_mixing (opnd C m0 b1) j1 hj1Junk hb1 hne1
        have hm1Lt : m1 < m0 := by
          have hle := (orReaches_le (opnd C m0 b1) m1 hr1m).1
          have hlt := opnd_lt hm0Lt b1
          have h11 := hr1m.1
          omega
        have hSub : ({m0, m1} : Finset ℕ) ⊆ orN G C \ lam G C := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hm0R
          · exact hM_sub_R hm1
        have h2 : 2 ≤ (orN G C \ lam G C).card := by
          have := Finset.card_le_card hSub
          rw [Finset.card_pair (by omega : m0 ≠ m1)] at this; exact this
        exact ⟨by omega, fun _ => h2⟩
    · by_cases hne2 : (orIn 11 C (opnd C m0 b2)).Nonempty
      · -- opnd b1 empty, opnd b2 nonempty: m0 ∈ orN \ lam AND m2 ∈ mixing below m0!
        have hm0NotLam : m0 ∉ lam G C := by
          intro hlam
          obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
          fin_cases b1
          · exact hne1 h0
          · exact hne1 h1
        have hm0R : m0 ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hm0orN, hm0NotLam⟩
        obtain ⟨m2, hm2, hr2m, _⟩ := extract_mixing (opnd C m0 b2) j2 hj2Junk hb2 hne2
        have hm2Lt : m2 < m0 := by
          have hle := (orReaches_le (opnd C m0 b2) m2 hr2m).1
          have hlt := opnd_lt hm0Lt b2
          have h11 := hr2m.1
          omega
        have hSub : ({m0, m2} : Finset ℕ) ⊆ orN G C \ lam G C := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hm0R
          · exact hM_sub_R hm2
        have h2 : 2 ≤ (orN G C \ lam G C).card := by
          have := Finset.card_le_card hSub
          rw [Finset.card_pair (by omega : m0 ≠ m2)] at this; exact this
        exact ⟨by omega, fun _ => h2⟩
      · -- Both operands of m0 empty: m0 ∈ orN \ lam AND m0 ∉ mixing!
        have hm0NotLam : m0 ∉ lam G C := by
          intro hlam
          obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
          fin_cases b1
          · exact hne1 h0
          · exact hne1 h1
        have hm0R : m0 ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hm0orN, hm0NotLam⟩
        have h1 : 1 ≤ (orN G C \ lam G C).card := Finset.card_pos.mpr ⟨m0, hm0R⟩
        refine ⟨h1, fun hneW => ?_⟩
        obtain ⟨m1, hm1, _, _⟩ := extract_mixing w j1 hj1Junk hr1 hneW
        have hm0NotMix : m0 ∉ mixing G C := by
          intro hmix
          have hneE := (Finset.mem_filter.mp hmix).2
          have he1 : orIn 11 C (opnd C m0 b1) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne1
          have he2 : orIn 11 C (opnd C m0 b2) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne2
          fin_cases b1 <;> fin_cases b2
          · exact hb12Ne rfl
          · exact hneE (propext ⟨fun _ => he2, fun _ => he1⟩)
          · exact hneE (propext ⟨fun _ => he1, fun _ => he2⟩)
          · exact hb12Ne rfl
        have hNe : m0 ≠ m1 := fun heq => hm0NotMix (heq ▸ hm1)
        have hSub : ({m0, m1} : Finset ℕ) ⊆ orN G C \ lam G C := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hm0R
          · exact hM_sub_R hm1
        have := Finset.card_le_card hSub
        rw [Finset.card_pair hNe] at this; exact this
  -- Dispatch on shared top t ∈ tops G C with InCone 11 C j1 t ∧ InCone 11 C j2 t!
  obtain ⟨t, htTop, hjt1, hjt2⟩ := hShared
  have htData := Finset.mem_filter.mp htTop
  have htLt : t < C.gates.length := Finset.mem_range.mp htData.1
  have htAnd : (gateAt C t).op = GateOp.and := htData.2.1
  have htBf : BelowF G C t := htData.2.2
  have side_sub_wmax (b : Fin 2) (j : ℕ) (hrj : OrReaches 11 C (opnd C t b) j) :
      orIn 11 C (opnd C t (1 - b)) ⊆ wmax G C j := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro x hgx hxw
    have hvb : val (List.ofFn x) (opnd C t b) = true := orReaches_val (opnd C t b) j x hrj hgx
    have hv1b : val (List.ofFn x) (opnd C t (1 - b)) = true := orIn_val hw hxw
    have htx : gateVal 11 C t x = true := by
      rw [gateVal_eq]
      refine (val_and (by simp) htLt htAnd).mpr ?_
      intro y hy
      rw [inputs_two htLt] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      fin_cases b
      · rcases hy with rfl | rfl
        · exact ⟨opnd_lt htLt 0, hvb⟩
        · exact ⟨opnd_lt htLt 1, hv1b⟩
      · rcases hy with rfl | rfl
        · exact ⟨opnd_lt htLt 0, hv1b⟩
        · exact ⟨opnd_lt htLt 1, hvb⟩
    exact htBf x htx
  obtain ⟨b1, hb1⟩ := inCone_to_orReaches t htTop j1 hj1Junk t (Or.inl rfl) hjt1
  obtain ⟨b2, hb2⟩ := inCone_to_orReaches t htTop j2 hj2Junk t (Or.inl rfl) hjt2
  by_cases htC : t ∈ centreless G C
  · have hZ1 : 1 ≤ (centreless G C).card := Finset.card_pos.mpr ⟨t, htC⟩
    by_cases hSameSide : b1 = b2
    · subst hSameSide
      have hR1 := (sameSide_orN (opnd C t b1) hb1 hb2).1
      have hWmax : orIn 11 C (opnd C t (1 - b1)) ⊆ wmax G C j1 ∩ wmax G C j2 :=
        Finset.subset_inter (side_sub_wmax b1 j1 hb1) (side_sub_wmax b1 j2 hb2)
      exact centrelessSameSide G C j1 j2 t b1 hEqG ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hsz hlt12 hjunkEq
        hno12 hno21 htC hb1 hb2 hWmax hZ1 hR1 (by omega) hBudget hCover
    · have hb2Eq : b2 = 1 - b1 := by
        fin_cases b1 <;> fin_cases b2
        · exact absurd rfl hSameSide
        · rfl
        · rfl
        · exact absurd rfl hSameSide
      subst hb2Eq
      exact centrelessOppSides G C j1 j2 t b1 hEqG ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hsz hlt12 hjunkEq
        hno12 hno21 htC hb1 hb2 hZ1 (by omega) hBudget hCover
  · -- t ∉ centreless G C: both sides nonempty!
    have hNeB : ∀ b : Fin 2, (orIn 11 C (opnd C t b)).Nonempty := by
      intro b
      by_contra hne
      apply htC
      refine Finset.mem_filter.mpr ⟨htTop, ?_⟩
      have he := Finset.not_nonempty_iff_eq_empty.mp hne
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    by_cases hSameSide : b1 = b2
    · subst hSameSide
      have hRge2 := (sameSide_orN (opnd C t b1) hb1 hb2).2 (hNeB b1)
      exact sameSideMixing G C j1 j2 t b1 hEqG ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hsz hlt12 hjunkEq
        hno12 hno21 (Finset.mem_sdiff.mpr ⟨htTop, htC⟩) hb1 hb2 hRge2 (by omega) hBudget hCover
    · by_cases hAlso : OrReaches 11 C (opnd C t b1) j2
      · have hRge2 := (sameSide_orN (opnd C t b1) hb1 hAlso).2 (hNeB b1)
        exact sameSideMixing G C j1 j2 t b1 hEqG ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hsz hlt12 hjunkEq
          hno12 hno21 (Finset.mem_sdiff.mpr ⟨htTop, htC⟩) hb1 hAlso hRge2 (by omega) hBudget hCover
      · have hb2Eq : b2 = 1 - b1 := by
          fin_cases b1 <;> fin_cases b2
          · exact absurd rfl hSameSide
          · rfl
          · rfl
          · exact absurd rfl hSameSide
        subst hb2Eq
        obtain ⟨m1, hm1, hr1m, hm1j1⟩ := extract_mixing (opnd C t b1) j1 hj1Junk hb1 (hNeB b1)
        obtain ⟨m2, hm2, hr2m, hm2j2⟩ := extract_mixing (opnd C t (1 - b1)) j2 hj2Junk hb2 (hNeB (1 - b1))
        have h12Ne : m1 ≠ m2 := by
          intro heq; subst heq
          exact hAlso (orReaches_trans (opnd C t b1) m1 j2 hr1m hm2j2)
        have hSub : ({m1, m2} : Finset ℕ) ⊆ orN G C \ lam G C := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hM_sub_R hm1
          · exact hM_sub_R hm2
        have hRge2 : 2 ≤ (orN G C \ lam G C).card := by
          have := Finset.card_le_card hSub
          rw [Finset.card_pair h12Ne] at this; exact this
        exact oppSidesCentred G C j1 j2 t b1 hEqG ⟨⟨hao, hrb, hlen2⟩, hfun, hmin⟩ htop hsz hlt12 hjunkEq
          hno12 hno21 (Finset.mem_sdiff.mpr ⟨htTop, htC⟩) hb1 hb2 hRge2 (by omega) hBudget hCover
