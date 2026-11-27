import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5230_511
    (fiveTops :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ),
        G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        g < h → junk G C = {g, h} → InCone 11 C g h →
        5 ≤ (tops G C).card)
    (chargeBound :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ),
        G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        g < h → junk G C = {g, h} → InCone 11 C g h →
        let U := Ustar G C
        C.size ≤ 21 → 4 ≤ U.card →
        (∀ u v : Fin 11, s(u, v) ∈ U →
          ∃ j ∈ junk G C,
            gateVal 11 C j (pairInput u v) = true ∧
            (u ∈ wmax G C j ∨ v ∈ wmax G C j)) →
        U.card ≤ (centreless G C).card + (orN G C \ lam G C).card + 1)
    (fiveExact :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ) (K : Finset (Fin 11)),
        G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
        IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        g < h → junk G C = {g, h} → InCone 11 C g h →
        let U := Ustar G C
        C.size = 21 → (tops G C).card = 5 → 4 ≤ U.card →
        U.card = (centreless G C).card + (orN G C \ lam G C).card + 1 →
        (∀ u v : Fin 11, s(u, v) ∈ U →
          ∃ j ∈ junk G C,
            gateVal 11 C j (pairInput u v) = true ∧
            (u ∈ wmax G C j ∨ v ∈ wmax G C j)) →
        IsMinCover (G.deleteEdges ↑U) K →
        7 ≤ K.card + U.card →
        K.card ≤ (tops G C \ centreless G C).card →
        False) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False) := by
  intro G inst C x4 x5 hG hLeast hTop hJunk hCone
  dsimp only
  intro _ hTrace hSize hU4 K hKMin hKU hKT _ hBudget
  let : DecidableEq GateOp := gateOpDecEq
  have hG' : G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] := hG
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp -congrConsts only [id (@List.foldl_cons)]
      have hlt : i < (stepWire w g).length := by simp -congrConsts [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp -congrConsts [stepWire, List.getElem?_append_left hi]
  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp -congrConsts [List.getElem?_eq_none hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp -congrConsts at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp -congrConsts [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp -congrConsts only [id (@List.getElem_cons_zero)]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp -congrConsts [stepWire]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp -congrConsts [stepWire]; omega)]
          simp -congrConsts [stepWire, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa -congrConsts using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp -congrConsts [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp -congrConsts only [id (@List.getElem_cons_succ)]
        rw [e]
        exact key
  let val (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
  have gateAt_eq {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    delta gateAt
    simp -congrConsts [hj]
  have gateAt_mem {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj
  have two_inputs {k : ℕ} (hk : k < C.gates.length) :
      ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < 11 + k ∧ q < 11 + k ∧ opnd C k 0 = p ∧
        opnd C k 1 = q := by
    obtain ⟨_, hRB, h2⟩ := hLeast.1
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
    exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp -congrConsts), hRB k hk q (by rw [hin]; simp -congrConsts),
      by delta opnd; simp -congrConsts [hin], by delta opnd; simp -congrConsts [hin]⟩
  have val_input (x : Fin 11 → Bool) (u : Fin 11) : val (List.ofFn x) u.val = x u := by
    change (C.gates.foldl stepWire (List.ofFn x)).getD u.val false = x u
    have hlt : u.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact u.isLt
    rw [foldl_getD_lt C.gates (List.ofFn x) u.val hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos u.isLt]
    rfl
  have val_gate {x : List Bool} (hx : x.length = 11) {j : ℕ} (hj : j < C.gates.length) :
      val x (11 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < 11 + j then val x i else false) := by
    rw [← hx, gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj
  have val_or {x : Fin 11 → Bool} {r : ℕ} (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val (List.ofFn x) (11 + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < 11 + r ∧ val (List.ofFn x) i = true := by
    rw [val_gate (by rw [List.length_ofFn]) hr, hop]
    delta GateOp.eval
    simp -congrConsts only [id (@List.any_map), id (@List.any_eq_true), id (@Function.comp_apply), id (@id_eq)]
    constructor
    · intro h
      rcases h with ⟨i, hi, h⟩
      by_cases hlt : i < 11 + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · intro h
      rcases h with ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
  have val_and {x : Fin 11 → Bool} {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) :
      gateVal 11 C a x = true ↔ val (List.ofFn x) (opnd C a 0) = true ∧ val (List.ofFn x) (opnd C a 1) = true := by
    obtain ⟨p, q, hpq, hp, hq, hop0, hop1⟩ := two_inputs ha
    change val (List.ofFn x) (11 + a) = true ↔ _
    rw [val_gate (by rw [List.length_ofFn]) ha, hop, hpq, hop0, hop1]
    delta GateOp.eval
    simp -congrConsts only [id (@List.map_cons), id (@List.map_nil), id (@List.all_cons), id (@List.all_nil), id (@Bool.and_true), id (@Bool.and_eq_true), id (@id_eq)]
    rw [ite_eq_left hp, ite_eq_left hq]
  have coneStep_eq (cs : List (List ℕ)) (g : Gate) :
      coneStep 11 cs g = cs ++ [(g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
        (fun w => (w - 11) :: cs.getD (w - 11) [])] := rfl
  have cones_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep 11) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [coneStep_eq]
      omega
  have cones_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep 11) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 11 ≤ w ∧ w < 11 + j ∧
          (i = w - 11 ∨ i ∈ (gs.foldl (coneStep 11) []).getD (w - 11) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 11) []).length = gs.length := by
        rw [cones_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (coneStep 11 (gs.foldl (coneStep 11) []) g).getD k [] =
            (gs.foldl (coneStep 11) []).getD k [] := by
        intro k hk
        simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · intro h0
          rcases h0 with ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp -congrConsts; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)]
          exact h3
        · intro h0
          rcases h0 with ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp -congrConsts
        have e2 : (coneStep 11 (gs.foldl (coneStep 11) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + gs.length))).flatMap
              (fun w => (w - 11) :: (gs.foldl (coneStep 11) []).getD (w - 11) []) := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_right (by omega)]
          simp -congrConsts [hlen]
        rw [e2, e1]
        simp -congrConsts only [id (@List.mem_flatMap), id (@List.mem_filter), id (@List.mem_cons), id (@decide_eq_true_eq)]
        constructor
        · intro h0
          rcases h0 with ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp -congrConsts, w, hw, h1, h2, ?_⟩
          rw [key (w - 11) (by omega)]
          exact h3
        · intro h0
          rcases h0 with ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - 11) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep 11 (gs.foldl (coneStep 11) []) g).getD j [] = [] := by
          simp -congrConsts only [coneStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · intro h0
          rcases h0 with ⟨h0, _⟩
          simp -congrConsts at h0
          omega
  have inCone_iff (i j : ℕ) :
      InCone 11 C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ 11 + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone 11 C i k) := by
    have h := cones_char C.gates i j
    delta InCone cones gateAt
    rw [h]
    constructor
    · intro h0
      rcases h0 with ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - 11, by omega, ?_, h3⟩
      have he : 11 + (w - 11) = w := by omega
      rw [he]
      exact hw
    · intro h0
      rcases h0 with ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, 11 + k, hw, by omega, by omega, ?_⟩
      have he : 11 + k - 11 = k := by omega
      rw [he]
      exact h3
  have coneStrict : ∀ k h, InCone 11 C h k → h < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro h hh
      obtain ⟨_, p, hp, _, hpath⟩ := (inCone_iff h k).mp hh
      rcases hpath with rfl | hpath
      · exact hp
      · exact (ih p hp h hpath).trans hp
  have inCone_trans : ∀ k i j, InCone 11 C i j → InCone 11 C j k → InCone 11 C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i j hij hjk
      obtain ⟨hk, p, hp, hin, hpath⟩ := (inCone_iff j k).mp hjk
      rcases hpath with rfl | hpath
      · exact (inCone_iff i k).mpr ⟨hk, j, hp, hin, Or.inr hij⟩
      · exact (inCone_iff i k).mpr ⟨hk, p, hp, hin, Or.inr (ih p hp i j hij hpath)⟩
  have hOrder : x4 < x5 := coneStrict x5 x4 hCone
  have orStep_eq (cs : List (List ℕ)) (g : Gate) :
      orStep 11 cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
          (fun w => cs.getD (w - 11) [])
        else [])] := rfl
  have orSets_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep 11) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp -congrConsts
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp -congrConsts [orStep_eq]
      omega
  have orSets_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep 11) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 11 ≤ w ∧ w < 11 + j ∧
            i ∈ (gs.foldl (orStep 11) []).getD (w - 11) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp -congrConsts
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 11) []).length = gs.length := by
        rw [orSets_len]; simp -congrConsts
      have key : ∀ k, k < gs.length →
          (orStep 11 (gs.foldl (orStep 11) []) g).getD k [] =
            (gs.foldl (orStep 11) []).getD k [] := by
        intro k hk
        simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp -congrConsts only [id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · intro h0
          rcases h0 with ⟨_, h3⟩
          refine ⟨by simp -congrConsts; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - 11) (by omega)]
            exact h3
        · intro h0
          rcases h0 with ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - 11) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp -congrConsts
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep 11 (gs.foldl (orStep 11) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + gs.length))).flatMap
                (fun w => (gs.foldl (orStep 11) []).getD (w - 11) []) := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_cons), id (@List.mem_flatMap), id (@List.mem_filter), id (@decide_eq_true_eq)]
          constructor
          · intro h0
            rcases h0 with h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩
            · exact ⟨by simp -congrConsts, Or.inl h3⟩
            · refine ⟨by simp -congrConsts, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - 11) (by omega)]
              exact h3
          · intro h0
            rcases h0 with ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - 11) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep 11 (gs.foldl (orStep 11) []) g).getD gs.length [] = [gs.length] := by
            simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
            rw [List.getElem?_append_right (by omega)]
            simp -congrConsts [hlen, hop]
          rw [e2]
          simp -congrConsts only [id (@List.mem_singleton)]
          constructor
          · intro h3
            exact ⟨by simp -congrConsts, Or.inl h3⟩
          · intro h0
            rcases h0 with ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep 11 (gs.foldl (orStep 11) []) g).getD j [] = [] := by
          simp -congrConsts only [orStep_eq, id (@List.getD_eq_getElem?_getD)]
          rw [List.getElem?_eq_none (by simp -congrConsts; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp -congrConsts at h0
        · intro h0
          rcases h0 with ⟨h0, _⟩
          simp -congrConsts at h0
          omega
  have orReaches_iff (k g : ℕ) :
      OrReaches 11 C (11 + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < 11 + k ∧ OrReaches 11 C i g)) := by
    have h := orSets_char C.gates g k
    delta OrReaches orSets gateAt
    have e : 11 + k - 11 = k := by omega
    rw [e, h]
    constructor
    · intro h0
      rcases h0 with ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · intro h0
      rcases h0 with ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
  have orReaches_eq_or_inCone : ∀ w j, OrReaches 11 C w j →
      w = 11 + j ∨ ∃ r < C.gates.length, w = 11 + r ∧ InCone 11 C j r := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro j hr
      have hnw : 11 ≤ w := hr.1
      obtain ⟨r, rfl⟩ : ∃ r, w = 11 + r := ⟨w - 11, by omega⟩
      obtain ⟨hrlen, h3⟩ := (orReaches_iff r j).mp hr
      rcases h3 with rfl | ⟨_, i, hin, hlt, hri⟩
      · exact Or.inl rfl
      · rcases ih i hlt j hri with rfl | ⟨r', _, rfl, hinc⟩
        · exact Or.inr ⟨r, hrlen, rfl, (inCone_iff j r).mpr ⟨hrlen, j, by omega, hin, Or.inl rfl⟩⟩
        · exact Or.inr ⟨r, hrlen, rfl, (inCone_iff j r).mpr ⟨hrlen, r', by omega, hin, Or.inr hinc⟩⟩
  have orReaches_inCone {a w j : ℕ} (ha : a < C.gates.length) (hw : w ∈ (gateAt C a).inputs)
      (hlt : w < 11 + a) (hr : OrReaches 11 C w j) : InCone 11 C j a := by
    rcases orReaches_eq_or_inCone w j hr with rfl | ⟨r, _, rfl, hinc⟩
    · exact (inCone_iff j a).mpr ⟨ha, j, by omega, hw, Or.inl rfl⟩
    · exact (inCone_iff j a).mpr ⟨ha, r, by omega, hw, Or.inr hinc⟩
  have orReaches_mono_val : ∀ w j (x : Fin 11 → Bool),
      OrReaches 11 C w j → gateVal 11 C j x = true → val (List.ofFn x) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro j x hr hjv
      have hnw : 11 ≤ w := hr.1
      obtain ⟨r, rfl⟩ : ∃ r, w = 11 + r := ⟨w - 11, by omega⟩
      obtain ⟨hrlen, h3⟩ := (orReaches_iff r j).mp hr
      rcases h3 with rfl | ⟨hop, i, hin, hlt, hri⟩
      · exact hjv
      · exact (val_or hrlen hop).mpr ⟨i, hin, hlt, ih i hlt j x hri hjv⟩
  have orIn_mono_val {w : ℕ} {u : Fin 11} {x : Fin 11 → Bool}
      (hu : u ∈ orIn 11 C w) (hxu : x u = true) : val (List.ofFn x) w = true := by
    delta orIn at hu
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)] at hu
    rcases hu with heq | ⟨k, hk, hr, hop, hin⟩
    · rw [← heq, val_input]; exact hxu
    · have hkv : gateVal 11 C k x = true :=
        (val_or hk hop).mpr ⟨u.val, hin, by have := u.isLt; omega, by rw [val_input]; exact hxu⟩
      exact orReaches_mono_val w k x hr hkv
  have wire_true_cases : ∀ w, w < 11 + C.gates.length → ∀ (x : Fin 11 → Bool),
      val (List.ofFn x) w = true →
      (∃ u ∈ orIn 11 C w, x u = true) ∨
      (∃ k < C.gates.length, OrReaches 11 C w k ∧ (gateAt C k).op = GateOp.and ∧ gateVal 11 C k x = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x hv
      by_cases hlt11 : w < 11
      · refine Or.inl ⟨⟨w, hlt11⟩, ?_, ?_⟩
        · delta orIn
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
        · have hvi := val_input x ⟨w, hlt11⟩
          rw [← hvi]
          exact hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hLeast.1.1 _ (gateAt_mem hk) with hand | hor
        · exact Or.inr ⟨k, hk, (orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩, hand, hv⟩
        · obtain ⟨i, hin, hilt, hiv⟩ := (val_or hk hor).mp hv
          rcases ih i hilt (by omega) x hiv with ⟨u, hu, hxu⟩ | ⟨m, hm, hrm, hmand, hmv⟩
          · refine Or.inl ⟨u, ?_, hxu⟩
            delta orIn at hu ⊢
            simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)] at hu ⊢
            rcases hu with heq | ⟨r, hr, hri, hrop, hrin⟩
            · exact Or.inr ⟨k, hk, (orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩, hor, heq ▸ hin⟩
            · exact Or.inr ⟨r, hr, (orReaches_iff k r).mpr ⟨hk, Or.inr ⟨hor, i, hin, hilt, hri⟩⟩, hrop, hrin⟩
          · exact Or.inr ⟨m, hm, (orReaches_iff k m).mpr ⟨hk, Or.inr ⟨hor, i, hin, hilt, hrm⟩⟩, hmand, hmv⟩
  have and_inCone_mem_junk {a k : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and)
      (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and) (hinc : InCone 11 C k a) :
      k ∈ junk G C := by
    have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb haand hinc
    delta BelowF at hnb
    have hdir : ∃ x : Fin 11 → Bool, gateVal 11 C k x = true ∧ graphFun G ∅ x = false := by
      by_contra hno
      apply hnb
      intro x hkx
      cases hgx : graphFun G ∅ x
      · exact (hno ⟨x, hkx, hgx⟩).elim
      · rfl
    delta junk gatesWhere
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)]
    exact ⟨hk, hkand, hk, hdir⟩
  have junk_mem_info {j : ℕ} (hj : j ∈ junk G C) :
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        ∃ x : Fin 11 → Bool, gateVal 11 C j x = true ∧ graphFun G ∅ x = false := by
    delta junk gatesWhere at hj
    simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)] at hj
    exact ⟨hj.1, hj.2.1, hj.2.2.2⟩
  have hx4_mem : x4 ∈ junk G C := by rw [hJunk]; exact Finset.mem_insert_self x4 {x5}
  have hx5_mem : x5 ∈ junk G C := by rw [hJunk]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self x5)
  obtain ⟨hx4_lt, hx4_and, hx4_dirty⟩ := junk_mem_info hx4_mem
  obtain ⟨hx5_lt, hx5_and, _⟩ := junk_mem_info hx5_mem
  have inCone_between_orReaches : ∀ r, r < C.gates.length →
      InCone 11 C x4 r → InCone 11 C r x5 → OrReaches 11 C (11 + r) x4 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrlen h4r hr5
      have hor : (gateAt C r).op = GateOp.or := by
        rcases hLeast.1.1 _ (gateAt_mem hrlen) with hand | hor
        · have hrj : r ∈ junk G C := and_inCone_mem_junk hx5_lt hx5_and hrlen hand hr5
          rw [hJunk] at hrj
          simp -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] at hrj
          have h1 : x4 < r := coneStrict r x4 h4r
          have h2 : r < x5 := coneStrict x5 r hr5
          omega
        · exact hor
      obtain ⟨_, p, hp, hin, hpath⟩ := (inCone_iff x4 r).mp h4r
      rcases hpath with rfl | h4p
      · exact (orReaches_iff r x4).mpr ⟨hrlen, Or.inr ⟨hor, 11 + x4, hin, by omega, (orReaches_iff x4 x4).mpr ⟨hx4_lt, Or.inl rfl⟩⟩⟩
      · have hp5 : InCone 11 C p x5 :=
          inCone_trans x5 p r ((inCone_iff p r).mpr ⟨hrlen, p, hp, hin, Or.inl rfl⟩) hr5
        exact (orReaches_iff r x4).mpr ⟨hrlen, Or.inr ⟨hor, 11 + p, hin, by omega, ih p hp (by omega) h4p hp5⟩⟩
  have hx5_orReaches_x4 : ∃ d : Fin 2, OrReaches 11 C (opnd C x5 d) x4 := by
    obtain ⟨_, p, hp, hin, hpath⟩ := (inCone_iff x4 x5).mp hCone
    obtain ⟨q0, q1, hqs, _, _, hq0, hq1⟩ := two_inputs hx5_lt
    have hreach : OrReaches 11 C (11 + p) x4 := by
      rcases hpath with rfl | h4p
      · exact (orReaches_iff x4 x4).mpr ⟨hx4_lt, Or.inl rfl⟩
      · exact inCone_between_orReaches p (by omega) h4p ((inCone_iff p x5).mpr ⟨hx5_lt, p, hp, hin, Or.inl rfl⟩)
    rw [hqs] at hin
    simp -congrConsts only [id (@List.mem_cons), id (@List.not_mem_nil), id (@or_false)] at hin
    rcases hin with h0 | h1
    · exact ⟨0, by rw [hq0, ← h0]; exact hreach⟩
    · exact ⟨1, by rw [hq1, ← h1]; exact hreach⟩
  have opnd_pair {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
      ∃ b' : Fin 2,
        opnd C a b' ∈ (gateAt C a).inputs ∧ opnd C a b' < 11 + a ∧
        (∀ x : Fin 11 → Bool, (gateAt C a).op = GateOp.and →
          (gateVal 11 C a x = true ↔ val (List.ofFn x) (opnd C a b) = true ∧ val (List.ofFn x) (opnd C a b') = true)) := by
    obtain ⟨p, q, hpq, hp, hq, hop0, hop1⟩ := two_inputs ha
    rcases b with ⟨bv, hbv⟩
    cases bv with
    | zero =>
      refine ⟨1, by rw [hop1, hpq]; simp -congrConsts, by rw [hop1]; exact hq, ?_⟩
      intro x hand
      exact val_and ha hand
    | succ bv' =>
      have hbv0 : bv' = 0 := by omega
      subst hbv0
      refine ⟨0, by rw [hop0, hpq]; simp -congrConsts, by rw [hop0]; exact hp, ?_⟩
      intro x hand
      exact (val_and (x := x) ha hand).trans and_comm
  have hWmax : ∀ u v : Fin 11, s(u, v) ∈ Ustar G C →
      ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true ∧
        (u ∈ wmax G C j ∨ v ∈ wmax G C j) := by
    intro u v huv
    obtain ⟨a, ha, b, j, hj, hav, hraj, hjv⟩ := hTrace u v huv
    have ha_info : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
      delta tops gatesWhere at ha
      simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_range)] at ha
      exact ⟨ha.1, ha.2.1, ha.2.2⟩
    obtain ⟨ha_lt, ha_and, ha_below⟩ := ha_info
    obtain ⟨b', hb'in, hb'lt, hand_iff⟩ := opnd_pair ha_lt b
    have hb'v : val (List.ofFn (pairInput u v)) (opnd C a b') = true :=
      ((hand_iff (pairInput u v) ha_and).mp hav).2
    rcases wire_true_cases (opnd C a b') (by omega) (pairInput u v) hb'v with
        ⟨z, hz, hzu⟩ | ⟨k, hk_lt, hrak, hk_and, hkv⟩
    · have hzw : z ∈ wmax G C j := by
        delta wmax
        simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)]
        intro x hjx hxz
        have h1 : val (List.ofFn x) (opnd C a b) = true := orReaches_mono_val _ j x hraj hjx
        have h2 : val (List.ofFn x) (opnd C a b') = true := orIn_mono_val hz hxz
        exact ha_below x ((hand_iff x ha_and).mpr ⟨h1, h2⟩)
      have hzeq : z = u ∨ z = v := of_decide_eq_true hzu
      exact ⟨j, hj, hjv, hzeq.elim (fun h => Or.inl (h ▸ hzw)) (fun h => Or.inr (h ▸ hzw))⟩
    · have hk_junk : k ∈ junk G C :=
        and_inCone_mem_junk ha_lt ha_and hk_lt hk_and (orReaches_inCone ha_lt hb'in hb'lt hrak)
      have hjk_ne : j ≠ k := by
        intro hjk
        subst hjk
        obtain ⟨_, _, x, hjx, hfx⟩ := junk_mem_info hj
        have h1 : val (List.ofFn x) (opnd C a b) = true := orReaches_mono_val _ j x hraj hjx
        have h2 : val (List.ofFn x) (opnd C a b') = true := orReaches_mono_val _ j x hrak hjx
        have htx : graphFun G ∅ x = true := ha_below x ((hand_iff x ha_and).mpr ⟨h1, h2⟩)
        rw [hfx] at htx
        cases htx
      have hboth : gateVal 11 C x4 (pairInput u v) = true ∧ gateVal 11 C x5 (pairInput u v) = true ∧
          ∀ x : Fin 11 → Bool, gateVal 11 C x4 x = true → gateVal 11 C x5 x = true → graphFun G ∅ x = true := by
        have hj45 : j = x4 ∨ j = x5 := by
          rw [hJunk] at hj
          simpa -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] using hj
        have hk45 : k = x4 ∨ k = x5 := by
          rw [hJunk] at hk_junk
          simpa -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] using hk_junk
        rcases hj45 with hj4 | hj5 <;> rcases hk45 with hk4 | hk5
        · exact (hjk_ne (hj4.trans hk4.symm)).elim
        · rw [hj4] at hjv hraj
          rw [hk5] at hkv hrak
          exact ⟨hjv, hkv, fun x h4 h5 => ha_below x ((hand_iff x ha_and).mpr
            ⟨orReaches_mono_val _ x4 x hraj h4, orReaches_mono_val _ x5 x hrak h5⟩)⟩
        · rw [hj5] at hjv hraj
          rw [hk4] at hkv hrak
          exact ⟨hkv, hjv, fun x h4 h5 => ha_below x ((hand_iff x ha_and).mpr
            ⟨orReaches_mono_val _ x5 x hraj h5, orReaches_mono_val _ x4 x hrak h4⟩)⟩
        · exact (hjk_ne (hj5.trans hk5.symm)).elim
      obtain ⟨hx4v, hx5v, h45_below⟩ := hboth
      obtain ⟨d, hdreach⟩ := hx5_orReaches_x4
      obtain ⟨d', hd'in, hd'lt, hx5_iff⟩ := opnd_pair hx5_lt d
      have hd'v : val (List.ofFn (pairInput u v)) (opnd C x5 d') = true :=
        ((hx5_iff (pairInput u v) hx5_and).mp hx5v).2
      rcases wire_true_cases (opnd C x5 d') (by omega) (pairInput u v) hd'v with
          ⟨z, hz, hzu⟩ | ⟨m, hm_lt, hrm, hm_and, _⟩
      · have hzw : z ∈ wmax G C x4 := by
          delta wmax
          simp -congrConsts only [id (@Finset.mem_filter), id (@Finset.mem_univ), id (@true_and)]
          intro x h4x hxz
          have h1 : val (List.ofFn x) (opnd C x5 d) = true := orReaches_mono_val _ x4 x hdreach h4x
          have h2 : val (List.ofFn x) (opnd C x5 d') = true := orIn_mono_val hz hxz
          have h5x : gateVal 11 C x5 x = true := (hx5_iff x hx5_and).mpr ⟨h1, h2⟩
          exact h45_below x h4x h5x
        have hzeq : z = u ∨ z = v := of_decide_eq_true hzu
        exact ⟨x4, hx4_mem, hx4v, hzeq.elim (fun h => Or.inl (h ▸ hzw)) (fun h => Or.inr (h ▸ hzw))⟩
      · have hm_cone : InCone 11 C m x5 := orReaches_inCone hx5_lt hd'in hd'lt hrm
        have hm_junk : m ∈ junk G C := and_inCone_mem_junk hx5_lt hx5_and hm_lt hm_and hm_cone
        have hm_lt5 : m < x5 := coneStrict x5 m hm_cone
        have hm_eq4 : m = x4 := by
          rw [hJunk] at hm_junk
          simp -congrConsts only [id (@Finset.mem_insert), id (@Finset.mem_singleton)] at hm_junk
          omega
        rw [hm_eq4] at hrm
        obtain ⟨x, h4x, hfx⟩ := hx4_dirty
        have h1 : val (List.ofFn x) (opnd C x5 d) = true := orReaches_mono_val _ x4 x hdreach h4x
        have h2 : val (List.ofFn x) (opnd C x5 d') = true := orReaches_mono_val _ x4 x hrm h4x
        have h5x : gateVal 11 C x5 x = true := (hx5_iff x hx5_and).mpr ⟨h1, h2⟩
        have htx : graphFun G ∅ x = true := h45_below x h4x h5x
        rw [hfx] at htx
        cases htx
  have hFive : 5 ≤ (tops G C).card := fiveTops G C x4 x5 hG' hLeast hTop hOrder hJunk hCone
  have hCharge : (Ustar G C).card ≤ (centreless G C).card + (orN G C \ lam G C).card + 1 :=
    chargeBound G C x4 x5 hG' hLeast hTop hOrder hJunk hCone hSize hU4 hWmax
  have hSub : (tops G C \ centreless G C).card + (centreless G C).card = (tops G C).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hSize21 : C.size = 21 := by omega
  have hT5 : (tops G C).card = 5 := by omega
  have hUEq : (Ustar G C).card = (centreless G C).card + (orN G C \ lam G C).card + 1 := by omega
  exact fiveExact G C x4 x5 K hG' hLeast hTop hOrder hJunk hCone hSize21 hT5 hU4 hUEq hWmax hKMin hKU hKT
