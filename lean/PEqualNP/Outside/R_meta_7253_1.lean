import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_7253_1
    (h1 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;           have x10 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x11 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x12 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           PEqualNP.TopForm.mixing x1 x3 = ∅ → (1 : ℕ) ≤ x12.card → (1 : ℕ) ≤ x9.card → (2 : ℕ) ≤ x10.card → (4 : ℕ) ≤ x11.card → (x8 \ x9).card + (2 : ℕ) * x9.card + x10.card + x12.card ≤ (13 : ℕ) + x11.card → (52 : ℕ) ≤ (4 : ℕ) * (x8 \ x9).card + x11.card → (∀ (x18 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x18 → x18.card ≤ (x8 \ x9).card) → False)
    (h2 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;           have x10 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x11 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x12 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card → (1 : ℕ) ≤ x9.card → (2 : ℕ) ≤ x10.card → (4 : ℕ) ≤ x11.card → (x8 \ x9).card + (2 : ℕ) * x9.card + x10.card + x12.card ≤ (13 : ℕ) + x11.card → (52 : ℕ) ≤ (4 : ℕ) * (x8 \ x9).card + x11.card → (∀ (x18 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x18 → x18.card ≤ (x8 \ x9).card) → False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;           have x10 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x11 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x12 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           (1 : ℕ) ≤ x9.card → (2 : ℕ) ≤ x10.card → (4 : ℕ) ≤ x11.card → (x8 \ x9).card + (2 : ℕ) * x9.card + x10.card + x12.card ≤ (13 : ℕ) + x11.card → (52 : ℕ) ≤ (4 : ℕ) * (x8 \ x9).card + x11.card → (∀ (x18 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x18 → x18.card ≤ (x8 \ x9).card) → False := by
  intro G inst C hG hL hT hs
  let _ : DecidableEq GateOp := gateOpDecEq
  dsimp only
  intro hc hj hu hbud hcov hmin
  by_cases hmix : (mixing G C).Nonempty
  · exact h2 G C hG hL hT hs (Finset.card_pos.mpr hmix) hc hj hu hbud hcov hmin
  have hmix0 : mixing G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hmix
  by_cases hR : (orN G C \ lam G C).Nonempty
  · exact h1 G C hG hL hT hs hmix0 (Finset.card_pos.mpr hR) hc hj hu hbud hcov hmin
  have hR0 : orN G C \ lam G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
  have hRsub : ∀ k, k ∈ orN G C → k ∈ lam G C := by
    intro k hk
    by_contra hn
    have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk, hn⟩
    rw [hR0] at hm
    exact Finset.notMem_empty k hm
  let PG23 : SimpleGraph (Fin 26) :=
    SimpleGraph.fromRel fun (x4 x5 : Fin 26) =>
      (x4 : ℕ) < 13 ∧ 13 ≤ (x5 : ℕ) ∧ ((x4 : ℕ) + 26 - (x5 : ℕ)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  change G = PG23 at hG
  subst hG
  have hBip : ∀ u v : Fin 26, PG23.Adj u v → decide (u.val < 13) ≠ decide (v.val < 13) := by
    intro u v huv
    rcases huv with ⟨_, ⟨hu, hv, _⟩ | ⟨hv, hu, _⟩⟩
    · simp [hu, show ¬ v.val < 13 by omega]
    · simp [hv, show ¬ u.val < 13 by omega]
  have hDiff : ∀ d1 ∈ ([0, 1, 3, 9] : List ℕ), ∀ d2 ∈ ([0, 1, 3, 9] : List ℕ),
      ∀ d3 ∈ ([0, 1, 3, 9] : List ℕ), ∀ d4 ∈ ([0, 1, 3, 9] : List ℕ),
      d1 ≠ d2 → d1 ≠ d3 → (d1 + 13 - d2) % 13 ≠ (d3 + 13 - d4) % 13 := by
    decide
  have hNoFour : NoFourCycle PG23 := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    by_contra hne
    have hneVal : w1.val ≠ w2.val := fun h => hne (Fin.ext h)
    have habVal : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hlt_a := a.isLt; have hlt_b := b.isLt; have hlt_1 := w1.isLt; have hlt_2 := w2.isLt
    rcases h1.1 with ⟨_, ⟨ha1, hw1_ge, hd1⟩ | ⟨hw1_lt, ha1_ge, hd1⟩⟩
    · rcases h1.2 with ⟨_, ⟨hb1, _, hd2⟩ | ⟨hw1_lt, _, _⟩⟩
      · rcases h2.1 with ⟨_, ⟨_, hw2_ge, hd3⟩ | ⟨_, ha_ge, _⟩⟩
        · rcases h2.2 with ⟨_, ⟨_, _, hd4⟩ | ⟨_, hb_ge, _⟩⟩
          · have h12 : (a.val + 26 - w1.val) % 13 ≠ (b.val + 26 - w1.val) % 13 := by omega
            have h13 : (a.val + 26 - w1.val) % 13 ≠ (a.val + 26 - w2.val) % 13 := by omega
            have hmod := hDiff _ hd1 _ hd2 _ hd3 _ hd4 h12 h13
            omega
          · omega
        · omega
      · omega
    · rcases h1.2 with ⟨_, ⟨hb1, _, _⟩ | ⟨_, hb1_ge, hd2⟩⟩
      · omega
      · rcases h2.1 with ⟨_, ⟨ha2, _, _⟩ | ⟨hw2_lt, _, hd3⟩⟩
        · omega
        · rcases h2.2 with ⟨_, ⟨hb2, _, _⟩ | ⟨_, _, hd4⟩⟩
          · omega
          · have h12 : (w1.val + 26 - a.val) % 13 ≠ (w1.val + 26 - b.val) % 13 := by omega
            have h13 : (w1.val + 26 - a.val) % 13 ≠ (w2.val + 26 - a.val) % 13 := by omega
            have hmod := hDiff _ hd1 _ hd2 _ hd3 _ hd4 h12 h13
            omega
  have pi_left : ∀ u v : Fin 26, pairInput u v u = true := by
    intro u v; unfold pairInput; exact decide_eq_true (Or.inl rfl)
  have pi_right : ∀ u v : Fin 26, pairInput u v v = true := by
    intro u v; unfold pairInput; exact decide_eq_true (Or.inr rfl)
  have pi_iff : ∀ u v t : Fin 26, pairInput u v t = true ↔ t = u ∨ t = v := by
    intro u v t; unfold pairInput; rw [decide_eq_true_eq]
  have pi_comm : ∀ u v : Fin 26, pairInput u v = pairInput v u := by
    intro u v; funext w; unfold pairInput; exact decide_eq_decide.mpr or_comm
  have hGfun_pair : ∀ u v : Fin 26, graphFun PG23 ∅ (pairInput u v) = true ↔ PG23.Adj u v := by
    intro u v
    unfold graphFun
    rw [decide_eq_false (by rintro ⟨a, ha, _⟩; exact Finset.notMem_empty a ha), Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases (pi_iff u v a).mp ha with hau | hav <;> rcases (pi_iff u v b).mp hb with hbu | hbv
      · rw [hau, hbu] at hab; exact (PG23.irrefl hab).elim
      · rw [hau, hbv] at hab; exact hab
      · rw [hav, hbu] at hab; exact hab.symm
      · rw [hav, hbv] at hab; exact (PG23.irrefl hab).elim
    · intro huv
      exact ⟨u, v, huv, pi_left u v, pi_right u v⟩
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ), j < gs.length →
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs.getD j ⟨GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro w j hj; simp at hj
    | append_singleton gs g ih =>
      intro w j hj
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen := foldl_len gs w
      simp only [List.length_append, List.length_singleton] at hj
      have key : ∀ i, i < w.length + gs.length →
          (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
        intro i hi
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        change ((gs.foldl stepW w) ++ [_])[i]?.getD false = _
        rw [List.getElem?_append_left (by rw [hlen]; exact hi)]
      rcases Nat.lt_or_ge j gs.length with h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [e1, key _ (by omega), ih w j h]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i (by omega)]
        · rfl
      · have hj' : j = gs.length := by omega
        subst hj'
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
            g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
          rw [List.getD_eq_getElem?_getD]
          change ((gs.foldl stepW w) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false)])[w.length + gs.length]?.getD false = _
          rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
          rfl
        rw [e2]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i hi]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by rw [hlen]; omega)]
          rfl
  have hgate_mem : ∀ {j : ℕ}, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    have h1 : gateAt C j = C.gates[j] := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [h1]
    exact List.getElem_mem hj
  have hinputs_eq : ∀ {j : ℕ}, j < C.gates.length →
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    intro j hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 _ (hgate_mem hj))
    unfold opnd
    rw [hab]
    rfl
  have hopnd_lt : ∀ {j : ℕ}, j < C.gates.length → ∀ b : Fin 2, opnd C j b < 26 + j := by
    intro j hj b
    have hmem : opnd C j b ∈ (gateAt C j).inputs := by
      rw [hinputs_eq hj]
      fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    exact hL.1.2.1 j hj (opnd C j b) hmem
  have wv_input : ∀ (x : Fin 26 → Bool) (u : Fin 26), wireVal 26 C u.val x = x u := by
    intro x u
    unfold wireVal
    change (C.gates.foldl stepW (List.ofFn x)).getD u.val false = x u
    rw [foldl_getD_lt _ _ _ (by rw [List.length_ofFn]; exact u.isLt)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    rw [dif_pos u.isLt]
    rfl
  have gateVal_rec : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      gateVal 26 C j x =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal 26 C i x) := by
    intro x j hj
    unfold gateVal gateAt wireVal
    have h := foldl_gate C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at h
    change (C.gates.foldl stepW (List.ofFn x)).getD (26 + j) false = _
    rw [h]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt : i < 26 + j := hL.1.2.1 j hj i hi
    rw [ite_eq_left hlt]
    rfl
  have eval_and : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have eval_or : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have and_eval : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      (gateAt C j).op = GateOp.and →
      (gateVal 26 C j x = true ↔
        wireVal 26 C (opnd C j 0) x = true ∧ wireVal 26 C (opnd C j 1) x = true) := by
    intro x j hj hop
    rw [gateVal_rec x j hj, hop, hinputs_eq hj]
    change GateOp.and.eval [wireVal 26 C (opnd C j 0) x, wireVal 26 C (opnd C j 1) x] = true ↔ _
    rw [eval_and, Bool.and_eq_true]
  have or_eval : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      (gateAt C j).op = GateOp.or →
      (gateVal 26 C j x = true ↔
        wireVal 26 C (opnd C j 0) x = true ∨ wireVal 26 C (opnd C j 1) x = true) := by
    intro x j hj hop
    rw [gateVal_rec x j hj, hop, hinputs_eq hj]
    change GateOp.or.eval [wireVal 26 C (opnd C j 0) x, wireVal 26 C (opnd C j 1) x] = true ↔ _
    rw [eval_or, Bool.or_eq_true]
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]
      omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep 26) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 26 ≤ w ∧ w < 26 + j ∧
          (i = w - 26 ∨ i ∈ (gs.foldl (coneStep 26) []).getD (w - 26) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep 26) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep 26 (gs.foldl (coneStep 26) []) g).getD k [] =
            (gs.foldl (coneStep 26) []).getD k [] := by
        intro k hk
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        change ((gs.foldl (coneStep 26) []) ++ [_])[k]?.getD [] = _
        rw [List.getElem?_append_left (by rw [hlen]; exact hk)]
      simp only [List.length_append, List.length_singleton]
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [key j h, ih i j]
        have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [e1]
        constructor
        · rintro ⟨_, w, hw, hge, hlt, hm⟩
          refine ⟨by omega, w, hw, hge, hlt, ?_⟩
          rw [key (w - 26) (by omega)]
          exact hm
        · rintro ⟨_, w, hw, hge, hlt, hm⟩
          rw [key (w - 26) (by omega)] at hm
          exact ⟨h, w, hw, hge, hlt, hm⟩
      · rcases Nat.eq_or_lt_of_le h with rfl | hgt
        · have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD]
          rw [e1]
          have e2 : (coneStep 26 (gs.foldl (coneStep 26) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + gs.length))).flatMap
                (fun w => (w - 26) :: (gs.foldl (coneStep 26) []).getD (w - 26) []) := by
            rw [List.getD_eq_getElem?_getD]
            change ((gs.foldl (coneStep 26) []) ++ [_])[gs.length]?.getD [] = _
            rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
            rfl
          rw [e2]
          simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
          constructor
          · rintro ⟨w, ⟨hw, hge, hlt⟩, hm⟩
            refine ⟨by omega, w, hw, hge, hlt, ?_⟩
            rw [key (w - 26) (by omega)]
            exact hm
          · rintro ⟨_, w, hw, hge, hlt, hm⟩
            rw [key (w - 26) (by omega)] at hm
            exact ⟨w, ⟨hw, hge, hlt⟩, hm⟩
        · have hge2 : (coneStep 26 (gs.foldl (coneStep 26) []) g).length ≤ j := by
            change ((gs.foldl (coneStep 26) []) ++ [_]).length ≤ j
            rw [List.length_append, List.length_singleton, hlen]
            omega
          have hnone : (coneStep 26 (gs.foldl (coneStep 26) []) g).getD j [] = [] := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
          rw [hnone]
          simp only [List.not_mem_nil, false_iff]
          rintro ⟨h1, _⟩
          omega
  have inCone_iff : ∀ i j : ℕ, InCone 26 C i j ↔
      j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧ w < 26 + j ∧
        (i = w - 26 ∨ InCone 26 C i (w - 26)) := by
    intro i j
    exact cones_char C.gates i j
  have inCone_lt : ∀ {i j : ℕ}, InCone 26 C i j → i < j := by
    intro i j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro h
      obtain ⟨_, w, _, hge, hlt, hm⟩ := (inCone_iff i j).mp h
      rcases hm with rfl | h'
      · omega
      · have := ih (w - 26) (by omega) h'
        omega
  have inCone_trans : ∀ {i j k : ℕ}, InCone 26 C i j → InCone 26 C j k → InCone 26 C i k := by
    intro i j k hij hjk
    induction k using Nat.strongRecOn with
    | ind k ih =>
      obtain ⟨hk, w, hw, hge, hlt, hm⟩ := (inCone_iff j k).mp hjk
      refine (inCone_iff i k).mpr ⟨hk, w, hw, hge, hlt, Or.inr ?_⟩
      rcases hm with rfl | h'
      · exact hij
      · exact ih (w - 26) (by omega) h'
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]
      omega
  have orSets_char : ∀ (gs : List Gate) (j g : ℕ),
      g ∈ (gs.foldl (orStep 26) []).getD j [] ↔
        j < gs.length ∧ (g = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 26 ≤ w ∧ w < 26 + j ∧
            g ∈ (gs.foldl (orStep 26) []).getD (w - 26) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro j g; simp
    | append_singleton gs gt ih =>
      intro j g
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep 26) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep 26 (gs.foldl (orStep 26) []) gt).getD k [] =
            (gs.foldl (orStep 26) []).getD k [] := by
        intro k hk
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        change ((gs.foldl (orStep 26) []) ++ [_])[k]?.getD [] = _
        rw [List.getElem?_append_left (by rw [hlen]; exact hk)]
      simp only [List.length_append, List.length_singleton]
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [key j h, ih j g]
        have e1 : (gs ++ [gt]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [e1]
        constructor
        · rintro ⟨_, rfl | ⟨hop, w, hw, hge, hlt, hm⟩⟩
          · exact ⟨by omega, Or.inl rfl⟩
          · refine ⟨by omega, Or.inr ⟨hop, w, hw, hge, hlt, ?_⟩⟩
            rw [key (w - 26) (by omega)]
            exact hm
        · rintro ⟨_, rfl | ⟨hop, w, hw, hge, hlt, hm⟩⟩
          · exact ⟨h, Or.inl rfl⟩
          · rw [key (w - 26) (by omega)] at hm
            exact ⟨h, Or.inr ⟨hop, w, hw, hge, hlt, hm⟩⟩
      · rcases Nat.eq_or_lt_of_le h with rfl | hgt
        · have e1 : (gs ++ [gt]).getD gs.length ⟨GateOp.or, []⟩ = gt := by
            simp [List.getD_eq_getElem?_getD]
          rw [e1]
          have e2 : (orStep 26 (gs.foldl (orStep 26) []) gt).getD gs.length [] =
              gs.length :: (if gt.op = GateOp.or then
                (gt.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + gs.length))).flatMap
                  (fun w => (gs.foldl (orStep 26) []).getD (w - 26) [])
                else []) := by
            rw [List.getD_eq_getElem?_getD]
            change ((gs.foldl (orStep 26) []) ++ [_])[gs.length]?.getD [] = _
            rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
            rfl
          rw [e2]
          simp only [List.mem_cons]
          by_cases hop : gt.op = GateOp.or
          · simp only [hop, ↓reduceIte, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
            constructor
            · rintro (rfl | ⟨w, ⟨hw, hge, hlt⟩, hm⟩)
              · exact ⟨by omega, Or.inl rfl⟩
              · refine ⟨by omega, Or.inr ⟨trivial, w, hw, hge, hlt, ?_⟩⟩
                rw [key (w - 26) (by omega)]
                exact hm
            · rintro ⟨_, rfl | ⟨_, w, hw, hge, hlt, hm⟩⟩
              · exact Or.inl rfl
              · rw [key (w - 26) (by omega)] at hm
                exact Or.inr ⟨w, ⟨hw, hge, hlt⟩, hm⟩
          · simp only [hop, ↓reduceIte, List.not_mem_nil, or_false, false_and]
            constructor
            · rintro rfl; exact ⟨by omega, rfl⟩
            · rintro ⟨_, rfl⟩; rfl
        · have hge2 : (orStep 26 (gs.foldl (orStep 26) []) gt).length ≤ j := by
            change ((gs.foldl (orStep 26) []) ++ [_]).length ≤ j
            rw [List.length_append, List.length_singleton, hlen]
            omega
          have hnone : (orStep 26 (gs.foldl (orStep 26) []) gt).getD j [] = [] := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
          rw [hnone]
          simp only [List.not_mem_nil, false_iff]
          rintro ⟨h1, _⟩
          omega
  have orReaches_iff : ∀ j g : ℕ, OrReaches 26 C (26 + j) g ↔
      j < C.gates.length ∧ (g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧ w < 26 + j ∧ OrReaches 26 C w g)) := by
    intro j g
    unfold OrReaches orSets
    have hsub : 26 + j - 26 = j := by omega
    rw [hsub]
    simp only [Nat.le_add_right, true_and]
    rw [orSets_char C.gates j g]
    constructor
    · rintro ⟨hj, rfl | ⟨hop, w, hw, hge, hlt, hm⟩⟩
      · exact ⟨hj, Or.inl rfl⟩
      · exact ⟨hj, Or.inr ⟨hop, w, hw, hge, hlt, hge, hm⟩⟩
    · rintro ⟨hj, rfl | ⟨hop, w, hw, hge, hlt, _, hm⟩⟩
      · exact ⟨hj, Or.inl rfl⟩
      · exact ⟨hj, Or.inr ⟨hop, w, hw, hge, hlt, hm⟩⟩
  have orReaches_trans_j : ∀ j k g : ℕ,
      OrReaches 26 C (26 + j) k → OrReaches 26 C (26 + k) g → OrReaches 26 C (26 + j) g := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro k g hjk hkg
      obtain ⟨hj, hdisj⟩ := (orReaches_iff j k).mp hjk
      rcases hdisj with rfl | ⟨hop, u, hu, huge, hult, huk⟩
      · exact hkg
      · refine (orReaches_iff j g).mpr ⟨hj, Or.inr ⟨hop, u, hu, huge, hult, ?_⟩⟩
        have hEq : 26 + (u - 26) = u := by omega
        rw [← hEq] at huk ⊢
        exact ih (u - 26) (by omega) k g huk hkg
  have orReaches_trans : ∀ {w k g : ℕ},
      OrReaches 26 C w k → OrReaches 26 C (26 + k) g → OrReaches 26 C w g := by
    intro w k g hwk hkg
    have hEq : 26 + (w - 26) = w := by have := hwk.1; omega
    rw [← hEq] at hwk ⊢
    exact orReaches_trans_j (w - 26) k g hwk hkg
  have orIn_lt : ∀ (u : Fin 26), orIn 26 C u.val = {u} := by
    intro u
    ext t
    unfold orIn
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h | ⟨k, _, hr, _, _⟩⟩
      · exact Fin.ext h
      · have := hr.1; have := u.isLt; omega
    · rintro rfl; exact ⟨Finset.mem_univ _, Or.inl rfl⟩
  have orIn_and : ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.and →
      orIn 26 C (26 + j) = ∅ := by
    intro j hj hop
    ext t
    unfold orIn
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro (h | ⟨k, _, hr, hkop, _⟩)
    · have := t.isLt; omega
    · obtain ⟨_, rfl | ⟨hor, _⟩⟩ := (orReaches_iff j k).mp hr
      · rw [hop] at hkop; cases hkop
      · rw [hop] at hor; cases hor
  have orIn_or : ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.or →
      orIn 26 C (26 + j) = orIn 26 C (opnd C j 0) ∪ orIn 26 C (opnd C j 1) := by
    intro j hj hop
    ext t
    unfold orIn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨k, hk, hr, hkop, ht⟩)
      · have := t.isLt; omega
      · obtain ⟨_, rfl | ⟨_, w, hw, _, _, hwk⟩⟩ := (orReaches_iff j k).mp hr
        · rw [hinputs_eq hj] at ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with h0 | h1
          · exact Or.inl (Or.inl h0)
          · exact Or.inr (Or.inl h1)
        · rw [hinputs_eq hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact Or.inl (Or.inr ⟨k, hk, hwk, hkop, ht⟩)
          · exact Or.inr (Or.inr ⟨k, hk, hwk, hkop, ht⟩)
    · rintro ((h0 | ⟨k, hk, hr, hkop, ht⟩) | (h1 | ⟨k, hk, hr, hkop, ht⟩))
      · refine Or.inr ⟨j, hj, (orReaches_iff j j).mpr ⟨hj, Or.inl rfl⟩, hop, ?_⟩
        rw [hinputs_eq hj, h0]; exact List.mem_cons_self
      · refine Or.inr ⟨k, hk, ?_, hkop, ht⟩
        refine (orReaches_iff j k).mpr ⟨hj, Or.inr ⟨hop, opnd C j 0, ?_, hr.1, hopnd_lt hj 0, hr⟩⟩
        rw [hinputs_eq hj]; exact List.mem_cons_self
      · refine Or.inr ⟨j, hj, (orReaches_iff j j).mpr ⟨hj, Or.inl rfl⟩, hop, ?_⟩
        rw [hinputs_eq hj, h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · refine Or.inr ⟨k, hk, ?_, hkop, ht⟩
        refine (orReaches_iff j k).mpr ⟨hj, Or.inr ⟨hop, opnd C j 1, ?_, hr.1, hopnd_lt hj 1, hr⟩⟩
        rw [hinputs_eq hj]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have orIn_mono_reach : ∀ {w k : ℕ}, OrReaches 26 C w k →
      ∀ t ∈ orIn 26 C (26 + k), t ∈ orIn 26 C w := by
    intro w k hwk t ht
    unfold orIn at ht ⊢
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ t, ?_⟩
    rcases ht.2 with h | ⟨m, hm, hkm, hmop, htm⟩
    · have := t.isLt; omega
    · exact Or.inr ⟨m, hm, orReaches_trans hwk hkm, hmop, htm⟩
  have orIn_sound : ∀ (x : Fin 26 → Bool) (w : ℕ) (t : Fin 26),
      t ∈ orIn 26 C w → x t = true → wireVal 26 C w x = true := by
    intro x w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro t ht hxt
      by_cases hlt : w < 26
      · have ht' : t = ⟨w, hlt⟩ := by
          rw [show w = (⟨w, hlt⟩ : Fin 26).val from rfl, orIn_lt ⟨w, hlt⟩] at ht
          exact Finset.mem_singleton.mp ht
        subst ht'
        rw [wv_input x ⟨w, hlt⟩]
        exact hxt
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        by_cases hj : j < C.gates.length
        · rcases hL.1.1 _ (hgate_mem hj) with hand | hor
          · rw [orIn_and hj hand] at ht
            exact (Finset.notMem_empty t ht).elim
          · rw [orIn_or hj hor, Finset.mem_union] at ht
            change gateVal 26 C j x = true
            rw [or_eval x j hj hor]
            rcases ht with h0 | h1
            · exact Or.inl (ih (opnd C j 0) (hopnd_lt hj 0) t h0 hxt)
            · exact Or.inr (ih (opnd C j 1) (hopnd_lt hj 1) t h1 hxt)
        · exfalso
          unfold orIn at ht
          rw [Finset.mem_filter] at ht
          rcases ht.2 with h | ⟨k, _, hr, _, _⟩
          · have := t.isLt; omega
          · exact hj ((orReaches_iff j k).mp hr).1
  have lam_pure : ∀ (k : ℕ), k ∈ lam PG23 C → ∀ (x : Fin 26 → Bool),
      gateVal 26 C k x = true ↔ ∃ t ∈ orIn 26 C (26 + k), x t = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hklam x
      have hkorN : k ∈ orN PG23 C := (Finset.mem_filter.mp hklam).1
      have h0non : (orIn 26 C (opnd C k 0)).Nonempty := (Finset.mem_filter.mp hklam).2.1
      have h1non : (orIn 26 C (opnd C k 1)).Nonempty := (Finset.mem_filter.mp hklam).2.2.1
      have hklen : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hkorN).1
      have hkop : (gateAt C k).op = GateOp.or := (Finset.mem_filter.mp hkorN).2.1
      have hside : ∀ b : Fin 2, (orIn 26 C (opnd C k b)).Nonempty →
          (wireVal 26 C (opnd C k b) x = true ↔ ∃ t ∈ orIn 26 C (opnd C k b), x t = true) := by
        intro b hbnon
        have hlt : opnd C k b < 26 + k := hopnd_lt hklen b
        by_cases hw : opnd C k b < 26
        · let u : Fin 26 := ⟨opnd C k b, hw⟩
          have hu : opnd C k b = u.val := rfl
          rw [hu, wv_input x u, orIn_lt u]
          exact ⟨fun h => ⟨u, Finset.mem_singleton_self u, h⟩,
            by rintro ⟨t, ht, hxt⟩; rw [Finset.mem_singleton.mp ht] at hxt; exact hxt⟩
        · obtain ⟨j, hj_eq⟩ : ∃ j, opnd C k b = 26 + j := ⟨opnd C k b - 26, by omega⟩
          have hjk : j < k := by omega
          have hjlen : j < C.gates.length := by omega
          rw [hj_eq] at hbnon ⊢
          rcases hL.1.1 _ (hgate_mem hjlen) with hand | hor
          · rw [orIn_and hjlen hand] at hbnon
            exact (Finset.not_nonempty_empty hbnon).elim
          · have hjnb : ¬ BelowF PG23 C j := by
              intro hbel
              obtain ⟨t, ht⟩ := hbnon
              have hv : gateVal 26 C j (pairInput t t) = true :=
                orIn_sound (pairInput t t) (26 + j) t ht (pi_left t t)
              have hF := hbel (pairInput t t) hv
              exact PG23.irrefl ((hGfun_pair t t).mp hF)
            have hjlam : j ∈ lam PG23 C := by
              apply hRsub j
              unfold orN gatesWhere
              rw [Finset.mem_filter, Finset.mem_range]
              exact ⟨hjlen, hor, hjnb⟩
            exact ih j hjk hjlam x
      rw [or_eval x k hklen hkop, orIn_or hklen hkop, hside 0 h0non, hside 1 h1non]
      simp only [Finset.mem_union]
      constructor
      · rintro (⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩)
        · exact ⟨t, Or.inl ht, hxt⟩
        · exact ⟨t, Or.inr ht, hxt⟩
      · rintro ⟨t, ht0 | ht1, hxt⟩
        · exact Or.inl ⟨t, ht0, hxt⟩
        · exact Or.inr ⟨t, ht1, hxt⟩
  have lam_star : ∀ (k : ℕ), k ∈ lam PG23 C →
      ∃ c : Fin 26, ∀ t ∈ orIn 26 C (26 + k), PG23.Adj c t ∧ s(c, t) ∈ starEdges PG23 C := by
    intro k hklam
    obtain ⟨_, _, _, a', ha', b', hcard1, hreach⟩ := Finset.mem_filter.mp hklam
    obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard1
    refine ⟨c, fun t ht => ?_⟩
    have ht_side : t ∈ side (n := 26) C a' b' := orIn_mono_reach hreach t ht
    have hc_side : c ∈ side (n := 26) C a' (1 - b') := by rw [hc_eq]; exact Finset.mem_singleton_self c
    have ha'len : a' < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha').1
    have ha'op : (gateAt C a').op = GateOp.and := (Finset.mem_filter.mp ha').2.1
    have ha'bel : BelowF PG23 C a' := (Finset.mem_filter.mp ha').2.2
    have hct_star : s(c, t) ∈ starEdges PG23 C := by
      unfold starEdges
      rw [Finset.mem_biUnion]
      fin_cases b'
      · exact ⟨a', ha', Finset.mem_image.mpr ⟨(t, c), Finset.mem_product.mpr ⟨ht_side, hc_side⟩, Sym2.eq_swap⟩⟩
      · exact ⟨a', ha', Finset.mem_image.mpr ⟨(c, t), Finset.mem_product.mpr ⟨hc_side, ht_side⟩, rfl⟩⟩
    have hct_adj : PG23.Adj c t := by
      apply (hGfun_pair c t).mp
      apply ha'bel (pairInput c t)
      rw [and_eval (pairInput c t) a' ha'len ha'op]
      fin_cases b'
      · exact ⟨orIn_sound (pairInput c t) (opnd C a' 0) t ht_side (pi_right c t),
          orIn_sound (pairInput c t) (opnd C a' 1) c hc_side (pi_left c t)⟩
      · exact ⟨orIn_sound (pairInput c t) (opnd C a' 0) c hc_side (pi_left c t),
          orIn_sound (pairInput c t) (opnd C a' 1) t ht_side (pi_right c t)⟩
    exact ⟨hct_adj, hct_star⟩
  have no_belowF_in_cone : ∀ (a : ℕ), a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ (k : ℕ), InCone 26 C k a → ¬ BelowF PG23 C k := by
    intro a ha haop k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hka hbel
      have hklt : k < a := inCone_lt hka
      have hklen : k < C.gates.length := by omega
      rcases hL.1.1 _ (hgate_mem hklen) with hand | hor
      · exact hT k hklen a ha hand hbel haop hka
      · have hlt0 : opnd C k 0 < 26 + k := hopnd_lt hklen 0
        by_cases hw : opnd C k 0 < 26
        · let u : Fin 26 := ⟨opnd C k 0, hw⟩
          have hv : gateVal 26 C k (pairInput u u) = true := by
            rw [or_eval (pairInput u u) k hklen hor]
            left
            change wireVal 26 C u.val (pairInput u u) = true
            rw [wv_input]
            exact pi_left u u
          exact PG23.irrefl ((hGfun_pair u u).mp (hbel (pairInput u u) hv))
        · obtain ⟨j, hj_eq⟩ : ∃ j, opnd C k 0 = 26 + j := ⟨opnd C k 0 - 26, by omega⟩
          have hjk : j < k := by omega
          have hcone_jk : InCone 26 C j k := by
            refine (inCone_iff j k).mpr ⟨hklen, opnd C k 0, ?_, by omega, hlt0, Or.inl (by omega)⟩
            rw [hinputs_eq hklen]; exact List.mem_cons_self
          have hjnb : ¬ BelowF PG23 C j := ih j hjk (inCone_trans hcone_jk hka)
          obtain ⟨x, hjx, hFx⟩ : ∃ x, gateVal 26 C j x = true ∧ graphFun PG23 ∅ x ≠ true := by
            by_contra h
            exact hjnb fun x hx => Classical.byContradiction fun hne => h ⟨x, hx, hne⟩
          have hkx : gateVal 26 C k x = true := by
            rw [or_eval x k hklen hor]
            left
            rw [hj_eq]
            exact hjx
          exact hFx (hbel x hkx)
  have wire_as_conj : ∀ (a : ℕ), a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ (w : ℕ), (w < 26 ∨ (26 ≤ w ∧ InCone 26 C (w - 26) a)) →
      ∃ L : List (Finset (Fin 26)),
        (∀ S ∈ L, (∃ v : Fin 26, S = {v}) ∨
          (∃ c : Fin 26, ∀ t ∈ S, PG23.Adj c t ∧ s(c, t) ∈ starEdges PG23 C)) ∧
        (∀ x : Fin 26 → Bool, wireVal 26 C w x = true ↔ ∀ S ∈ L, ∃ t ∈ S, x t = true) := by
    intro a ha haop w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hwa
      rcases hwa with hlt | ⟨hge, hcone⟩
      · refine ⟨[{⟨w, hlt⟩}], ?_, ?_⟩
        · intro S hS
          simp only [List.mem_singleton] at hS
          exact Or.inl ⟨⟨w, hlt⟩, hS⟩
        · intro x
          have hu : wireVal 26 C w x = x ⟨w, hlt⟩ := wv_input x ⟨w, hlt⟩
          rw [hu]
          simp
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hsub : 26 + k - 26 = k := by omega
        rw [hsub] at hcone
        have hka : k < a := inCone_lt hcone
        have hklen : k < C.gates.length := by omega
        have hknb : ¬ BelowF PG23 C k := no_belowF_in_cone a ha haop k hcone
        rcases hL.1.1 _ (hgate_mem hklen) with hand | hor
        · have hchild : ∀ b : Fin 2, opnd C k b < 26 ∨
              (26 ≤ opnd C k b ∧ InCone 26 C (opnd C k b - 26) a) := by
            intro b
            by_cases hb : opnd C k b < 26
            · exact Or.inl hb
            · refine Or.inr ⟨by omega, inCone_trans ?_ hcone⟩
              refine (inCone_iff (opnd C k b - 26) k).mpr
                ⟨hklen, opnd C k b, ?_, by omega, hopnd_lt hklen b, Or.inl rfl⟩
              rw [hinputs_eq hklen]; fin_cases b <;> simp
          obtain ⟨L0, hL0_ok, hL0_ev⟩ := ih (opnd C k 0) (hopnd_lt hklen 0) (hchild 0)
          obtain ⟨L1, hL1_ok, hL1_ev⟩ := ih (opnd C k 1) (hopnd_lt hklen 1) (hchild 1)
          refine ⟨L0 ++ L1, ?_, ?_⟩
          · intro S hS
            rcases List.mem_append.mp hS with h0 | h1
            · exact hL0_ok S h0
            · exact hL1_ok S h1
          · intro x
            change gateVal 26 C k x = true ↔ _
            rw [and_eval x k hklen hand, hL0_ev x, hL1_ev x]
            constructor
            · rintro ⟨h0, h1⟩ S hS
              rcases List.mem_append.mp hS with hs0 | hs1
              · exact h0 S hs0
              · exact h1 S hs1
            · intro h
              exact ⟨fun S hS => h S (List.mem_append_left L1 hS),
                fun S hS => h S (List.mem_append_right L0 hS)⟩
        · have hklam : k ∈ lam PG23 C := by
            apply hRsub k
            unfold orN gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨hklen, hor, hknb⟩
          refine ⟨[orIn 26 C (26 + k)], ?_, ?_⟩
          · intro S hS
            simp only [List.mem_singleton] at hS
            subst hS
            exact Or.inr (lam_star k hklam)
          · intro x
            change gateVal 26 C k x = true ↔ _
            rw [lam_pure k hklam x]
            exact ⟨fun h S hS => by rw [List.mem_singleton.mp hS]; exact h,
              fun h => h _ List.mem_cons_self⟩
  have ustar_covered : ∀ e ∈ Ustar PG23 C,
      ∃ a ∈ centreless PG23 C, ∃ u v : Fin 26, e = s(u, v) ∧
        gateVal 26 C a (pairInput u v) = true := by
    intro e he
    revert he
    refine Sym2.ind (fun u v he => ?_) e
    have hadj : PG23.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    have hnotstar : s(u, v) ∉ starEdges PG23 C := (Finset.mem_sdiff.mp he).2
    have hout_eval : ∀ x : Fin 26 → Bool, wireVal 26 C C.output x = graphFun PG23 ∅ x := by
      intro x
      have hf := congrFun hL.2.1 x
      exact hf
    have hout_ge : 26 ≤ C.output := by
      by_contra hlt
      let q : Fin 26 := ⟨C.output, by omega⟩
      have h1 : wireVal 26 C C.output (pairInput q q) = true := by
        change wireVal 26 C q.val (pairInput q q) = true
        rw [wv_input]; exact pi_left q q
      rw [hout_eval] at h1
      exact PG23.irrefl ((hGfun_pair q q).mp h1)
    obtain ⟨o, ho_eq⟩ : ∃ o, C.output = 26 + o := ⟨C.output - 26, by omega⟩
    have ho_len : o < C.gates.length := by
      by_contra hge
      have h1 : wireVal 26 C (26 + o) (pairInput u v) = false := by
        unfold wireVal
        change (C.gates.foldl stepW (List.ofFn (pairInput u v))).getD (26 + o) false = false
        have hlen := foldl_len C.gates (List.ofFn (pairInput u v))
        simp only [List.length_ofFn] at hlen
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega)]
        rfl
      rw [← ho_eq, hout_eval, (hGfun_pair u v).mpr hadj] at h1
      cases h1
    have ho_bel : BelowF PG23 C o := by
      intro x hx
      have h1 : wireVal 26 C C.output x = true := by rw [ho_eq]; exact hx
      rwa [hout_eval] at h1
    have ho_true : gateVal 26 C o (pairInput u v) = true := by
      change wireVal 26 C (26 + o) (pairInput u v) = true
      rw [← ho_eq, hout_eval]
      exact (hGfun_pair u v).mpr hadj
    have find_top : ∀ k : ℕ, k < C.gates.length → BelowF PG23 C k →
        gateVal 26 C k (pairInput u v) = true →
        ∃ a ∈ tops PG23 C, gateVal 26 C a (pairInput u v) = true := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro hklen hkbel hkv
        rcases hL.1.1 _ (hgate_mem hklen) with hand | hor
        · exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklen, hand, hkbel⟩, hkv⟩
        · rw [or_eval (pairInput u v) k hklen hor] at hkv
          have step_side : ∀ b : Fin 2, wireVal 26 C (opnd C k b) (pairInput u v) = true →
              ∃ a ∈ tops PG23 C, gateVal 26 C a (pairInput u v) = true := by
            intro b hbv
            by_cases hw : opnd C k b < 26
            · exfalso
              let q : Fin 26 := ⟨opnd C k b, hw⟩
              have hq : gateVal 26 C k (pairInput q q) = true := by
                rw [or_eval (pairInput q q) k hklen hor]
                have hqq : wireVal 26 C (opnd C k b) (pairInput q q) = true := by
                  change wireVal 26 C q.val (pairInput q q) = true
                  rw [wv_input]; exact pi_left q q
                fin_cases b
                · exact Or.inl hqq
                · exact Or.inr hqq
              exact PG23.irrefl ((hGfun_pair q q).mp (hkbel (pairInput q q) hq))
            · obtain ⟨j, hj_eq⟩ : ∃ j, opnd C k b = 26 + j := ⟨opnd C k b - 26, by omega⟩
              have hltb := hopnd_lt hklen b
              have hjk : j < k := by omega
              have hjbel : BelowF PG23 C j := by
                intro x hjx
                apply hkbel x
                rw [or_eval x k hklen hor]
                have hbx : wireVal 26 C (opnd C k b) x = true := by rw [hj_eq]; exact hjx
                fin_cases b
                · exact Or.inl hbx
                · exact Or.inr hbx
              rw [hj_eq] at hbv
              exact ih j hjk (by omega) hjbel hbv
          rcases hkv with h0 | h1
          · exact step_side 0 h0
          · exact step_side 1 h1
    obtain ⟨a, hatop, hav⟩ := find_top o ho_len ho_bel ho_true
    refine ⟨a, ?_, u, v, rfl, hav⟩
    by_contra hnotc
    have h0non : (side (n := 26) C a 0).Nonempty := by
      by_contra h0e
      apply hnotc
      exact Finset.mem_filter.mpr ⟨hatop, Or.inl (Finset.not_nonempty_iff_eq_empty.mp h0e)⟩
    have h1non : (side (n := 26) C a 1).Nonempty := by
      by_contra h1e
      apply hnotc
      exact Finset.mem_filter.mpr ⟨hatop, Or.inr (Finset.not_nonempty_iff_eq_empty.mp h1e)⟩
    have halen : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hatop).1
    have haop : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp hatop).2.1
    have habel : BelowF PG23 C a := (Finset.mem_filter.mp hatop).2.2
    have hside_hit : ∀ b : Fin 2, (side (n := 26) C a b).Nonempty →
        wireVal 26 C (opnd C a b) (pairInput u v) = true →
        ∃ t ∈ side (n := 26) C a b, pairInput u v t = true := by
      intro b hbnon hbv
      by_cases hw : opnd C a b < 26
      · let q : Fin 26 := ⟨opnd C a b, hw⟩
        have hq : wireVal 26 C q.val (pairInput u v) = true := hbv
        rw [wv_input] at hq
        refine ⟨q, ?_, hq⟩
        unfold side
        change q ∈ orIn 26 C q.val
        rw [orIn_lt q]
        exact Finset.mem_singleton_self q
      · obtain ⟨j, hj_eq⟩ : ∃ j, opnd C a b = 26 + j := ⟨opnd C a b - 26, by omega⟩
        have hltb := hopnd_lt halen b
        have hja : j < a := by omega
        have hjlen : j < C.gates.length := by omega
        have hjcone : InCone 26 C j a := by
          refine (inCone_iff j a).mpr ⟨halen, opnd C a b, ?_, by omega, hltb, Or.inl (by omega)⟩
          rw [hinputs_eq halen]
          fin_cases b
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        have hjnb : ¬ BelowF PG23 C j := no_belowF_in_cone a halen haop j hjcone
        rcases hL.1.1 _ (hgate_mem hjlen) with hand | hor
        · unfold side at hbnon
          rw [hj_eq, orIn_and hjlen hand] at hbnon
          exact (Finset.not_nonempty_empty hbnon).elim
        · have hjlam : j ∈ lam PG23 C := by
            apply hRsub j
            unfold orN gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨hjlen, hor, hjnb⟩
          unfold side
          rw [hj_eq] at hbv ⊢
          exact (lam_pure j hjlam (pairInput u v)).mp hbv
    obtain ⟨hav0, hav1⟩ := (and_eval (pairInput u v) a halen haop).mp hav
    obtain ⟨t0, ht0s, ht0p⟩ := hside_hit 0 h0non hav0
    obtain ⟨t1, ht1s, ht1p⟩ := hside_hit 1 h1non hav1
    have htne : t0 ≠ t1 := by
      intro heq
      subst heq
      have hself : gateVal 26 C a (pairInput t0 t0) = true := by
        rw [and_eval (pairInput t0 t0) a halen haop]
        exact ⟨orIn_sound (pairInput t0 t0) (opnd C a 0) t0 ht0s (pi_left t0 t0),
          orIn_sound (pairInput t0 t0) (opnd C a 1) t0 ht1s (pi_left t0 t0)⟩
      exact PG23.irrefl ((hGfun_pair t0 t0).mp (habel (pairInput t0 t0) hself))
    rw [pi_iff] at ht0p ht1p
    have hpair_eq : s(t0, t1) = s(u, v) := by
      rcases ht0p with rfl | rfl <;> rcases ht1p with rfl | rfl
      · exact (htne rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (htne rfl).elim
    have hstar : s(u, v) ∈ starEdges PG23 C := by
      rw [← hpair_eq]
      unfold starEdges
      rw [Finset.mem_biUnion]
      exact ⟨a, hatop, Finset.mem_image.mpr ⟨(t0, t1), Finset.mem_product.mpr ⟨ht0s, ht1s⟩, rfl⟩⟩
    exact hnotstar hstar
  let E_of : ℕ → Finset (Sym2 (Fin 26)) := fun a =>
    (Ustar PG23 C).filter fun e => ∃ u v : Fin 26, e = s(u, v) ∧
      gateVal 26 C a (pairInput u v) = true
  have hE_card_le_one : ∀ a ∈ centreless PG23 C, (E_of a).card ≤ 1 := by
    intro a ha
    have hatop : a ∈ tops PG23 C := (Finset.mem_filter.mp ha).1
    have halen : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hatop).1
    have haop : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp hatop).2.1
    have habel : BelowF PG23 C a := (Finset.mem_filter.mp hatop).2.2
    have hchild : ∀ b : Fin 2, opnd C a b < 26 ∨
        (26 ≤ opnd C a b ∧ InCone 26 C (opnd C a b - 26) a) := by
      intro b
      by_cases hb : opnd C a b < 26
      · exact Or.inl hb
      · refine Or.inr ⟨by omega, ?_⟩
        refine (inCone_iff (opnd C a b - 26) a).mpr
          ⟨halen, opnd C a b, ?_, by omega, hopnd_lt halen b, Or.inl rfl⟩
        rw [hinputs_eq halen]
        fin_cases b
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨L0, hL0_ok, hL0_ev⟩ := wire_as_conj a halen haop (opnd C a 0) (hchild 0)
    obtain ⟨L1, hL1_ok, hL1_ev⟩ := wire_as_conj a halen haop (opnd C a 1) (hchild 1)
    let L : List (Finset (Fin 26)) := L0 ++ L1
    have hL_ok : ∀ S ∈ L, (∃ v : Fin 26, S = {v}) ∨
        (∃ c : Fin 26, ∀ t ∈ S, PG23.Adj c t ∧ s(c, t) ∈ starEdges PG23 C) := by
      intro S hS
      rcases List.mem_append.mp hS with h0 | h1
      · exact hL0_ok S h0
      · exact hL1_ok S h1
    have hL_ev : ∀ x : Fin 26 → Bool, gateVal 26 C a x = true ↔ ∀ S ∈ L, ∃ t ∈ S, x t = true := by
      intro x
      rw [and_eval x a halen haop, hL0_ev x, hL1_ev x]
      constructor
      · rintro ⟨h0, h1⟩ S hS
        rcases List.mem_append.mp hS with hs0 | hs1
        · exact h0 S hs0
        · exact h1 S hs1
      · intro h
        exact ⟨fun S hS => h S (List.mem_append_left L1 hS),
          fun S hS => h S (List.mem_append_right L0 hS)⟩
    have hL_mono : ∀ S ∈ L, (∀ t ∈ S, t.val < 13) ∨ (∀ t ∈ S, 13 ≤ t.val) := by
      intro S hS
      rcases hL_ok S hS with ⟨v, rfl⟩ | ⟨c, hcS⟩
      · by_cases hv : v.val < 13
        · exact Or.inl (fun t ht => by rw [Finset.mem_singleton.mp ht]; exact hv)
        · exact Or.inr (fun t ht => by have := Finset.mem_singleton.mp ht; subst this; omega)
      · by_cases hcv : c.val < 13
        · refine Or.inr (fun t ht => ?_)
          have hne := hBip c t (hcS t ht).1
          by_contra hge
          have hlt : t.val < 13 := by omega
          simp [hcv, hlt] at hne
        · refine Or.inl (fun t ht => ?_)
          have hne := hBip c t (hcS t ht).1
          have hcf : decide (c.val < 13) = false := decide_eq_false hcv
          rw [hcf] at hne
          by_contra hge
          have htf : decide (t.val < 13) = false := decide_eq_false hge
          exact hne htf.symm
    let Lp : List (Finset (Fin 26)) := L.filter fun S => decide (∀ t ∈ S, t.val < 13)
    let Ll : List (Finset (Fin 26)) := L.filter fun S => decide (∀ t ∈ S, 13 ≤ t.val)
    let A : Finset (Fin 26) := Finset.univ.filter fun u => u.val < 13 ∧ ∀ S ∈ Lp, u ∈ S
    let B : Finset (Fin 26) := Finset.univ.filter fun v => 13 ≤ v.val ∧ ∀ S ∈ Ll, v ∈ S
    have hAB_iff : ∀ u v : Fin 26, u.val < 13 → 13 ≤ v.val →
        (gateVal 26 C a (pairInput u v) = true ↔ u ∈ A ∧ v ∈ B) := by
      intro u v hu13 hv13
      rw [hL_ev (pairInput u v)]
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, hu13, hv13]
      constructor
      · intro h
        constructor
        · intro S hS
          simp only [Lp, List.mem_filter, decide_eq_true_eq] at hS
          obtain ⟨t, htS, htp⟩ := h S hS.1
          rw [pi_iff] at htp
          rcases htp with htu | htv
          · subst htu; exact htS
          · subst htv; have := hS.2 t htS; omega
        · intro S hS
          simp only [Ll, List.mem_filter, decide_eq_true_eq] at hS
          obtain ⟨t, htS, htp⟩ := h S hS.1
          rw [pi_iff] at htp
          rcases htp with htu | htv
          · subst htu; have := hS.2 t htS; omega
          · subst htv; exact htS
      · rintro ⟨hA, hB⟩ S hS
        rcases hL_mono S hS with hp | hl
        · have hSp : S ∈ Lp := List.mem_filter.mpr ⟨hS, decide_eq_true hp⟩
          exact ⟨u, hA S hSp, pi_left u v⟩
        · have hSl : S ∈ Ll := List.mem_filter.mpr ⟨hS, decide_eq_true hl⟩
          exact ⟨v, hB S hSl, pi_right u v⟩
    have hAB_adj : ∀ u ∈ A, ∀ v ∈ B, PG23.Adj u v := by
      intro u huA v hvB
      have hu13 : u.val < 13 := (Finset.mem_filter.mp huA).2.1
      have hv13 : 13 ≤ v.val := (Finset.mem_filter.mp hvB).2.1
      have hgv : gateVal 26 C a (pairInput u v) = true :=
        (hAB_iff u v hu13 hv13).mpr ⟨huA, hvB⟩
      exact (hGfun_pair u v).mp (habel (pairInput u v) hgv)
    have hAB_card : A.card ≤ 1 ∨ B.card ≤ 1 := by
      by_contra h
      have hAgt : 1 < A.card := by omega
      have hBgt : 1 < B.card := by omega
      obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hAgt
      have hsub : B ⊆ Finset.univ.filter fun w => PG23.Adj u1 w ∧ PG23.Adj u2 w := by
        intro v hvB
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hAB_adj u1 hu1 v hvB, hAB_adj u2 hu2 v hvB⟩
      have hle := (Finset.card_le_card hsub).trans (hNoFour u1 u2 hune)
      omega
    have hE_orient : ∀ e ∈ E_of a, ∃ u v : Fin 26, e = s(u, v) ∧ u ∈ A ∧ v ∈ B ∧
        s(u, v) ∉ starEdges PG23 C := by
      intro e he
      have heU : e ∈ Ustar PG23 C := (Finset.mem_filter.mp he).1
      obtain ⟨u0, v0, rfl, hgv⟩ := (Finset.mem_filter.mp he).2
      have hadj0 : PG23.Adj u0 v0 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp heU).1
      have hns0 : s(u0, v0) ∉ starEdges PG23 C := (Finset.mem_sdiff.mp heU).2
      have hne := hBip u0 v0 hadj0
      by_cases hu0 : u0.val < 13
      · have hv0 : 13 ≤ v0.val := by
          by_contra hge
          have hlt : v0.val < 13 := by omega
          simp [hu0, hlt] at hne
        obtain ⟨huA, hvB⟩ := (hAB_iff u0 v0 hu0 hv0).mp hgv
        exact ⟨u0, v0, rfl, huA, hvB, hns0⟩
      · have hv0 : v0.val < 13 := by
          have huf : decide (u0.val < 13) = false := decide_eq_false hu0
          rw [huf] at hne
          by_contra hge
          exact hne (decide_eq_false hge).symm
        have hgv' : gateVal 26 C a (pairInput v0 u0) = true := by rw [pi_comm]; exact hgv
        obtain ⟨hvA, huB⟩ := (hAB_iff v0 u0 hv0 (by omega)).mp hgv'
        exact ⟨v0, u0, Sym2.eq_swap, hvA, huB, by rwa [Sym2.eq_swap]⟩
    rw [Finset.card_le_one]
    intro e1 he1 e2 he2
    obtain ⟨u1, v1, rfl, hu1A, hv1B, hns1⟩ := hE_orient e1 he1
    obtain ⟨u2, v2, rfl, hu2A, hv2B, _⟩ := hE_orient e2 he2
    rcases hAB_card with hA1 | hB1
    · have hueq : u1 = u2 := Finset.card_le_one.mp hA1 u1 hu1A u2 hu2A
      subst hueq
      have hLl_non : Ll ≠ [] := by
        intro hnil
        have hself : gateVal 26 C a (pairInput u1 u1) = true := by
          rw [hL_ev (pairInput u1 u1)]
          intro S hS
          rcases hL_mono S hS with hp | hl
          · have hSp : S ∈ Lp := List.mem_filter.mpr ⟨hS, decide_eq_true hp⟩
            exact ⟨u1, (Finset.mem_filter.mp hu1A).2.2 S hSp, pi_left u1 u1⟩
          · have hSl : S ∈ Ll := List.mem_filter.mpr ⟨hS, decide_eq_true hl⟩
            rw [hnil] at hSl
            exact (List.not_mem_nil hSl).elim
        exact PG23.irrefl ((hGfun_pair u1 u1).mp (habel (pairInput u1 u1) hself))
      obtain ⟨S, rest, hLl_eq⟩ := List.exists_cons_of_ne_nil hLl_non
      have hSl : S ∈ Ll := by rw [hLl_eq]; exact List.mem_cons_self
      have hSL : S ∈ L := (List.mem_filter.mp hSl).1
      have hv1S : v1 ∈ S := (Finset.mem_filter.mp hv1B).2.2 S hSl
      have hv2S : v2 ∈ S := (Finset.mem_filter.mp hv2B).2.2 S hSl
      have hveq : v1 = v2 := by
        rcases hL_ok S hSL with ⟨v0, rfl⟩ | ⟨c, hcS⟩
        · rw [Finset.mem_singleton.mp hv1S, Finset.mem_singleton.mp hv2S]
        · by_cases hcu : c = u1
          · subst hcu
            exact (hns1 (hcS v1 hv1S).2).elim
          · have hsub : ({v1, v2} : Finset (Fin 26)) ⊆
                Finset.univ.filter fun w => PG23.Adj u1 w ∧ PG23.Adj c w := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with hw1 | hw2
              · subst hw1
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hAB_adj u1 hu1A w hv1B, (hcS w hv1S).1⟩
              · subst hw2
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hAB_adj u1 hu1A w hv2B, (hcS w hv2S).1⟩
            have hle := (Finset.card_le_card hsub).trans (hNoFour u1 c (Ne.symm hcu))
            by_contra hvne
            rw [Finset.card_pair hvne] at hle
            omega
      subst hveq
      rfl
    · have hveq : v1 = v2 := Finset.card_le_one.mp hB1 v1 hv1B v2 hv2B
      subst hveq
      have hLp_non : Lp ≠ [] := by
        intro hnil
        have hself : gateVal 26 C a (pairInput v1 v1) = true := by
          rw [hL_ev (pairInput v1 v1)]
          intro S hS
          rcases hL_mono S hS with hp | hl
          · have hSp : S ∈ Lp := List.mem_filter.mpr ⟨hS, decide_eq_true hp⟩
            rw [hnil] at hSp
            exact (List.not_mem_nil hSp).elim
          · have hSl : S ∈ Ll := List.mem_filter.mpr ⟨hS, decide_eq_true hl⟩
            exact ⟨v1, (Finset.mem_filter.mp hv1B).2.2 S hSl, pi_left v1 v1⟩
        exact PG23.irrefl ((hGfun_pair v1 v1).mp (habel (pairInput v1 v1) hself))
      obtain ⟨S, rest, hLp_eq⟩ := List.exists_cons_of_ne_nil hLp_non
      have hSp : S ∈ Lp := by rw [hLp_eq]; exact List.mem_cons_self
      have hSL : S ∈ L := (List.mem_filter.mp hSp).1
      have hu1S : u1 ∈ S := (Finset.mem_filter.mp hu1A).2.2 S hSp
      have hu2S : u2 ∈ S := (Finset.mem_filter.mp hu2A).2.2 S hSp
      have hueq : u1 = u2 := by
        rcases hL_ok S hSL with ⟨u0, rfl⟩ | ⟨c, hcS⟩
        · rw [Finset.mem_singleton.mp hu1S, Finset.mem_singleton.mp hu2S]
        · by_cases hcv : c = v1
          · subst hcv
            have hs : s(u1, c) ∈ starEdges PG23 C := by
              rw [Sym2.eq_swap]; exact (hcS u1 hu1S).2
            exact (hns1 hs).elim
          · have hsub : ({u1, u2} : Finset (Fin 26)) ⊆
                Finset.univ.filter fun w => PG23.Adj v1 w ∧ PG23.Adj c w := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with hw1 | hw2
              · subst hw1
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, (hAB_adj w hu1A v1 hv1B).symm, (hcS w hu1S).1⟩
              · subst hw2
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, (hAB_adj w hu2A v1 hv1B).symm, (hcS w hu2S).1⟩
            have hle := (Finset.card_le_card hsub).trans (hNoFour v1 c (Ne.symm hcv))
            by_contra hune
            rw [Finset.card_pair hune] at hle
            omega
      subst hueq
      rfl
  have hU_sub : Ustar PG23 C ⊆ (centreless PG23 C).biUnion E_of := by
    intro e he
    obtain ⟨a, ha, u, v, rfl, hgv⟩ := ustar_covered e he
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨he, u, v, rfl, hgv⟩⟩
  have hU_le : (Ustar PG23 C).card ≤ (centreless PG23 C).card := by
    calc (Ustar PG23 C).card
        ≤ ((centreless PG23 C).biUnion E_of).card := Finset.card_le_card hU_sub
      _ ≤ ∑ a ∈ centreless PG23 C, (E_of a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ centreless PG23 C, 1 := Finset.sum_le_sum hE_card_le_one
      _ = (centreless PG23 C).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [hR0, Finset.card_empty] at hbud
  omega
