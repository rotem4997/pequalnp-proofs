import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5244_2
    (h1 : ∃ (c1 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        ∀ jtop ∈ PEqualNP.TopForm.junk G C,
          (∀ j ∈ PEqualNP.TopForm.junk G C, j = jtop ∨ PEqualNP.EdgeOwnership.InCone n C j jtop) →
          (¬∃ (K : Finset (Fin n)) (E0 : Finset (Sym2 (Fin n))),
            K.card ≤ (4 : ℕ) ∧ E0.card ≤ C.size + (1 : ℕ) ∧
            ∀ e ∈ PEqualNP.TopForm.Ustar G C, e ∈ E0 ∨
              ∃ (u v : Fin n), e = s(u, v) ∧ ((∃ w ∈ K, G.Adj u w) ∨ (∃ w ∈ K, G.Adj v w))) →
          (PEqualNP.TopForm.Ustar G C ∩ PEqualNP.TopForm.gammaE G C jtop).card ≤ c1 * (C.size + (1 : ℕ)))
    (h2 : ∃ (c2 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        ∀ jtop ∈ PEqualNP.TopForm.junk G C,
          (∀ j ∈ PEqualNP.TopForm.junk G C, j = jtop ∨ PEqualNP.EdgeOwnership.InCone n C j jtop) →
          (¬∃ (K : Finset (Fin n)) (E0 : Finset (Sym2 (Fin n))),
            K.card ≤ (4 : ℕ) ∧ E0.card ≤ C.size + (1 : ℕ) ∧
            ∀ e ∈ PEqualNP.TopForm.Ustar G C, e ∈ E0 ∨
              ∃ (u v : Fin n), e = s(u, v) ∧ ((∃ w ∈ K, G.Adj u w) ∨ (∃ w ∈ K, G.Adj v w))) →
          ((PEqualNP.TopForm.Ustar G C \ PEqualNP.TopForm.gammaE G C jtop).filter fun e =>
            ∃ j ∈ PEqualNP.TopForm.junk G C, j ≠ jtop ∧ PEqualNP.EdgeOwnership.InCone n C j jtop ∧
              e ∈ PEqualNP.TopForm.gammaE G C j).card ≤ c2 * (C.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨c1 + c2, ?_⟩
  intro n G _ hgirth hne C hleast htop hj3 hmax_ex hno_cov
  obtain ⟨jtop, hjtop, hmax⟩ := hmax_ex
  have hbound1 := hc1 n G hgirth hne C hleast htop hj3 jtop hjtop hmax hno_cov
  have hbound2 := hc2 n G hgirth hne C hleast htop hj3 jtop hjtop hmax hno_cov
  obtain ⟨⟨handor, hreads, hfan2⟩, hfun, _⟩ := hleast
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have hstep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hstep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons]
      have hlt : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool)
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl step ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < ws.length + j then (gs.foldl step ws).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro ws j g hj; simp at hj
    | cons g0 gs ih =>
      intro ws j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hstep_lt gs (step ws g0) ws.length hlt]
        have hself : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun i => ws.getD i false) := by
          simp only [step, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < ws.length
        · have hilt : i < (step ws g0).length := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          simp only [hi, ↓reduceIte]
          rw [hstep_lt gs (step ws g0) i hilt]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
            Option.getD_none]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j + 1) = (step ws g0).length + j := by omega
        rw [hidx]
        exact ih (step ws g0) j g hj
  have hgateAt_eq : ∀ (j : ℕ) (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hgate_inputs_eq : ∀ j : ℕ, j < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs =
        [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] := by
    intro j hj
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 := by
      rw [hgateAt_eq j hj]; exact hfan2 _ hmem
    cases hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs with
    | nil => rw [hinp] at hlen; simp at hlen
    | cons a l1 =>
      cases l1 with
      | nil => rw [hinp] at hlen; simp at hlen
      | cons b l2 =>
        cases l2 with
        | cons _ _ => rw [hinp] at hlen; simp at hlen
        | nil =>
          have h0 : PEqualNP.TopForm.opnd C j 0 = a := by
            change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a
            rw [hinp]; rfl
          have h1' : PEqualNP.TopForm.opnd C j 1 = b := by
            change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b
            rw [hinp]; rfl
          rw [h0, h1']
  have hopnd_lt : ∀ j : ℕ, j < C.gates.length → ∀ b : Fin 2,
      PEqualNP.TopForm.opnd C j b < n + j := by
    intro j hj b
    have hinp := hgate_inputs_eq j hj
    have hmem : PEqualNP.TopForm.opnd C j b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
      rw [hinp]
      fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    exact hreads j hj _ hmem
  have hwire_in : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      PEqualNP.CleanedNonEdge.wireVal n C w x = x ⟨w, hw⟩ := by
    intro x w hw
    change (C.gates.foldl step (List.ofFn x)).getD w false = x ⟨w, hw⟩
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have hlt : w < (List.ofFn x).length := by omega
    rw [hstep_lt C.gates (List.ofFn x) w hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have hand_ev : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hor_ev : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hwire_gate : ∀ (x : Fin n → Bool) (j : ℕ), j < C.gates.length →
      PEqualNP.CleanedNonEdge.wireVal n C (n + j) x =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
          [PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C j 0) x,
           PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C j 1) x] := by
    intro x j hj
    have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
    have hg := hstep_gate C.gates (List.ofFn x) j C.gates[j] hget
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at hg
    have hinp := hgate_inputs_eq j hj
    rw [hgateAt_eq j hj] at hinp ⊢
    have h0 := hopnd_lt j hj 0
    have h1' := hopnd_lt j hj 1
    change (C.gates.foldl step (List.ofFn x)).getD (n + j) false = _
    rw [hg, hinp]
    simp only [List.map_cons, List.map_nil, h0, h1', ↓reduceIte]
    rfl
  have hwire_ge : ∀ (x : Fin n → Bool) (w : ℕ), n + C.gates.length ≤ w →
      PEqualNP.CleanedNonEdge.wireVal n C w x = false := by
    intro x w hw
    change (C.gates.foldl step (List.ofFn x)).getD w false = false
    have hlen : (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length := by
      rw [hstep_len, List.length_ofFn]
    have hge : (C.gates.foldl step (List.ofFn x)).length ≤ w := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  -- OR closure helpers
  let ostep : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (List ℕ) :=
    fun cs g => cs ++ [cs.length :: (if g.op = PEqualNP.CircuitLowerBounds.GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]
  have hostep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl ostep cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons]
      have hlt : i < (ostep cs g).length := by
        simp only [ostep, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (ostep cs g) i hlt]
      simp only [ostep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hostep_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ))
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl ostep cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if g.op = PEqualNP.CircuitLowerBounds.GateOp.or then
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
            (fun w => (gs.foldl ostep cs).getD (w - n) [])
          else []) := by
    intro gs
    induction gs with
    | nil => intro cs j g hj; simp at hj
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (ostep cs g0).length := by
          simp only [ostep, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hostep_lt gs (ostep cs g0) cs.length hlt]
        have hself : (ostep cs g0).getD cs.length [] =
            cs.length :: (if g0.op = PEqualNP.CircuitLowerBounds.GateOp.or then
              (g0.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
                (fun w => cs.getD (w - n) [])
              else []) := by
          simp only [ostep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        congr 1
        split_ifs
        · apply List.flatMap_congr
          intro w hw
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          have hwlt : w - n < cs.length := by omega
          have hwlt1 : w - n < (ostep cs g0).length := by
            simp only [ostep, List.length_append, List.length_cons, List.length_nil]; omega
          rw [hostep_lt gs (ostep cs g0) (w - n) hwlt1]
          simp only [ostep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
        · rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (ostep cs g0).length = cs.length + 1 := by
          simp only [ostep, List.length_append, List.length_cons, List.length_nil]
        have hidx : cs.length + (j + 1) = (ostep cs g0).length + j := by omega
        rw [hidx]
        exact ih (ostep cs g0) j g hj
  have horReaches_self : ∀ j : ℕ, j < C.gates.length →
      PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j := by
    intro j hj
    change n ≤ n + j ∧ j ∈ (C.gates.foldl ostep []).getD (n + j - n) []
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    have hg := hostep_gate C.gates [] j C.gates[j] (List.getElem?_eq_getElem hj)
    simp only [List.length_nil, Nat.zero_add] at hg
    rw [hg]
    exact List.mem_cons_self
  have horReaches_or_step : ∀ (a : ℕ) (w k : ℕ),
      a < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs →
      w < n + a →
      PEqualNP.CleanedNonEdge.OrReaches n C w k →
      PEqualNP.CleanedNonEdge.OrReaches n C (n + a) k := by
    intro a w k ha hop hmem hwlt hreach
    obtain ⟨hnw, hk⟩ := hreach
    change n ≤ n + a ∧ k ∈ (C.gates.foldl ostep []).getD (n + a - n) []
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    have hg := hostep_gate C.gates [] a C.gates[a] (List.getElem?_eq_getElem ha)
    simp only [List.length_nil, Nat.zero_add] at hg
    rw [hg]
    rw [hgateAt_eq a ha] at hop hmem
    simp only [hop, ↓reduceIte, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    right
    exact ⟨w, ⟨hmem, hnw, hwlt⟩, hk⟩
  have horIn_mono_or : ∀ (a : ℕ) (b : Fin 2) (i : Fin n),
      a < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      i ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a b) →
      i ∈ PEqualNP.TopForm.orIn n C (n + a) := by
    intro a b i ha hop hi
    change i ∈ Finset.univ.filter fun i0 : Fin n => (i0 : ℕ) = PEqualNP.TopForm.opnd C a b ∨
      ∃ k < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) k ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (i0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs at hi
    change i ∈ Finset.univ.filter fun i0 : Fin n => (i0 : ℕ) = n + a ∨
      ∃ k < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (n + a) k ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (i0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hmem : PEqualNP.TopForm.opnd C a b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by
      rw [hgate_inputs_eq a ha]
      fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hlt := hopnd_lt a ha b
    right
    rcases hi with heq | ⟨k, hklt, hreach, hkop, hkin⟩
    · exact ⟨a, ha, horReaches_self a ha, hop, heq ▸ hmem⟩
    · exact ⟨k, hklt, horReaches_or_step a _ k ha hop hmem hlt hreach, hkop, hkin⟩
  have horReaches_sound : ∀ (w k : ℕ) (x : Fin n → Bool),
      PEqualNP.CleanedNonEdge.OrReaches n C w k →
      PEqualNP.CleanedNonEdge.wireVal n C (n + k) x = true →
      PEqualNP.CleanedNonEdge.wireVal n C w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro k x hreach hkval
      obtain ⟨hnw, hmem⟩ := hreach
      let j := w - n
      have hwj : w = n + j := by omega
      have hjlt : j < C.gates.length := by
        by_contra hge
        have hlen : (C.gates.foldl ostep []).length = C.gates.length := by
          have : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
              (gs.foldl ostep cs).length = cs.length + gs.length := by
            intro gs
            induction gs with
            | nil => intro cs; simp
            | cons g gs' ih' =>
              intro cs
              simp only [List.foldl_cons, ih', ostep, List.length_append, List.length_cons, List.length_nil]
              omega
          have h := this C.gates []
          simp only [List.length_nil, Nat.zero_add] at h
          exact h
        have hnone : (C.gates.foldl ostep [])[j]? = none := List.getElem?_eq_none (by omega)
        have hemp : (C.gates.foldl ostep []).getD j [] = [] := by
          rw [List.getD_eq_getElem?_getD, hnone]; rfl
        change k ∈ (C.gates.foldl ostep []).getD j [] at hmem
        rw [hemp] at hmem
        simp at hmem
      have hg := hostep_gate C.gates [] j C.gates[j] (List.getElem?_eq_getElem hjlt)
      simp only [List.length_nil, Nat.zero_add] at hg
      change k ∈ (C.gates.foldl ostep []).getD j [] at hmem
      rw [hg, List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · rw [hwj]; exact hkval
      · by_cases hop : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or
        · simp only [hop, ↓reduceIte, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hrest
          obtain ⟨u, ⟨hu_in, hnu, hult⟩, hk_u⟩ := hrest
          have huval : PEqualNP.CleanedNonEdge.wireVal n C u x = true :=
            ih u (by omega) k x ⟨hnu, hk_u⟩ hkval
          rw [hwj, hwire_gate x j hjlt]
          have hga_op : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
              PEqualNP.CircuitLowerBounds.GateOp.or := by rw [hgateAt_eq j hjlt]; exact hop
          rw [hga_op, hor_ev]
          have hinp := hgate_inputs_eq j hjlt
          rw [hgateAt_eq j hjlt] at hinp
          rw [hinp] at hu_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_in
          rcases hu_in with rfl | rfl
          · rw [huval]; rfl
          · rw [huval]; exact Bool.or_true _
        · simp only [hop, ↓reduceIte, List.not_mem_nil] at hrest
  have horIn_sound : ∀ (w : ℕ) (i : Fin n) (x : Fin n → Bool),
      i ∈ PEqualNP.TopForm.orIn n C w → x i = true →
      PEqualNP.CleanedNonEdge.wireVal n C w x = true := by
    intro w i x hi hxi
    change i ∈ Finset.univ.filter fun i0 : Fin n => (i0 : ℕ) = w ∨
      ∃ k < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C w k ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (i0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with rfl | ⟨k, hklt, hreach, hkop, hkin⟩
    · rw [hwire_in x i.val i.isLt]; exact hxi
    · apply horReaches_sound w k x hreach
      rw [hwire_gate x k hklt, hkop, hor_ev]
      rw [hgate_inputs_eq k hklt] at hkin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
      rcases hkin with heq | heq
      · rw [← heq, hwire_in x i.val i.isLt, hxi]; rfl
      · rw [← heq, hwire_in x i.val i.isLt, hxi]; exact Bool.or_true _
  -- Every edge in Ustar fires at least one junk AND gate!
  have hsub : PEqualNP.TopForm.Ustar G C ⊆
      (PEqualNP.TopForm.Ustar G C ∩ PEqualNP.TopForm.gammaE G C jtop) ∪
      ((PEqualNP.TopForm.Ustar G C \ PEqualNP.TopForm.gammaE G C jtop).filter fun e =>
        ∃ j ∈ PEqualNP.TopForm.junk G C, j ≠ jtop ∧ PEqualNP.EdgeOwnership.InCone n C j jtop ∧
          e ∈ PEqualNP.TopForm.gammaE G C j) := by
    intro e he
    by_cases hjt : e ∈ PEqualNP.TopForm.gammaE G C jtop
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, hjt⟩)
    · apply Finset.mem_union_right
      rw [Finset.mem_filter, Finset.mem_sdiff]
      refine ⟨⟨he, hjt⟩, ?_⟩
      -- Prove ∃ j ∈ junk G C, e ∈ gammaE G C j
      have he_mem : e ∈ G.edgeFinset ∧ e ∉ PEqualNP.TopForm.starEdges G C := by
        change e ∈ G.edgeFinset \ PEqualNP.TopForm.starEdges G C at he
        exact Finset.mem_sdiff.mp he
      obtain ⟨he_edge, he_not_star⟩ := he_mem
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he_edge
        have hpi : ∀ (p q z : Fin n),
            PEqualNP.EdgeOwnership.pairInput p q z = true ↔ z = p ∨ z = q :=
          fun _ _ _ => decide_eq_true_iff
        let x := PEqualNP.EdgeOwnership.pairInput u v
        have hgraph_true : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
          change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
            decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_true_eq]
          exact ⟨u, v, huv, (hpi u v u).mpr (Or.inl rfl), (hpi u v v).mpr (Or.inr rfl)⟩
        have hgraph_one : ∀ i : Fin n,
            PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
              (PEqualNP.EdgeOwnership.pairInput i i) = false := by
          intro i
          change (decide (∃ a ∈ (∅ : Finset (Fin n)), PEqualNP.EdgeOwnership.pairInput i i a = true) ||
            decide (∃ a b, G.Adj a b ∧ PEqualNP.EdgeOwnership.pairInput i i a = true ∧
              PEqualNP.EdgeOwnership.pairInput i i b = true)) = false
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_false_iff_not]
          intro hex'
          obtain ⟨a, b, hab, ha, hb⟩ := hex'
          have ha' : a = i := by rcases (hpi i i a).mp ha with h | h <;> exact h
          have hb' : b = i := by rcases (hpi i i b).mp hb with h | h <;> exact h
          rw [ha', hb'] at hab
          exact G.loopless.irrefl i hab
        have hout_true : PEqualNP.CleanedNonEdge.wireVal n C C.output x = true := by
          have hfx := congrFun hfun x
          change C.eval (List.ofFn x) = _ at hfx
          change C.eval (List.ofFn x) = true
          rw [hfx]; exact hgraph_true
        have hout_orIn_empty : ∀ i : Fin n, i ∉ PEqualNP.TopForm.orIn n C C.output := by
          intro i hi
          have hti : PEqualNP.CleanedNonEdge.wireVal n C C.output
              (PEqualNP.EdgeOwnership.pairInput i i) = true :=
            horIn_sound C.output i (PEqualNP.EdgeOwnership.pairInput i i) hi
              ((hpi i i i).mpr (Or.inl rfl))
          have hfi : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput i i)) = false := by
            have := congrFun hfun (PEqualNP.EdgeOwnership.pairInput i i)
            change C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput i i)) = _ at this
            rw [this]; exact hgraph_one i
          change C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput i i)) = true at hti
          rw [hfi] at hti
          cases hti
        let P : ℕ → Prop := fun w =>
          PEqualNP.CleanedNonEdge.wireVal n C w x = true ∧
            ∀ i ∈ PEqualNP.TopForm.orIn n C w, x i = false
        have hP_ex : ∃ w : ℕ, P w :=
          ⟨C.output, hout_true, fun i hi => absurd hi (hout_orIn_empty i)⟩
        let w := Nat.find hP_ex
        have hPw : P w := Nat.find_spec hP_ex
        have hPmin : ∀ w' < w, ¬ P w' := fun w' hw' => Nat.find_min hP_ex hw'
        have hwn : n ≤ w := by
          by_contra hlt
          have hlt' : w < n := Nat.lt_of_not_ge hlt
          have hmem_self : (⟨w, hlt'⟩ : Fin n) ∈ PEqualNP.TopForm.orIn n C w := by
            change (⟨w, hlt'⟩ : Fin n) ∈ Finset.univ.filter fun i0 : Fin n => (i0 : ℕ) = w ∨ _
            simp
          have hf := hPw.2 ⟨w, hlt'⟩ hmem_self
          have ht := hPw.1
          rw [hwire_in x w hlt'] at ht
          rw [hf] at ht
          cases ht
        have hwlt : w < n + C.gates.length := by
          by_contra hge
          have hf := hwire_ge x w (Nat.le_of_not_lt hge)
          rw [hPw.1] at hf
          cases hf
        let a := w - n
        have halt : a < C.gates.length := by omega
        have hwa : w = n + a := by omega
        have haop : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op =
            PEqualNP.CircuitLowerBounds.GateOp.and := by
          have hmem_a : C.gates[a] ∈ C.gates := List.getElem_mem halt
          have hdisj := handor C.gates[a] hmem_a
          rw [← hgateAt_eq a halt] at hdisj
          rcases hdisj with hand | hor
          · exact hand
          · exfalso
            have hval := hPw.1
            rw [hwa, hwire_gate x a halt, hor, hor_ev, Bool.or_eq_true] at hval
            rcases hval with h0 | h1'
            · apply hPmin (PEqualNP.TopForm.opnd C a 0) (by have := hopnd_lt a halt 0; omega)
              refine ⟨h0, fun i hi => hPw.2 i ?_⟩
              rw [hwa]; exact horIn_mono_or a 0 i halt hor hi
            · apply hPmin (PEqualNP.TopForm.opnd C a 1) (by have := hopnd_lt a halt 1; omega)
              refine ⟨h1', fun i hi => hPw.2 i ?_⟩
              rw [hwa]; exact horIn_mono_or a 1 i halt hor hi
        by_cases hbel : PEqualNP.TopForm.BelowF G C a
        · exfalso
          have hval := hPw.1
          rw [hwa, hwire_gate x a halt, haop, hand_ev, Bool.and_eq_true] at hval
          have hnP0 := hPmin (PEqualNP.TopForm.opnd C a 0) (by have := hopnd_lt a halt 0; omega)
          have hnP1 := hPmin (PEqualNP.TopForm.opnd C a 1) (by have := hopnd_lt a halt 1; omega)
          have hex0 : ∃ i0 ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0), x i0 = true := by
            by_contra hall
            apply hnP0
            refine ⟨hval.1, fun i hi => ?_⟩
            by_cases hxi : x i = true
            · exact absurd ⟨i, hi, hxi⟩ hall
            · exact Bool.eq_false_iff.mpr hxi
          have hex1 : ∃ i1 ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1), x i1 = true := by
            by_contra hall
            apply hnP1
            refine ⟨hval.2, fun i hi => ?_⟩
            by_cases hxi : x i = true
            · exact absurd ⟨i, hi, hxi⟩ hall
            · exact Bool.eq_false_iff.mpr hxi
          obtain ⟨i0, hi0_mem, hi0_x⟩ := hex0
          obtain ⟨i1, hi1_mem, hi1_x⟩ := hex1
          have hne01 : i0 ≠ i1 := by
            intro heq
            subst heq
            have hv0 := horIn_sound (PEqualNP.TopForm.opnd C a 0) i0
              (PEqualNP.EdgeOwnership.pairInput i0 i0) hi0_mem
              ((hpi i0 i0 i0).mpr (Or.inl rfl))
            have hv1 := horIn_sound (PEqualNP.TopForm.opnd C a 1) i0
              (PEqualNP.EdgeOwnership.pairInput i0 i0) hi1_mem
              ((hpi i0 i0 i0).mpr (Or.inl rfl))
            have hva : PEqualNP.EdgeOwnership.gateVal n C a
                (PEqualNP.EdgeOwnership.pairInput i0 i0) = true := by
              change PEqualNP.CleanedNonEdge.wireVal n C (n + a)
                (PEqualNP.EdgeOwnership.pairInput i0 i0) = true
              rw [hwire_gate _ a halt, haop, hand_ev, hv0, hv1]; rfl
            have hgf := hbel (PEqualNP.EdgeOwnership.pairInput i0 i0) hva
            rw [hgraph_one i0] at hgf
            cases hgf
          have hi0_uv : i0 = u ∨ i0 = v := (hpi u v i0).mp hi0_x
          have hi1_uv : i1 = u ∨ i1 = v := (hpi u v i1).mp hi1_x
          have hpair_eq : s(i0, i1) = s(u, v) := by
            rcases hi0_uv with rfl | rfl <;> rcases hi1_uv with rfl | rfl
            · exact absurd rfl hne01
            · rfl
            · exact Sym2.eq_swap
            · exact absurd rfl hne01
          have ha_top : a ∈ PEqualNP.TopForm.tops G C := by
            unfold PEqualNP.TopForm.tops PEqualNP.TopForm.gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨halt, haop, hbel⟩
          have hstar_mem : s(u, v) ∈ PEqualNP.TopForm.starEdges G C := by
            unfold PEqualNP.TopForm.starEdges
            rw [Finset.mem_biUnion]
            refine ⟨a, ha_top, ?_⟩
            rw [Finset.mem_image]
            exact ⟨(i0, i1), Finset.mem_product.mpr ⟨hi0_mem, hi1_mem⟩, hpair_eq⟩
          exact he_not_star hstar_mem
        · have ha_junk : a ∈ PEqualNP.TopForm.junk G C := by
            unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨halt, haop, halt, ?_⟩
            by_contra hall
            apply hbel
            intro y hy
            by_cases hgy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true
            · exact hgy
            · exact absurd ⟨y, hy, Bool.eq_false_iff.mpr hgy⟩ hall
          have ha_gamma : s(u, v) ∈ PEqualNP.TopForm.gammaE G C a := by
            unfold PEqualNP.TopForm.gammaE
            rw [Finset.mem_filter]
            refine ⟨he_edge, u, v, rfl, ?_⟩
            have hval := hPw.1
            rw [hwa] at hval
            exact hval
          have ha_ne : a ≠ jtop := fun h => hjt (h ▸ ha_gamma)
          have ha_cone : PEqualNP.EdgeOwnership.InCone n C a jtop := by
            rcases hmax a ha_junk with rfl | hcone
            · exact absurd rfl ha_ne
            · exact hcone
          exact ⟨a, ha_junk, ha_ne, ha_cone, ha_gamma⟩
  have hcard_le : (PEqualNP.TopForm.Ustar G C).card ≤
      (PEqualNP.TopForm.Ustar G C ∩ PEqualNP.TopForm.gammaE G C jtop).card +
      ((PEqualNP.TopForm.Ustar G C \ PEqualNP.TopForm.gammaE G C jtop).filter fun e =>
        ∃ j ∈ PEqualNP.TopForm.junk G C, j ≠ jtop ∧ PEqualNP.EdgeOwnership.InCone n C j jtop ∧
          e ∈ PEqualNP.TopForm.gammaE G C j).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  calc
    (PEqualNP.TopForm.Ustar G C).card
        ≤ (PEqualNP.TopForm.Ustar G C ∩ PEqualNP.TopForm.gammaE G C jtop).card +
          ((PEqualNP.TopForm.Ustar G C \ PEqualNP.TopForm.gammaE G C jtop).filter fun e =>
            ∃ j ∈ PEqualNP.TopForm.junk G C, j ≠ jtop ∧ PEqualNP.EdgeOwnership.InCone n C j jtop ∧
              e ∈ PEqualNP.TopForm.gammaE G C j).card := hcard_le
    _ ≤ c1 * (C.size + 1) + c2 * (C.size + 1) := Nat.add_le_add hbound1 hbound2
    _ = (c1 + c2) * (C.size + 1) := (Nat.add_mul c1 c2 (C.size + 1)).symm
