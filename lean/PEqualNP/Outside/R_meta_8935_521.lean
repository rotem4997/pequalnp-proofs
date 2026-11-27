import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8935_521
    (hLedger : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
      x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card +
        (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ≤
        x4.size + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) ∧
      ∀ (x9 : Finset (Fin x1)),
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (x2.deleteEdges ↑(PEqualNP.TopForm.Ustar x2 x4)) x9 →
        x9.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card)
    (hNoOneJunk : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit)
      (x5 : Fin x1 → Bool),
      (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x5 x6 ≠ x5 x7) →
      PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 →
      (PEqualNP.TopForm.junk x2 x4).card ≠ (1 : ℕ))
    (hResidual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.IsBipartite → ¬ G.IsAcyclic → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∀ S : Finset (Fin n), G.IsVertexCover ↑S → C.size + 1 < G.edgeFinset.card + S.card) →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      1 ≤ (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card →
      3 ≤ (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card →
      5 ≤ 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card →
      3 ≤ (PEqualNP.TopForm.Ustar G C).card →
      (∀ A : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.Ustar G C, ∃ v ∈ A, v ∈ e) →
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
          A.card + (PEqualNP.TopForm.Ustar G C).card) →
      (∃ j ∈ PEqualNP.TopForm.junk G C,
        ∃ a b c d : Fin n, s(a, b) ∈ PEqualNP.TopForm.Ustar G C ∧
          s(c, d) ∈ PEqualNP.TopForm.Ustar G C ∧ s(a, b) ≠ s(c, d) ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a b) = true ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput c d) = true) →
      False) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ) := by
  classical
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro n G _ C hBip hCyc h4 hLeast hTop hWit
  by_contra hNoCover
  have hAllBad : ∀ S : Finset (Fin n), G.IsVertexCover ↑S → C.size + 1 < G.edgeFinset.card + S.card := by
    intro S hS
    by_contra hLe
    exact hNoCover ⟨S, hS, by omega⟩
  obtain ⟨fCol⟩ := hBip
  let col : Fin n → Bool := fun v => decide (fCol v = 0)
  have hbip : ∀ u v : Fin n, G.Adj u v → col u ≠ col v := by
    intro u v huv
    have hne : fCol u ≠ fCol v := fCol.valid huv
    have hu := (fCol u).isLt
    have hv := (fCol v).isLt
    have hval : (fCol u).val ≠ (fCol v).val := fun h => hne (Fin.ext h)
    dsimp only [col]
    by_cases h1 : fCol u = 0
    · have h2 : fCol v ≠ 0 := fun h => hne (h1.trans h.symm)
      rw [decide_eq_true h1, decide_eq_false h2]
      exact Bool.noConfusion
    · have h1v : (fCol u).val ≠ 0 := fun h => h1 (Fin.ext h)
      have h2v : (fCol v).val = 0 := by omega
      have h2 : fCol v = 0 := Fin.ext h2v
      rw [decide_eq_false h1, decide_eq_true h2]
      exact Bool.noConfusion
  obtain ⟨jw, hjwLt, hjwOp, hjwDirty, a1, b1, a2, b2, hadj1, hadj2, hne12, hnr1, hnr2, hgv1, hgv2⟩ := hWit
  have hEne : G.edgeFinset.Nonempty := ⟨s(a1, b1), SimpleGraph.mem_edgeFinset.mpr hadj1⟩
  obtain ⟨hLedIneq, hMinCov⟩ := hLedger n G C h4 hEne hLeast hTop
  let H : SimpleGraph (Fin n) := G.deleteEdges ↑(Ustar G C)
  let covers : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => ∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T)
  have hCoversNe : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u _ _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨K0, hK0mem, hK0min⟩ := Finset.exists_min_image covers Finset.card hCoversNe
  have hK0cov : ∀ u v : Fin n, H.Adj u v → u ∈ K0 ∨ v ∈ K0 := (Finset.mem_filter.mp hK0mem).2
  have hIsMinK0 : IsMinCover H K0 := by
    refine ⟨hK0cov, ?_⟩
    intro T' hT'
    exact hK0min T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)
  have hK0le : K0.card ≤ (tops G C \ centreless G C).card := hMinCov K0 hIsMinK0
  have hBudgetLtCov : ∀ A : Finset (Fin n), (∀ e ∈ Ustar G C, ∃ v ∈ A, v ∈ e) →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
        A.card + (Ustar G C).card := by
    intro A hA
    have hVC : G.IsVertexCover ↑(K0 ∪ A) := by
      intro u v huv
      by_cases hu : s(u, v) ∈ Ustar G C
      · obtain ⟨w, hwA, hwe⟩ := hA s(u, v) hu
        rcases Sym2.mem_iff.mp hwe with rfl | rfl
        · exact Or.inl (Finset.mem_union_right K0 hwA)
        · exact Or.inr (Finset.mem_union_right K0 hwA)
      · have hH : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, Finset.mem_coe.not.mpr hu⟩
        rcases hK0cov u v hH with huK | hvK
        · exact Or.inl (Finset.mem_union_left A huK)
        · exact Or.inr (Finset.mem_union_left A hvK)
    have hBad := hAllBad (K0 ∪ A) hVC
    have hUn := Finset.card_union_le K0 A
    omega
  have hBudgetLtTwoU :
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
        2 * (Ustar G C).card := by
    have hEx : ∀ e : Sym2 (Fin n), ∃ v : Fin n, v ∈ e := fun e =>
      Sym2.ind (fun u v => ⟨u, Sym2.mem_mk_left u v⟩) e
    choose pick hpick using hEx
    have hA := hBudgetLtCov ((Ustar G C).image pick) (by
      intro e he
      exact ⟨pick e, Finset.mem_image_of_mem pick he, hpick e⟩)
    have hImg : ((Ustar G C).image pick).card ≤ (Ustar G C).card := Finset.card_image_le
    omega
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  let stepWire : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_def : ∀ (C' : Circuit) (x : List Bool), C'.wires x = C'.gates.foldl stepWire x :=
    fun _ _ => rfl
  have size_def : ∀ (C' : Circuit), C'.size = C'.gates.length := fun _ => rfl
  have eval_def : ∀ (C' : Circuit) (x : List Bool), C'.eval x = (C'.wires x).getD C'.output false :=
    fun _ _ => rfl
  have circuitFun_def : ∀ (C' : Circuit) (x : Fin n → Bool),
      circuitFun n C' x = (C'.wires (List.ofFn x)).getD C'.output false := fun _ _ => rfl
  have graphFun_def : ∀ (x : Fin n → Bool),
      graphFun G ∅ x = (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  have gateAt_def : ∀ (C' : Circuit) (j : ℕ), gateAt C' j = C'.gates.getD j ⟨GateOp.or, []⟩ :=
    fun _ _ => rfl
  have gateVal_def : ∀ (C' : Circuit) (j : ℕ) (x : Fin n → Bool),
      gateVal n C' j x = (C'.wires (List.ofFn x)).getD (n + j) false := fun _ _ _ => rfl
  have opnd_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      opnd C' a b = (gateAt C' a).inputs.getD b.val 0 := fun _ _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin n), pairInput u v w = decide (w = u ∨ w = v) :=
    fun _ _ _ => rfl
  have pairInput_symm : ∀ (u v : Fin n), pairInput u v = pairInput v u := fun u v =>
    funext fun w => by simp only [pairInput_def, or_comm]
  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := by
    intro cs g
    change cs ++ [(g.inputs.filter (fun w => @decide (n ≤ w ∧ w < n + cs.length) _)).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])] = _
    congr 2
  have cones_def : ∀ (C' : Circuit), cones n C' = C'.gates.foldl (coneStep n) [] := fun _ => rfl
  have inCone_def : ∀ (C' : Circuit) (i j : ℕ), InCone n C' i j = (i ∈ (cones n C').getD j []) :=
    fun _ _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      orStep n cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := by
    intro cs g
    change cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
      ((g.inputs.filter (fun w => @decide (n ≤ w ∧ w < n + cs.length) _)).flatMap
        (fun w => cs.getD (w - n) [])) [])] = _
    by_cases hop : g.op = GateOp.or
    · rw [ite_eq_left hop]
    · rw [ite_eq_right hop]
  have orSets_def : ∀ (C' : Circuit), orSets n C' = C'.gates.foldl (orStep n) [] := fun _ => rfl
  have orReaches_def : ∀ (C' : Circuit) (w g : ℕ),
      OrReaches n C' w g = (n ≤ w ∧ g ∈ (orSets n C').getD (w - n) []) := fun _ _ _ => rfl
  have orIn_def : ∀ (C' : Circuit) (w : ℕ) (i : Fin n),
      i ∈ orIn n C' w ↔ ((i : ℕ) = w ∨ ∃ k < C'.gates.length,
        OrReaches n C' w k ∧ (gateAt C' k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C' k).inputs) := by
    intro C' w i
    exact (@Finset.mem_filter _ _ _ Finset.univ i).trans (by simp only [Finset.mem_univ, true_and])
  have side_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      side (n := n) C' a b = orIn n C' (opnd C' a b) := fun _ _ _ => rfl
  have tops_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ tops G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧ BelowF G C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have junk_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ junk G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C' j x = true ∧ graphFun G ∅ x = false := by
    intro C' j
    refine (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans ?_
    rw [Finset.mem_range]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.1, h.2.2⟩⟩
  have orN_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ orN G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.or ∧ ¬ BelowF G C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have lam_mem : ∀ (C' : Circuit) (h : ℕ),
      h ∈ lam G C' ↔ h ∈ orN G C' ∧ (orIn n C' (opnd C' h 0)).Nonempty ∧
        (orIn n C' (opnd C' h 1)).Nonempty ∧ ∃ a ∈ tops G C', ∃ b : Fin 2,
          (side (n := n) C' a (1 - b)).card = 1 ∧ OrReaches n C' (opnd C' a b) h := by
    intro C' h
    exact @Finset.mem_filter _ _ _ (orN G C') h
  have centreless_mem : ∀ (C' : Circuit) (a : ℕ),
      a ∈ centreless G C' ↔ a ∈ tops G C' ∧ (side (n := n) C' a 0 = ∅ ∨ side (n := n) C' a 1 = ∅) := by
    intro C' a
    exact @Finset.mem_filter _ _ _ (tops G C') a
  have readers_mem : ∀ (C' : Circuit) (j k : ℕ),
      k ∈ readers n C' j ↔ k < C'.gates.length ∧ n + j ∈ (gateAt C' k).inputs := by
    intro C' j k
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) k).trans (by rw [Finset.mem_range])
  have starEdges_def : ∀ (C' : Circuit),
      starEdges G C' = (tops G C').biUnion (fun a => (side (n := n) C' a 0 ×ˢ side (n := n) C' a 1).image (fun p => s(p.1, p.2))) :=
    fun _ => rfl
  have Ustar_def : ∀ (C' : Circuit), Ustar G C' = G.edgeFinset \ starEdges G C' := fun _ => rfl
  have foldl_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp only [stepWire, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val : Circuit → List Bool → ℕ → Bool := fun C' x u => (C'.wires x).getD u false
  have gateAt_eq : ∀ {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length), gateAt C' j = C'.gates[j] := by
    intro C' j hj
    rw [gateAt_def]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have gateAt_mem : ∀ {C' : Circuit} {j : ℕ}, j < C'.gates.length → gateAt C' j ∈ C'.gates := by
    intro C' j hj
    rw [gateAt_eq hj]
    exact List.getElem_mem hj
  have val_input : ∀ {C' : Circuit} {x : List Bool}, x.length = n → ∀ {u : ℕ}, u < n →
      val C' x u = x.getD u false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = _
    rw [wires_def]
    exact foldl_getD_lt _ _ _ (by omega)
  have val_ge : ∀ {C' : Circuit} {x : List Bool}, x.length = n → ∀ {u : ℕ}, n + C'.gates.length ≤ u →
      val C' x u = false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = false
    apply getD_ge
    rw [wires_def, foldl_length]
    omega
  have val_gate : ∀ {C' : Circuit} {x : List Bool}, x.length = n → ∀ {j : ℕ}, j < C'.gates.length →
      val C' x (n + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
        if i < n + j then val C' x i else false) := by
    intro C' x hx j hj
    rw [← hx]
    change (C'.wires x).getD (x.length + j) false = _
    rw [wires_def, gateAt_eq hj]
    exact foldl_getD_gate C'.gates x j hj
  have val_or : ∀ {C' : Circuit} {x : List Bool}, x.length = n → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.or →
      (val C' x (n + r) = true ↔ ∃ i ∈ (gateAt C' r).inputs, i < n + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_or]
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; exact Bool.noConfusion h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
  have val_and : ∀ {C' : Circuit} {x : List Bool}, x.length = n → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.and →
      (val C' x (n + r) = true ↔ ∀ i ∈ (gateAt C' r).inputs, i < n + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_and]
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; exact Bool.noConfusion h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2
  have val_ofFn : ∀ (C' : Circuit) (x : Fin n → Bool) (u : Fin n),
      val C' (List.ofFn x) u.val = x u := by
    intro C' x u
    rw [val_input (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]
  have val_mono : ∀ (C' : Circuit), IsAO2 n C' → ∀ (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) →
      ∀ w : ℕ, val C' (List.ofFn x) w = true → val C' (List.ofFn y) w = true := by
    intro C' hAO' x y hle w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwn : w < n
      · have hx := val_ofFn C' x ⟨w, hwn⟩
        have hy := val_ofFn C' y ⟨w, hwn⟩
        rw [hy]
        exact hle ⟨w, hwn⟩ (hx.symm.trans hw)
      · by_cases hoob : n + C'.gates.length ≤ w
        · rw [val_ge List.length_ofFn hoob] at hw
          exact Bool.noConfusion hw
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C'.gates.length := by omega
          rcases hAO'.1 _ (gateAt_mem hk) with hand | hor
          · have h1 := (val_and List.length_ofFn hk hand).mp hw
            exact (val_and List.length_ofFn hk hand).mpr (fun i hi =>
              ⟨(h1 i hi).1, ih i (h1 i hi).1 (h1 i hi).2⟩)
          · obtain ⟨i, hi, hlt, hvi⟩ := (val_or List.length_ofFn hk hor).mp hw
            exact (val_or List.length_ofFn hk hor).mpr ⟨i, hi, hlt, ih i hlt hvi⟩
  have gateVal_eq_val : ∀ (C' : Circuit) (j : ℕ) (x : Fin n → Bool),
      gateVal n C' j x = val C' (List.ofFn x) (n + j) := fun _ _ _ => rfl
  let shiftW : ℕ → ℕ → ℕ := fun k w => if w < n + k then w else w - 1
  let unshiftW : ℕ → ℕ → ℕ := fun k w => if w < n + k then w else w + 1
  let unshiftG : ℕ → ℕ → ℕ := fun k j => if j < k then j else j + 1
  let shiftGate : ℕ → Gate → Gate := fun k g => ⟨g.op, g.inputs.map (shiftW k)⟩
  let delDead : ℕ → Circuit → Circuit := fun k C' =>
    ⟨(C'.gates.eraseIdx k).map (shiftGate k), shiftW k C'.output⟩
  have unshiftW_shiftW : ∀ (k w : ℕ), w ≠ n + k → unshiftW k (shiftW k w) = w := by
    intro k w hne
    dsimp only [unshiftW, shiftW]
    split_ifs <;> omega
  have delDead_length : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      (delDead k C').gates.length = C'.gates.length - 1 := by
    intro k C' hk
    dsimp only [delDead]
    rw [List.length_map, List.length_eraseIdx_of_lt hk]
  have delDead_gateAt : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      ∀ j, j < (delDead k C').gates.length →
      gateAt (delDead k C') j = shiftGate k (gateAt C' (unshiftG k j)) := by
    intro k C' hk j hj
    have hj_lt : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj_e : j < (C'.gates.eraseIdx k).length := by rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
    rw [gateAt_eq hj]
    dsimp only [delDead, unshiftG]
    rw [List.getElem_map]
    split_ifs with hjk
    · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (by omega)]
    · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
  have delDead_readsBack : ∀ (k : ℕ) (C' : Circuit), ReadsBack n C' →
      k < C'.gates.length → (∀ j < C'.gates.length, n + k ∉ (gateAt C' j).inputs) →
      ReadsBack n (delDead k C') := by
    intro k C' hRB hk hno j hj w' hw'
    rw [delDead_gateAt k C' hk j hj] at hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    have hj_len : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
    have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
    have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
    dsimp only [shiftW]
    dsimp only [unshiftG] at hw_lt
    split_ifs at hw_lt ⊢ <;> omega
  have delDead_ao2 : ∀ (k : ℕ) (C' : Circuit), IsAO2 n C' →
      k < C'.gates.length → (∀ j < C'.gates.length, n + k ∉ (gateAt C' j).inputs) →
      IsAO2 n (delDead k C') := by
    intro k C' h hk hno
    have mapped : ∀ g ∈ (delDead k C').gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hm := List.mem_of_mem_eraseIdx hg'
      exact ⟨h.1 g' hm, by dsimp only [shiftGate]; rw [List.length_map]; exact h.2.2 g' hm⟩
    exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack k C' h.2.1 hk hno,
      fun g hg => (mapped g hg).2⟩
  have delDead_wires_eq : ∀ (k : ℕ) (C' : Circuit) (l : List Bool), l.length = n →
      ReadsBack n C' → k < C'.gates.length → (∀ j < C'.gates.length, n + k ∉ (gateAt C' j).inputs) →
      ∀ w : ℕ, val (delDead k C') l w = val C' l (unshiftW k w) := by
    intro k C' l hl hRB hk hno w
    have hRB' : ReadsBack n (delDead k C') := delDead_readsBack k C' hRB hk hno
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw_oob : n + (delDead k C').gates.length ≤ w
      · have hdl := delDead_length k C' hk
        have huw : n + C'.gates.length ≤ unshiftW k w := by dsimp only [unshiftW]; split_ifs <;> omega
        rw [val_ge hl hw_oob, val_ge hl huw]
      · by_cases hwn : w < n
        · have huw : unshiftW k w = w := by dsimp only [unshiftW]; split_ifs <;> omega
          rw [huw, val_input hl hwn, val_input hl hwn]
        · let j := w - n
          have hw_eq : w = n + j := by omega
          have hj_lt : j < (delDead k C').gates.length := by omega
          have hdl := delDead_length k C' hk
          have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
          have huw : unshiftW k (n + j) = n + unshiftG k j := by
            dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
          rw [hw_eq, huw, val_gate hl hj_lt, val_gate hl hj0_lt, delDead_gateAt k C' hk j hj_lt]
          dsimp only [shiftGate]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hu_lt' : shiftW k u < n + j := by
            have hmem : shiftW k u ∈ (gateAt (delDead k C') j).inputs := by
              rw [delDead_gateAt k C' hk j hj_lt]
              exact List.mem_map.mpr ⟨u, hu, rfl⟩
            exact hRB' j hj_lt (shiftW k u) hmem
          have hu_lt0 : u < n + unshiftG k j := hRB (unshiftG k j) hj0_lt u hu
          have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
          simp only [Function.comp_apply]
          rw [if_pos hu_lt', if_pos hu_lt0, ih (shiftW k u) (by omega), unshiftW_shiftW k u hu_ne]
  have leastReadAny : ∀ {j : ℕ}, j < C.gates.length → C.output ≠ n + j → (readers n C j).Nonempty := by
    intro j hj hout
    by_contra hnot
    have hno : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs := by
      intro k hk hin
      exact hnot ⟨k, (readers_mem C j k).mpr ⟨hk, hin⟩⟩
    have heq : circuitFun n (delDead j C) = circuitFun n C := by
      funext x
      rw [circuitFun_def, circuitFun_def]
      change val (delDead j C) (List.ofFn x) (shiftW j C.output) = val C (List.ofFn x) C.output
      rw [delDead_wires_eq j C (List.ofFn x) List.length_ofFn hLeast.1.2.1 hj hno,
        unshiftW_shiftW j C.output hout]
    have hle := hLeast.2.2 (delDead j C) (delDead_ao2 j C hLeast.1 hj hno) (heq.trans hLeast.2.1)
    have hlen := delDead_length j C hj
    rw [size_def, size_def] at hle
    omega
  have leastRead : ∀ {j : ℕ}, j < C.gates.length → ¬ BelowF G C j → (readers n C j).Nonempty := by
    intro j hj hd
    refine leastReadAny hj ?_
    intro heq
    apply hd
    intro x hx
    have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hLeast.2.1 x
    rw [heq] at h
    exact h.symm.trans hx
  have pairInput_left : ∀ u v : Fin n, pairInput u v u = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inl rfl)
  have pairInput_right : ∀ u v : Fin n, pairInput u v v = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inr rfl)
  have pairInput_true : ∀ u v w : Fin n, pairInput u v w = true ↔ w = u ∨ w = v := by
    intro u v w; rw [pairInput_def, decide_eq_true_eq]
  have graphFun_pair : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    rw [graphFun_def]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
  have hOutLt : C.output < n + C.gates.length := by
    by_contra hge
    have hv : val C (List.ofFn (pairInput a1 b1)) C.output = true := by
      have h : val C (List.ofFn (pairInput a1 b1)) C.output = graphFun G ∅ (pairInput a1 b1) :=
        congrFun hLeast.2.1 (pairInput a1 b1)
      rw [h]
      exact (graphFun_pair a1 b1).mpr hadj1
    rw [val_ge List.length_ofFn (by omega)] at hv
    exact Bool.noConfusion hv
  have replace_gate_by_input : ∀ (a : ℕ) (u0 : Fin n),
      a < C.gates.length → ¬ BelowF G C a →
      (∀ x : Fin n → Bool, x u0 = true → gateVal n C a x = true) →
      (∀ p q : Fin n, G.Adj p q → gateVal n C a (pairInput p q) = true → pairInput p q u0 = true) →
      False := by
    intro a u0 ha hnb hUp hDown
    have houtNe : C.output ≠ n + a := by
      intro heq
      apply hnb
      intro x hx
      have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hLeast.2.1 x
      rw [heq] at h
      exact h.symm.trans hx
    let repW : ℕ → ℕ := fun w => if w = n + a then u0.val else if w < n + a then w else w - 1
    let repGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map repW⟩
    let D : Circuit := ⟨(C.gates.eraseIdx a).map repGate, repW C.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by
      dsimp only [D]
      rw [List.length_map, List.length_eraseIdx_of_lt ha]
    have hDgate : ∀ j, j < D.gates.length → gateAt D j = repGate (gateAt C (unshiftG a j)) := by
      intro j hj
      have hj_lt : j < C.gates.length - 1 := by omega
      have hj_e : j < (C.gates.eraseIdx a).length := by rw [List.length_eraseIdx_of_lt ha]; exact hj_lt
      rw [gateAt_eq hj]
      dsimp only [D, unshiftG]
      rw [List.getElem_map]
      split_ifs with hja
      · rw [List.getElem_eraseIdx_of_lt hj_e hja, gateAt_eq (by omega)]
      · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
    have hDRB : ReadsBack n D := by
      intro j hj w' hw'
      rw [hDgate j hj] at hw'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
      have hj0 : unshiftG a j < C.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
      have hwlt : w < n + unshiftG a j := hLeast.1.2.1 (unshiftG a j) hj0 w hw
      have hu0 : u0.val < n := u0.isLt
      dsimp only [repW]
      dsimp only [unshiftG] at hwlt
      split_ifs at hwlt ⊢ <;> omega
    have hDAO : IsAO2 n D := by
      have mapped : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have hm := List.mem_of_mem_eraseIdx hg'
        exact ⟨hLeast.1.1 g' hm, by dsimp only [repGate]; rw [List.length_map]; exact hLeast.1.2.2 g' hm⟩
      exact ⟨fun g hg => (mapped g hg).1, hDRB, fun g hg => (mapped g hg).2⟩
    have hDleC : ∀ (x : Fin n → Bool) (w : ℕ),
        val D (List.ofFn x) w = true → val C (List.ofFn x) (unshiftW a w) = true := by
      intro x w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hoob : n + D.gates.length ≤ w
        · rw [val_ge List.length_ofFn hoob] at hw
          exact Bool.noConfusion hw
        · by_cases hwn : w < n
          · have huw : unshiftW a w = w := by dsimp only [unshiftW]; split_ifs <;> omega
            rw [huw]
            rw [val_input List.length_ofFn hwn] at hw ⊢
            exact hw
          · let j := w - n
            have hweq : w = n + j := by omega
            have hj : j < D.gates.length := by omega
            have hj0 : unshiftG a j < C.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
            have huw : unshiftW a (n + j) = n + unshiftG a j := by
              dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
            rw [hweq] at hw
            rw [hweq, huw]
            have hstep : ∀ u ∈ (gateAt C (unshiftG a j)).inputs,
                val D (List.ofFn x) (repW u) = true → val C (List.ofFn x) u = true := by
              intro u hu hvu
              by_cases hua : u = n + a
              · subst u
                have hrep : repW (n + a) = u0.val := by dsimp only [repW]; rw [if_pos rfl]
                rw [hrep, val_ofFn] at hvu
                exact hUp x hvu
              · have hlt : repW u < n + j := hDRB j hj (repW u) (by rw [hDgate j hj]; exact List.mem_map.mpr ⟨u, hu, rfl⟩)
                have hinv : unshiftW a (repW u) = u := by dsimp only [unshiftW, repW]; split_ifs <;> omega
                have hih := ih (repW u) (by omega) hvu
                rwa [hinv] at hih
            have hopEq : (gateAt D j).op = (gateAt C (unshiftG a j)).op := by
              rw [hDgate j hj]
            rcases hLeast.1.1 _ (gateAt_mem hj0) with hand | hor
            · have h1 := (val_and List.length_ofFn hj (hopEq.trans hand)).mp hw
              exact (val_and List.length_ofFn hj0 hand).mpr (fun u hu =>
                ⟨hLeast.1.2.1 _ hj0 u hu, hstep u hu (h1 (repW u) (by rw [hDgate j hj]; exact List.mem_map.mpr ⟨u, hu, rfl⟩)).2⟩)
            · obtain ⟨u', hu', _, hvu'⟩ := (val_or List.length_ofFn hj (hopEq.trans hor)).mp hw
              rw [hDgate j hj] at hu'
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
              exact (val_or List.length_ofFn hj0 hor).mpr ⟨u, hu, hLeast.1.2.1 _ hj0 u hu, hstep u hu hvu'⟩
    have hCleD : ∀ (p q : Fin n), G.Adj p q → ∀ (w0 : ℕ), w0 < n + C.gates.length →
        val C (List.ofFn (pairInput p q)) w0 = true →
        val D (List.ofFn (pairInput p q)) (repW w0) = true := by
      intro p q hpq w0
      induction w0 using Nat.strong_induction_on with
      | ind w0 ih =>
        intro hw0lt hw0
        by_cases hwn : w0 < n
        · have hrep : repW w0 = w0 := by dsimp only [repW]; split_ifs <;> omega
          rw [hrep]
          rw [val_input List.length_ofFn hwn] at hw0 ⊢
          exact hw0
        · by_cases hwa : w0 = n + a
          · subst w0
            have hrep : repW (n + a) = u0.val := by dsimp only [repW]; rw [if_pos rfl]
            rw [hrep, val_ofFn]
            exact hDown p q hpq hw0
          · let j0 := w0 - n
            have hw0eq : w0 = n + j0 := by omega
            have hj0 : j0 < C.gates.length := by omega
            have hj0ne : j0 ≠ a := by omega
            let j := if j0 < a then j0 else j0 - 1
            have hj : j < D.gates.length := by dsimp only [j]; split_ifs <;> omega
            have hrep : repW w0 = n + j := by dsimp only [repW, j]; split_ifs <;> omega
            have hun : unshiftG a j = j0 := by dsimp only [unshiftG, j]; split_ifs <;> omega
            have hopEq : (gateAt D j).op = (gateAt C j0).op := by
              rw [hDgate j hj, hun]
            rw [hw0eq] at hw0
            rw [hrep]
            rcases hLeast.1.1 _ (gateAt_mem hj0) with hand | hor
            · have h1 := (val_and List.length_ofFn hj0 hand).mp hw0
              refine (val_and List.length_ofFn hj (hopEq.trans hand)).mpr ?_
              intro u' hu'
              have hlt' := hDRB j hj u' hu'
              rw [hDgate j hj, hun] at hu'
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
              have hult := (h1 u hu).1
              exact ⟨hlt', ih u (by omega) (by omega) (h1 u hu).2⟩
            · obtain ⟨u, hu, hult, hvu⟩ := (val_or List.length_ofFn hj0 hor).mp hw0
              have hu' : repW u ∈ (gateAt D j).inputs := by
                rw [hDgate j hj, hun]
                exact List.mem_map.mpr ⟨u, hu, rfl⟩
              exact (val_or List.length_ofFn hj (hopEq.trans hor)).mpr
                ⟨repW u, hu', hDRB j hj _ hu', ih u (by omega) (by omega) hvu⟩
    have hDcomp : circuitFun n D = graphFun G ∅ := by
      funext x
      rw [circuitFun_def]
      change val D (List.ofFn x) (repW C.output) = graphFun G ∅ x
      cases hgx : graphFun G ∅ x with
      | false =>
        cases hdx : val D (List.ofFn x) (repW C.output) with
        | false => rfl
        | true =>
          have hinv : unshiftW a (repW C.output) = C.output := by
            dsimp only [unshiftW, repW]; split_ifs <;> omega
          have hc := hDleC x (repW C.output) hdx
          rw [hinv] at hc
          have hceq : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hLeast.2.1 x
          rw [hceq, hgx] at hc
          exact Bool.noConfusion hc
      | true =>
        rw [graphFun_def] at hgx
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
          decide_eq_true_eq] at hgx
        obtain ⟨p, q, hpq, hxp, hxq⟩ := hgx
        have hcpq : val C (List.ofFn (pairInput p q)) C.output = true := by
          have h := congrFun hLeast.2.1 (pairInput p q)
          change val C (List.ofFn (pairInput p q)) C.output = _ at h
          rw [h]
          exact (graphFun_pair p q).mpr hpq
        have hdpq := hCleD p q hpq C.output hOutLt hcpq
        exact val_mono D hDAO (pairInput p q) x (fun i hi => by
          rcases (pairInput_true p q i).mp hi with rfl | rfl
          · exact hxp
          · exact hxq) (repW C.output) hdpq
    have hle := hLeast.2.2 D hDAO hDcomp
    rw [size_def, size_def, hDlen] at hle
    omega
  let OrStep : ℕ → ℕ → Prop := fun w w' =>
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k
  have orStep_up : ∀ {x : List Bool}, x.length = n → ∀ {w w' : ℕ},
      Relation.ReflTransGen OrStep w w' → val C x w' = true → val C x w = true := by
    intro x hx w w' h hv
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
  have or_trace : ∀ {x : List Bool}, x.length = n → ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen OrStep w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
    intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < n
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : n + C.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; exact Bool.noConfusion hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hop : (gateAt C k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
  have operand_trace : ∀ (u v : Fin n) (p : ℕ), val C (List.ofFn (pairInput u v)) p = true →
      (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val) ∨
      (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
        Relation.ReflTransGen OrStep p (n + h) ∧
        val C (List.ofFn (pairInput u v)) (n + h) = true) := by
    intro u v p hv
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (by simp) p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left
      refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right
      exact ⟨h, hh, hop, hr, hv'⟩
  have reach_var_val : ∀ (x : Fin n → Bool) (p : ℕ) (t : Fin n),
      Relation.ReflTransGen OrStep p t.val → x t = true → val C (List.ofFn x) p = true :=
    fun x p t hr ht => orStep_up (by simp) hr (by rw [val_ofFn]; exact ht)
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, coneStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        rw [coneStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have inCone_iff : ∀ i j : ℕ, InCone n C i j ↔
      j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k) := by
    intro i j
    have h := cones_char C.gates i j
    rw [inCone_def, cones_def, gateAt_def, h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - n, by omega, ?_, ?_⟩
      · have he : n + (w - n) = w := by omega
        rw [he]; exact hw
      · rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by rw [inCone_def, cones_def]; exact h3)
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      have he : n + k - n = k := by omega
      rw [he]
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by rw [inCone_def, cones_def] at h3; exact h3)
  have inCone_lt : ∀ {i j : ℕ}, InCone n C i j → i < j := by
    intro i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro h
      obtain ⟨_, k, hk, _, rfl | hic⟩ := (inCone_iff i j).mp h
      · exact hk
      · exact lt_trans (ih k hk hic) hk
  have inCone_trans : ∀ {i j k : ℕ}, InCone n C i j → InCone n C j k → InCone n C i k := by
    intro i j k hij
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hjk
      obtain ⟨hklen, r, hr, hrin, rfl | hjr⟩ := (inCone_iff j k).mp hjk
      · exact (inCone_iff i k).mpr ⟨hklen, j, hr, hrin, Or.inr hij⟩
      · exact (inCone_iff i k).mpr ⟨hklen, r, hr, hrin, Or.inr (ih r hr hjr)⟩
  have orStep_le : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' → w' ≤ w := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_refl _
    | head hstep _ ih =>
      obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
      omega
  have orStep_cone : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
      ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
      subst hk1
      right
      exact (inCone_iff h' k0).mpr ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
  have operand_cone : ∀ {a p h : ℕ}, a < C.gates.length → p ∈ (gateAt C a).inputs → p < n + a →
      Relation.ReflTransGen OrStep p (n + h) → InCone n C h a := by
    intro a p h ha hin hp hr
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
    exact (inCone_iff h a).mpr ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, orStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk
        rw [orStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            rw [orStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            rw [orStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact False.elim (hop hop2)
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          rw [orStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have orReaches_iff : ∀ k g : ℕ, OrReaches n C (n + k) g ↔
      k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    intro k g
    have h := orSets_char C.gates g k
    rw [orReaches_def, orSets_def, gateAt_def]
    have e : n + k - n = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, by rw [orReaches_def, orSets_def]; exact ⟨h1, h3⟩⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1⟩
      · exact Or.inl h3
      · rw [orReaches_def, orSets_def] at h1
        exact Or.inr ⟨hop, w, hw, h1.1, h2, h1.2⟩
  have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStep w w2 →
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    intro w w2 h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
  have orReaches_reach : ∀ (g w : ℕ), OrReaches n C w g →
      Relation.ReflTransGen OrStep w (n + g) ∧ g < C.gates.length := by
    intro g w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      rw [orReaches_def] at h
      have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have h' : OrReaches n C (n + k) g := by rw [orReaches_def]; exact h
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h'
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
  have mem_orIn_reach : ∀ {p : ℕ} (u : Fin n), u ∈ orIn n C p → Relation.ReflTransGen OrStep p u.val := by
    intro p u hu
    rcases (orIn_def C p u).mp hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn : ∀ {p : ℕ} (u : Fin n), Relation.ReflTransGen OrStep p u.val → u ∈ orIn n C p := by
    intro p u hr
    apply (orIn_def C p u).mpr
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have orIn_mono : ∀ {w g : ℕ}, OrReaches n C w g → orIn n C (n + g) ⊆ orIn n C w := by
    intro w g hr u hu
    exact reach_mem_orIn u ((orReaches_reach g w hr).1.trans (mem_orIn_reach u hu))
  have topData : ∀ {a : ℕ}, a ∈ tops G C → a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a :=
    fun ha => (tops_mem C _).mp ha
  have junkData : ∀ {a : ℕ}, a ∈ junk G C →
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false :=
    fun ha => (junk_mem C _).mp ha
  have binaryInputs : ∀ {a : ℕ}, a < C.gates.length → ∃ p q, (gateAt C a).inputs = [p, q] :=
    fun ha => List.length_eq_two.mp (hLeast.1.2.2 _ (gateAt_mem ha))
  have opndMem : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b ∈ (gateAt C a).inputs := by
    intro a ha b
    obtain ⟨p, q, hpq⟩ := binaryInputs ha
    rw [opnd_def, hpq]
    fin_cases b <;> simp
  have opndBound : ∀ {a : ℕ}, a < C.gates.length → ∀ b : Fin 2, opnd C a b < n + a :=
    fun ha b => hLeast.1.2.1 _ ha _ (opndMem ha b)
  have andValBoth : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ x : Fin n → Bool, gateVal n C a x = true ↔
        val C (List.ofFn x) (opnd C a 0) = true ∧ val C (List.ofFn x) (opnd C a 1) = true := by
    intro a ha hop x
    rw [gateVal_eq_val, val_and (by simp) ha hop]
    constructor
    · intro h
      exact ⟨(h _ (opndMem ha 0)).2, (h _ (opndMem ha 1)).2⟩
    · intro h i hi
      refine ⟨hLeast.1.2.1 a ha i hi, ?_⟩
      obtain ⟨p, q, hpq⟩ := binaryInputs ha
      rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
      · have h0 : opnd C a 0 = i := by rw [opnd_def, hpq]; rfl
        rw [← h0]; exact h.1
      · have e : i = q := List.mem_singleton.mp hq
        subst i
        have h1 : opnd C a 1 = q := by rw [opnd_def, hpq]; rfl
        rw [← h1]; exact h.2
  have andValOperands : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ x : Fin n → Bool, gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
    intro a ha hop x
    rw [andValBoth ha hop]
    constructor
    · intro h b; fin_cases b; exact h.1; exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  have operandReachCone : ∀ {a h : ℕ}, a < C.gates.length → ∀ {b : Fin 2},
      OrReaches n C (opnd C a b) h → InCone n C h a := by
    intro a h ha b hr
    exact operand_cone ha (opndMem ha b) (opndBound ha b) (orReaches_reach h _ hr).1
  have operandOrAndJunk : ∀ {a h : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ {b : Fin 2}, OrReaches n C (opnd C a b) h → (gateAt C h).op = GateOp.and → h ∈ junk G C := by
    intro a h ha hop b hr hh
    have hlen := (orReaches_reach h _ hr).2
    have hnb : ¬ BelowF G C h := fun hb => hTop h hlen a ha hh hb hop (operandReachCone ha hr)
    have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
      by_contra hne
      apply hnb
      intro x hx
      by_contra hf
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact (junk_mem C h).mpr ⟨hlen, hh, hdirty⟩
  have inputsAsOpnd : ∀ {k z : ℕ}, k < C.gates.length → z ∈ (gateAt C k).inputs → ∃ b : Fin 2, z = opnd C k b := by
    intro k z hk hz
    obtain ⟨p, q, hpq⟩ := binaryInputs hk
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by rw [opnd_def, hpq]; rfl⟩
    · have e : z = q := List.mem_singleton.mp hq
      exact ⟨1, by rw [opnd_def, hpq]; exact e⟩
  have sideVal : ∀ {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n},
      t ∈ side (n := n) C a b → x t = true → val C (List.ofFn x) (opnd C a b) = true := by
    intro a b x t ht hx
    rw [side_def] at ht
    exact reach_var_val x _ t (mem_orIn_reach t ht) hx
  have topAdj : ∀ {a : ℕ}, a ∈ tops G C → ∀ {u v : Fin n},
      u ∈ side (n := n) C a 0 → v ∈ side (n := n) C a 1 → G.Adj u v := by
    intro a ha u v hu hv
    obtain ⟨hl, ho, hb⟩ := topData ha
    exact (graphFun_pair u v).mp
      (hb _ ((andValBoth hl ho _).mpr ⟨sideVal hu (pairInput_left u v), sideVal hv (pairInput_right u v)⟩))
  have acceptedTop : ∀ {u v : Fin n}, G.Adj u v → ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
    intro u v hadj'
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
      fun x => congrFun hLeast.2.1 x
    have huv : val C (List.ofFn (pairInput u v)) C.output = true := by
      rw [hout]; exact (graphFun_pair u v).mpr hadj'
    rcases operand_trace u v C.output huv with ⟨t, _, hr⟩ | ⟨a, hl, ho, hr, hv⟩
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact G.irrefl ((graphFun_pair t t).mp h1)
    · have hand := (hLeast.1.1 _ (gateAt_mem hl)).resolve_right ho
      have hb : BelowF G C a := fun x hx => by
        rw [← hout x]
        exact orStep_up (by simp) hr (gateVal_eq_val C a x ▸ hx)
      exact ⟨a, (tops_mem C a).mpr ⟨hl, hand, hb⟩, hv⟩
  have operandSupport : ∀ {a : ℕ}, a < C.gates.length → (gateAt C a).op = GateOp.and →
      ∀ {b : Fin 2} {u v : Fin n}, val C (List.ofFn (pairInput u v)) (opnd C a b) = true →
      (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
    intro a ha ho b u v h
    rcases operand_trace u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
    · exact Or.inl ⟨t, by rw [side_def]; exact reach_mem_orIn t hr, ht⟩
    · have hr' := reach_orReaches hr j rfl hj
      exact Or.inr ⟨j, operandOrAndJunk ha ho hr' ((hLeast.1.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
  have andRawEmpty : ∀ {j : ℕ}, (gateAt C j).op = GateOp.and → orIn n C (n + j) = ∅ := by
    intro j hj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rcases (orIn_def C (n + j) v).mp hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt; omega
    · rcases (orReaches_iff j k).mp hr with ⟨_, rfl | ⟨hof, _⟩⟩
      · rw [hj] at ho; exact GateOp.noConfusion ho
      · rw [hj] at hof; exact GateOp.noConfusion hof
  have lastOrBefore : ∀ {j w : ℕ}, Relation.ReflTransGen OrStep w (n + j) →
      w = n + j ∨ ∃ r, r < C.gates.length ∧ (gateAt C r).op = GateOp.or ∧
        n + j ∈ (gateAt C r).inputs ∧ n + j < n + r ∧ Relation.ReflTransGen OrStep w (n + r) := by
    intro j w hr
    rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
    · exact Or.inl eq.symm
    · obtain ⟨r, hrlen, rfl, ho, hi, hb⟩ := hstep
      exact Or.inr ⟨r, hrlen, ho, hi, hb, hz⟩
  have lastOrOutside : ∀ {j r : ℕ}, j ∈ junk G C → r < C.gates.length → (gateAt C r).op = GateOp.or →
      n + j ∈ (gateAt C r).inputs → n + j < n + r → r ∈ orN G C \ lam G C := by
    intro j r hj hr ho hi hb
    obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
    have hNotBelow : ¬ BelowF G C r := by
      intro h
      have hvr : gateVal n C r x = true := (val_or (by simp) hr ho).mpr ⟨n + j, hi, hb, hjx⟩
      exact Bool.noConfusion (hx.symm.trans (h x hvr))
    refine Finset.mem_sdiff.mpr ⟨(orN_mem C r).mpr ⟨hr, ho, hNotBelow⟩, ?_⟩
    intro hl
    obtain ⟨_, h0, h1, _⟩ := (lam_mem C r).mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hr hi
    have hne : (orIn n C (opnd C r b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty hjop] at hne
    exact Finset.not_nonempty_empty hne
  have residualTrace : ∀ {u v : Fin n}, s(u, v) ∈ Ustar G C →
      ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true ∧ ∃ b : Fin 2, ∃ j ∈ junk G C,
        OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
    intro u v he
    rw [Ustar_def] at he
    obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
    have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
    obtain ⟨a, ha, hv⟩ := acceptedTop adj'
    obtain ⟨hl, ho, _⟩ := topData ha
    have h := (andValOperands hl ho _).mp hv
    rcases operandSupport hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
    · rcases operandSupport hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
      · have hxy : x ≠ y := (topAdj ha hx hy).ne
        apply False.elim (miss ?_)
        rw [starEdges_def]
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
        rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
        · exact (hxy rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hxy rfl).elim
      · exact ⟨a, ha, hv, 1, j, hj, hr, hjv⟩
    · exact ⟨a, ha, hv, 0, j, hj, hr, hjv⟩
  have readData : ∀ {j k : ℕ}, k ∈ readers n C j → k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs :=
    fun hk => (readers_mem C _ _).mp hk
  have readLt : ∀ {j k : ℕ}, k ∈ readers n C j → j < k := by
    intro j k hk
    have hlt := hLeast.1.2.1 k (readData hk).1 _ (readData hk).2
    omega
  have top_orReaches_output : ∀ {t : ℕ}, t ∈ tops G C → Relation.ReflTransGen OrStep C.output (n + t) := by
    intro t ht
    obtain ⟨htlen, htop, htb⟩ := topData ht
    have hclimb : ∀ (d : ℕ) (k : ℕ), k < C.gates.length → C.gates.length - k ≤ d →
        Relation.ReflTransGen OrStep (n + k) (n + t) → Relation.ReflTransGen OrStep C.output (n + t) := by
      intro d
      induction d with
      | zero => intro k hk hle _; omega
      | succ d ih =>
        intro k hk hle hkt
        by_cases hout : C.output = n + k
        · rw [hout]; exact hkt
        · obtain ⟨r, hr⟩ := leastReadAny hk hout
          have hrlen := (readData hr).1
          have hrin := (readData hr).2
          have hkr : k < r := readLt hr
          have htr : InCone n C t r := by
            rcases orStep_cone hkt k t rfl rfl with rfl | htkc
            · exact (inCone_iff t r).mpr ⟨hrlen, t, hkr, hrin, Or.inl rfl⟩
            · exact (inCone_iff t r).mpr ⟨hrlen, k, hkr, hrin, Or.inr htkc⟩
          have hrop : (gateAt C r).op = GateOp.or := by
            rcases hLeast.1.1 _ (gateAt_mem hrlen) with hand | hor
            · exact False.elim (hTop t htlen r hrlen htop htb hand htr)
            · exact hor
          have hstep : OrStep (n + r) (n + k) := ⟨r, hrlen, rfl, hrop, hrin, by omega⟩
          exact ih r hrlen (by omega) (Relation.ReflTransGen.head hstep hkt)
    exact hclimb C.gates.length t htlen (by omega) Relation.ReflTransGen.refl
  have readsAtMost_false_mem_Ustar : ∀ (u v : Fin n), G.Adj u v →
      readsAtMost C n [u.val, v.val] 1 = false → s(u, v) ∈ Ustar G C := by
    intro u v huv hnr
    by_contra hnotU
    rw [Ustar_def] at hnotU
    have hstar : s(u, v) ∈ starEdges G C := by
      by_contra hms
      exact hnotU (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv, hms⟩)
    rw [starEdges_def] at hstar
    obtain ⟨t, ht, hp⟩ := Finset.mem_biUnion.mp hstar
    obtain ⟨p, hpm, hpeq⟩ := Finset.mem_image.mp hp
    obtain ⟨hp0, hp1⟩ := Finset.mem_product.mp hpm
    have huvNe : u.val ≠ v.val := fun h => G.irrefl ((Fin.ext h) ▸ huv)
    let S : List ℕ := [u.val, v.val]
    let rstepOr : List (List (List ℕ)) → Gate → List (List (List ℕ)) := fun R g =>
      R ++ [(g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []]
    let rstepAnd : List (List (List ℕ)) → Gate → List (List (List ℕ)) := fun R g =>
      R ++ [(g.inputs.map fun i => R.getD i []).foldl (andStep 1) [S.map fun _ => 0]]
    let rstep : List (List (List ℕ)) → Gate → List (List (List ℕ)) := fun R g =>
      if g.op = GateOp.or then rstepOr R g else if g.op = GateOp.and then rstepAnd R g else R ++ [[]]
    let rvInit : List (List (List ℕ)) := (List.range n).map (leafVectors S 1)
    have hrv_eq : readVectors C n S 1 = C.gates.foldl rstep rvInit := by
      change C.gates.foldl _ rvInit = C.gates.foldl rstep rvInit
      congr 1
      funext R g
      cases h : g.op <;>
        simp only [rstep, rstepOr, rstepAnd, h, ite_true, ite_false, reduceCtorEq]
    have hins_mem : ∀ (A : List (List ℕ)) (x y : List ℕ), (x ∈ A ∨ x = y) → x ∈ insertNew A y := by
      intro A x y h
      change x ∈ (if y ∈ A then A else A ++ [y])
      by_cases hy : y ∈ A
      · rw [if_pos hy]
        rcases h with hx | rfl
        · exact hx
        · exact hy
      · rw [if_neg hy, List.mem_append, List.mem_singleton]
        exact h
    have hfold_ins : ∀ (L acc : List (List ℕ)) (x : List ℕ), (x ∈ acc ∨ x ∈ L) → x ∈ L.foldl insertNew acc := by
      intro L
      induction L with
      | nil =>
        intro acc x h
        rcases h with h | h
        · exact h
        · exact False.elim (List.not_mem_nil h)
      | cons y ys ih =>
        intro acc x h
        rw [List.foldl_cons]
        apply ih
        rcases h with hacc | hmem
        · exact Or.inl (hins_mem acc x y (Or.inl hacc))
        · rcases List.mem_cons.mp hmem with rfl | hys
          · exact Or.inl (hins_mem acc x x (Or.inr rfl))
          · exact Or.inr hys
    have hfold_or : ∀ (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (x : List ℕ),
        (x ∈ acc ∨ ∃ A ∈ Ls, x ∈ A) → x ∈ Ls.foldl (fun a B => B.foldl insertNew a) acc := by
      intro Ls
      induction Ls with
      | nil =>
        intro acc x h
        rcases h with h | ⟨_, h, _⟩
        · exact h
        · exact False.elim (List.not_mem_nil h)
      | cons B Bs ih =>
        intro acc x h
        rw [List.foldl_cons]
        apply ih
        rcases h with hacc | ⟨A, hA, hxA⟩
        · exact Or.inl (hfold_ins B acc x (Or.inl hacc))
        · rcases List.mem_cons.mp hA with rfl | hBs
          · exact Or.inl (hfold_ins A acc x (Or.inr hxA))
          · exact Or.inr ⟨A, hBs, hxA⟩
    have handStep_mem : ∀ (A B : List (List ℕ)) (x y : List ℕ),
        x ∈ A → y ∈ B → capAdd 1 x y ∈ andStep 1 A B := by
      intro A B x y hx hy
      change capAdd 1 x y ∈ (A.flatMap fun u' => B.map fun v' => capAdd 1 u' v').foldl insertNew []
      apply hfold_ins
      right
      exact List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩
    have hrstep_len : ∀ (R : List (List (List ℕ))) (g : Gate), (rstep R g).length = R.length + 1 := by
      intro R g
      dsimp only [rstep, rstepOr, rstepAnd]
      split_ifs <;> simp only [List.length_append, List.length_singleton]
    have hrv_len : ∀ (gs : List Gate) (R : List (List (List ℕ))),
        (gs.foldl rstep R).length = R.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro R; simp
      | cons g gs ih =>
        intro R
        rw [List.foldl_cons, ih, hrstep_len]
        simp only [List.length_cons]
        omega
    have hrv_getD_lt : ∀ (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ), i < R.length →
        (gs.foldl rstep R).getD i [] = R.getD i [] := by
      intro gs
      induction gs with
      | nil => intro _ _ _; rfl
      | cons g gs ih =>
        intro R i hi
        rw [List.foldl_cons, ih (rstep R g) i (by rw [hrstep_len]; omega)]
        dsimp only [rstep, rstepOr, rstepAnd]
        split_ifs <;> simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have hrv_at : ∀ (gs : List Gate) (R : List (List (List ℕ))) (j : ℕ) (hj : j < gs.length),
        (gs.foldl rstep R).getD (R.length + j) [] =
          ((gs.take j).foldl rstep R |> fun Rj =>
            if (gs[j]).op = GateOp.or then
              ((gs[j]).inputs.map fun i => Rj.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
            else if (gs[j]).op = GateOp.and then
              ((gs[j]).inputs.map fun i => Rj.getD i []).foldl (andStep 1) [S.map fun _ => 0]
            else []) := by
      intro gs R j hj
      have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
        calc gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
          _ = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
          _ = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by simp only [List.append_assoc, List.singleton_append]
      have hlenJ : ((gs.take j).foldl rstep R).length = R.length + j := by
        rw [hrv_len, List.length_take, Nat.min_eq_left (by omega)]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hrv_getD_lt (gs.drop (j + 1)) _ (R.length + j) (by rw [hrstep_len, hlenJ]; omega)]
      rw [← hlenJ]
      generalize (gs.take j).foldl rstep R = Rj
      dsimp only [rstep, rstepOr, rstepAnd]
      split_ifs <;>
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    have hrv_take_getD : ∀ (j i : ℕ), j < C.gates.length → i < n + j →
        ((C.gates.take j).foldl rstep rvInit).getD i [] = (readVectors C n S 1).getD i [] := by
      intro j i hj hi
      have hlenInit : rvInit.length = n := by dsimp only [rvInit]; rw [List.length_map, List.length_range]
      have hlenJ : ((C.gates.take j).foldl rstep rvInit).length = n + j := by
        rw [hrv_len, hlenInit, List.length_take, Nat.min_eq_left (by omega)]
      rw [hrv_eq]
      conv_rhs => rw [← List.take_append_drop j C.gates]
      rw [List.foldl_append, hrv_getD_lt (C.gates.drop j) _ i (by omega)]
    have hrv_orStep : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
        ∀ vec : List ℕ, vec ∈ (readVectors C n S 1).getD w' [] →
          vec ∈ (readVectors C n S 1).getD w [] := by
      intro w w' h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro vec hv; exact hv
      | head hstep _ ih =>
        intro vec hv
        obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
        have hv' := ih vec hv
        have hlenInit : rvInit.length = n := by dsimp only [rvInit]; rw [List.length_map, List.length_range]
        rw [hrv_eq]
        have hat := hrv_at C.gates rvInit k hk
        rw [hlenInit] at hat
        rw [hat]
        dsimp only
        have hgk : C.gates[k] = gateAt C k := (gateAt_eq hk).symm
        rw [hgk, if_pos hop]
        apply hfold_or
        right
        refine ⟨((C.gates.take k).foldl rstep rvInit).getD _ [], List.mem_map.mpr ⟨_, hin, rfl⟩, ?_⟩
        rw [hrv_take_getD k _ hk hlt]
        exact hv'
    have hrv_leaf_u : [1, 0] ∈ (readVectors C n S 1).getD u.val [] := by
      have hlenInit : rvInit.length = n := by dsimp only [rvInit]; rw [List.length_map, List.length_range]
      rw [hrv_eq, hrv_getD_lt C.gates rvInit u.val (by omega)]
      dsimp only [rvInit]
      have hget : ((List.range n).map (leafVectors S 1)).getD u.val [] = leafVectors S 1 u.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range u.isLt]
        rfl
      rw [hget]
      have hmem : u.val ∈ S := List.mem_cons_self
      change [1, 0] ∈ (if u.val ∈ S then [S.map fun j => if j = u.val then min 1 (1 + 1) else 0] else [])
      rw [if_pos hmem]
      dsimp only [S]
      simp [huvNe.symm]
    have hrv_leaf_v : [0, 1] ∈ (readVectors C n S 1).getD v.val [] := by
      have hlenInit : rvInit.length = n := by dsimp only [rvInit]; rw [List.length_map, List.length_range]
      rw [hrv_eq, hrv_getD_lt C.gates rvInit v.val (by omega)]
      dsimp only [rvInit]
      have hget : ((List.range n).map (leafVectors S 1)).getD v.val [] = leafVectors S 1 v.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range v.isLt]
        rfl
      rw [hget]
      have hmem : v.val ∈ S := List.mem_cons_of_mem u.val List.mem_cons_self
      change [0, 1] ∈ (if v.val ∈ S then [S.map fun j => if j = v.val then min 1 (1 + 1) else 0] else [])
      rw [if_pos hmem]
      dsimp only [S]
      simp [huvNe]
    obtain ⟨htlen, htop, _⟩ := topData ht
    obtain ⟨i0, i1, hi01⟩ := binaryInputs htlen
    have h0eq : opnd C t 0 = i0 := by rw [opnd_def, hi01]; rfl
    have h1eq : opnd C t 1 = i1 := by rw [opnd_def, hi01]; rfl
    have htop11 : [1, 1] ∈ (readVectors C n S 1).getD (n + t) [] := by
      have hlenInit : rvInit.length = n := by dsimp only [rvInit]; rw [List.length_map, List.length_range]
      have hneOr : (gateAt C t).op ≠ GateOp.or := by rw [htop]; exact GateOp.noConfusion
      have hpairMem : ([1, 0] ∈ (readVectors C n S 1).getD i0 [] ∧ [0, 1] ∈ (readVectors C n S 1).getD i1 []) ∨
          ([0, 1] ∈ (readVectors C n S 1).getD i0 [] ∧ [1, 0] ∈ (readVectors C n S 1).getD i1 []) := by
        rcases Sym2.eq_iff.mp hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left
          rw [side_def, h0eq] at hp0
          rw [side_def, h1eq] at hp1
          exact ⟨hrv_orStep (mem_orIn_reach p.1 hp0) [1, 0] hrv_leaf_u,
            hrv_orStep (mem_orIn_reach p.2 hp1) [0, 1] hrv_leaf_v⟩
        · right
          rw [side_def, h0eq] at hp0
          rw [side_def, h1eq] at hp1
          exact ⟨hrv_orStep (mem_orIn_reach p.1 hp0) [0, 1] hrv_leaf_v,
            hrv_orStep (mem_orIn_reach p.2 hp1) [1, 0] hrv_leaf_u⟩
      have hi0lt : i0 < n + t := hLeast.1.2.1 t htlen i0 (by rw [hi01]; exact List.mem_cons_self)
      have hi1lt : i1 < n + t := hLeast.1.2.1 t htlen i1 (by rw [hi01]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [hrv_eq]
      have hat := hrv_at C.gates rvInit t htlen
      rw [hlenInit] at hat
      rw [hat]
      dsimp only
      have hgk : C.gates[t] = gateAt C t := (gateAt_eq htlen).symm
      rw [hgk, if_neg hneOr, if_pos htop, hi01]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [hrv_take_getD t i0 htlen hi0lt, hrv_take_getD t i1 htlen hi1lt]
      have h00 : [0, 0] ∈ [S.map fun _ => 0] := List.mem_cons_self
      rcases hpairMem with ⟨hL, hR⟩ | ⟨hL, hR⟩
      · have hs1 : [1, 0] ∈ andStep 1 [S.map fun _ => 0] ((readVectors C n S 1).getD i0 []) := by
          have hc := handStep_mem [S.map fun _ => 0] ((readVectors C n S 1).getD i0 []) [0, 0] [1, 0] h00 hL
          exact hc
        exact handStep_mem _ _ [1, 0] [0, 1] hs1 hR
      · have hs1 : [0, 1] ∈ andStep 1 [S.map fun _ => 0] ((readVectors C n S 1).getD i0 []) := by
          have hc := handStep_mem [S.map fun _ => 0] ((readVectors C n S 1).getD i0 []) [0, 0] [0, 1] h00 hL
          exact hc
        exact handStep_mem _ _ [0, 1] [1, 0] hs1 hR
    have hout11 : [1, 1] ∈ (readVectors C n S 1).getD C.output [] :=
      hrv_orStep (top_orReaches_output ht) [1, 1] htop11
    have htrue : readsAtMost C n S 1 = true := by
      change ((readVectors C n S 1).getD C.output []).any (fun v => v.all fun a => decide (a ≤ 1)) = true
      exact List.any_eq_true.mpr ⟨[1, 1], hout11, rfl⟩
    exact Bool.noConfusion (htrue.symm.trans hnr)
  have he1U : s(a1, b1) ∈ Ustar G C := readsAtMost_false_mem_Ustar a1 b1 hadj1 hnr1
  have he2U : s(a2, b2) ∈ Ustar G C := readsAtMost_false_mem_Ustar a2 b2 hadj2 hnr2
  have hUstarGe2 : 2 ≤ (Ustar G C).card := by
    have hsub : ({s(a1, b1), s(a2, b2)} : Finset (Sym2 (Fin n))) ⊆ Ustar G C := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he2
      · exact he1U
      · rw [Finset.mem_singleton.mp he2]; exact he2U
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne12] at hc
    exact hc
  have hjwMem : jw ∈ junk G C := by
    refine (junk_mem C jw).mpr ⟨hjwLt, hjwOp, ?_⟩
    by_contra hnone
    apply hjwDirty
    intro x hx
    by_contra hf
    exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  have hJunkNe1 : (junk G C).card ≠ 1 := hNoOneJunk n G C col hbip h4 hLeast
  have hJunkGe2 : 2 ≤ (junk G C).card := by
    have hpos : 0 < (junk G C).card := Finset.card_pos.mpr ⟨jw, hjwMem⟩
    omega
  have junkNotBelow : ∀ {j : ℕ}, j ∈ junk G C → ¬ BelowF G C j := by
    intro j hj h
    obtain ⟨_, _, x, hx, hf⟩ := junkData hj
    exact Bool.false_ne_true (hf.symm.trans (h x hx))
  have emptySide : ∀ {a : ℕ}, a ∈ tops G C → ∀ {b : Fin 2}, side (n := n) C a b = ∅ → a ∈ centreless G C := by
    intro a ha b hs
    refine (centreless_mem C a).mpr ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl hs
    · exact Or.inr hs
  have classifyReader : ∀ {j k : ℕ}, ¬ BelowF G C j → orIn n C (n + j) = ∅ →
      k ∈ readers n C j → k ∈ junk G C ∨ k ∈ centreless G C ∨ k ∈ orN G C \ lam G C := by
    intro j k hd hz hr
    obtain ⟨hk, hin⟩ := readData hr
    obtain ⟨b, hb⟩ := inputsAsOpnd hk hin
    have hs : side (n := n) C k b = ∅ := by rw [side_def, ← hb]; exact hz
    rcases hLeast.1.1 _ (gateAt_mem hk) with hand | hor
    · by_cases hbelow : BelowF G C k
      · right; left
        exact emptySide ((tops_mem C k).mpr ⟨hk, hand, hbelow⟩) hs
      · left
        have hw : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
          by_contra hnone
          apply hbelow
          intro x hx
          by_contra hf
          exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
        exact (junk_mem C k).mpr ⟨hk, hand, hw⟩
    · right; right
      have hnb : ¬ BelowF G C k := by
        intro hbelow
        apply hd
        intro x hx
        exact hbelow x ((val_or (by simp) hk hor).mpr ⟨_, hin, hLeast.1.2.1 k hk _ hin, hx⟩)
      refine Finset.mem_sdiff.mpr ⟨(orN_mem C k).mpr ⟨hk, hor, hnb⟩, ?_⟩
      intro hlam
      obtain ⟨_, h0, h1, _⟩ := (lam_mem C k).mp hlam
      have hn : (orIn n C (opnd C k b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, hz] at hn
      exact Finset.not_nonempty_empty hn
  have orEmpty : ∀ {r : ℕ}, (∀ w ∈ (gateAt C r).inputs, orIn n C w = ∅) → orIn n C (n + r) = ∅ := by
    intro r h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w, hw, tail⟩
    · have := u.isLt; omega
    · obtain ⟨k, _, he, _, hi, _⟩ := hw
      have e : k = r := by omega
      subst k
      have hu' := reach_mem_orIn u tail
      rw [h w hi] at hu'
      exact Finset.notMem_empty _ hu'
  have val_allTrue : ∀ w, w < n + C.gates.length → val C (List.ofFn (fun _ : Fin n => true)) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwn : w < n
      · rw [val_input (by simp) hwn]
        simp [List.getD_eq_getElem?_getD, hwn]
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rcases hLeast.1.1 _ (gateAt_mem hj) with hand | hor
        · exact (val_and (by simp) hj hand).mpr (fun i hi => by
            have hilt := hLeast.1.2.1 j hj i hi
            exact ⟨hilt, ih i hilt (by omega)⟩)
        · have hi0 := opndMem hj 0
          have hlt0 := opndBound hj 0
          exact (val_or (by simp) hj hor).mpr ⟨opnd C j 0, hi0, hlt0, ih _ hlt0 (by omega)⟩
  have not_belowF_inCone_and : ∀ {k j : ℕ}, k < C.gates.length → BelowF G C k →
      j < C.gates.length → (gateAt C j).op = GateOp.and → ¬ InCone n C k j := by
    intro k j hk hbk hj hjo hkj
    have htk := val_allTrue (n + k) (by omega)
    obtain ⟨w', hstep, _, hw'⟩ := or_trace (by simp) (n + k) htk
    rcases hw' with hlt | ⟨t, htlen, rfl, htop⟩
    · have hvar := reach_var_val (pairInput ⟨w', hlt⟩ ⟨w', hlt⟩) (n + k) ⟨w', hlt⟩ hstep (pairInput_left _ _)
      exact G.irrefl ((graphFun_pair _ _).mp (hbk _ hvar))
    · have htand := (hLeast.1.1 _ (gateAt_mem htlen)).resolve_right htop
      have htb : BelowF G C t := fun x hx => hbk x (orStep_up (by simp) hstep (gateVal_eq_val C t x ▸ hx))
      rcases orStep_cone hstep k t rfl rfl with rfl | htkc
      · exact hTop t htlen j hj htand htb hjo hkj
      · exact hTop t htlen j hj htand htb hjo (inCone_trans htkc hkj)
  have dirty_reaches_and : ∀ {r : ℕ}, r < C.gates.length → ¬ BelowF G C r →
      ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ (r = a ∨ InCone n C r a) := by
    intro r hr hnb
    have hclimb : ∀ (d : ℕ) (k : ℕ), k < C.gates.length → C.gates.length - k ≤ d →
        ¬ BelowF G C k → (r = k ∨ InCone n C r k) →
        ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ (r = a ∨ InCone n C r a) := by
      intro d
      induction d with
      | zero => intro k hk hle _ _; omega
      | succ d ih =>
        intro k hk hle hknb hrk
        rcases hLeast.1.1 _ (gateAt_mem hk) with hand | hor
        · exact ⟨k, hk, hand, hrk⟩
        · obtain ⟨q, hq⟩ := leastRead hk hknb
          have hqlen := (readData hq).1
          have hqin := (readData hq).2
          have hkq : k < q := readLt hq
          have hrq : InCone n C r q := by
            rcases hrk with rfl | hrkc
            · exact (inCone_iff r q).mpr ⟨hqlen, r, hkq, hqin, Or.inl rfl⟩
            · exact (inCone_iff r q).mpr ⟨hqlen, k, hkq, hqin, Or.inr hrkc⟩
          rcases hLeast.1.1 _ (gateAt_mem hqlen) with hqand | hqor
          · exact ⟨q, hqlen, hqand, Or.inr hrq⟩
          · have hqnb : ¬ BelowF G C q := by
              intro hqb
              apply hknb
              intro x hx
              exact hqb x ((val_or (by simp) hqlen hqor).mpr ⟨n + k, hqin, by omega, hx⟩)
            exact ih q hqlen (by omega) hqnb (Or.inr hrq)
    exact hclimb C.gates.length r hr (by omega) hnb (Or.inl rfl)
  have not_belowF_inCone_dirty : ∀ {k r : ℕ}, k < C.gates.length → BelowF G C k →
      r < C.gates.length → ¬ BelowF G C r → ¬ InCone n C k r := by
    intro k r hk hbk hr hnb hkr
    obtain ⟨a, ha, haop, rfl | hra⟩ := dirty_reaches_and hr hnb
    · exact not_belowF_inCone_and hk hbk ha haop hkr
    · exact not_belowF_inCone_and hk hbk ha haop (inCone_trans hkr hra)
  have lam_monochrome : ∀ {h : ℕ}, h ∈ lam G C →
      ∃ (t : ℕ) (d : Fin 2) (z : Fin n), t ∈ tops G C ∧ side (n := n) C t (1 - d) = {z} ∧
        OrReaches n C (opnd C t d) h ∧
        ∀ v ∈ orIn n C (n + h), v ∈ side (n := n) C t d ∧ G.Adj z v ∧ col v = !(col z) := by
    intro h hh
    obtain ⟨_, _, _, t, ht, d, hcard, hreach⟩ := (lam_mem C h).mp hh
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    refine ⟨t, d, z, ht, hz, hreach, ?_⟩
    intro v hv
    have hvs : v ∈ side (n := n) C t d := by
      rw [side_def]
      exact orIn_mono hreach hv
    have hzs : z ∈ side (n := n) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self z
    have hadjv : G.Adj z v := by
      fin_cases d
      · exact (topAdj ht hvs hzs).symm
      · exact topAdj ht hzs hvs
    have hcolv : col v = !(col z) := by
      have hne := hbip z v hadjv
      cases hcz : col z <;> cases hcv : col v <;> rw [hcz, hcv] at hne <;>
        first | rfl | exact False.elim (hne rfl)
    exact ⟨hvs, hadjv, hcolv⟩
  have or_nonempty_of_lam : ∀ {h : ℕ}, h ∈ lam G C → (orIn n C (n + h)).Nonempty := by
    intro h hh
    obtain ⟨hN, h0, _, _⟩ := (lam_mem C h).mp hh
    obtain ⟨hlen, hop, _⟩ := (orN_mem C h).mp hN
    obtain ⟨v, hv⟩ := h0
    have hstep : OrStep (n + h) (opnd C h 0) := ⟨h, hlen, rfl, hop, opndMem hlen 0, opndBound hlen 0⟩
    exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head hstep (mem_orIn_reach v hv))⟩
  have no_bothNonempty_R_below_lam : ∀ {m0 h : ℕ}, m0 ∈ orN G C \ lam G C → h ∈ lam G C →
      (orIn n C (opnd C m0 0)).Nonempty → (orIn n C (opnd C m0 1)).Nonempty →
      ¬ OrReaches n C (n + h) m0 := by
    intro m0 h hm0 hh h0 h1 hreach
    obtain ⟨_, _, _, t, ht, d, hcard, hth⟩ := (lam_mem C h).mp hh
    have hm0N := (Finset.mem_sdiff.mp hm0).1
    have hm0len := ((orN_mem C m0).mp hm0N).1
    have htm0 : OrReaches n C (opnd C t d) m0 :=
      reach_orReaches ((orReaches_reach h _ hth).1.trans (orReaches_reach m0 _ hreach).1) m0 rfl hm0len
    exact (Finset.mem_sdiff.mp hm0).2 ((lam_mem C m0).mpr ⟨hm0N, h0, h1, t, ht, d, hcard, htm0⟩)
  let MonoSet : Finset (Fin n) → Prop := fun S =>
    ∃ c : Bool, (∀ v ∈ S, col v = c) ∧
      (∀ v1 v2 : Fin n, v1 ≠ v2 → v1 ∈ S → v2 ∈ S →
        ∃ t ∈ tops G C, ∃ d : Fin 2, ∃ z : Fin n,
          side (n := n) C t (1 - d) = {z} ∧ v1 ∈ side (n := n) C t d ∧ v2 ∈ side (n := n) C t d ∧
          G.Adj z v1 ∧ G.Adj z v2)
  let setsEval : Finset (Finset (Fin n)) → (Fin n → Bool) → Prop := fun Fs x =>
    ∀ S ∈ Fs, ∃ v ∈ S, x v = true
  have monoSet_singleton : ∀ v0 : Fin n, MonoSet {v0} := by
    intro v0
    refine ⟨col v0, fun v hv => by rw [Finset.mem_singleton.mp hv], ?_⟩
    intro v1 v2 hne h1 h2
    exact False.elim (hne ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm))
  have monoSet_lam : ∀ {h : ℕ}, h ∈ lam G C → MonoSet (orIn n C (n + h)) := by
    intro h hh
    obtain ⟨t, d, z, ht, hz, _, hprop⟩ := lam_monochrome hh
    refine ⟨!(col z), fun v hv => (hprop v hv).2.2, ?_⟩
    intro v1 v2 _ hv1 hv2
    exact ⟨t, ht, d, z, hz, (hprop v1 hv1).1, (hprop v2 hv2).1, (hprop v1 hv1).2.1, (hprop v2 hv2).2.1⟩
  have setsEval_empty : ∀ x : Fin n → Bool, setsEval ∅ x := fun _ _ h => False.elim (Finset.notMem_empty _ h)
  have setsEval_union : ∀ (A B : Finset (Finset (Fin n))) (x : Fin n → Bool),
      setsEval (A ∪ B) x ↔ setsEval A x ∧ setsEval B x := by
    intro A B x
    constructor
    · intro h
      exact ⟨fun S hS => h S (Finset.mem_union_left B hS), fun S hS => h S (Finset.mem_union_right A hS)⟩
    · rintro ⟨hA, hB⟩ S hS
      rcases Finset.mem_union.mp hS with h1 | h2
      · exact hA S h1
      · exact hB S h2
  have setsEval_mono_sub : ∀ {A B : Finset (Finset (Fin n))} {x : Fin n → Bool},
      A ⊆ B → setsEval B x → setsEval A x := fun hsub h S hS => h S (hsub hS)
  have setsEval_rect : ∀ (Fs : Finset (Finset (Fin n))), (∀ S ∈ Fs, MonoSet S) →
      ∀ (c0 : Bool) (u1 u2 v1 v2 : Fin n),
        col u1 = c0 → col u2 = c0 → col v1 = !c0 → col v2 = !c0 →
        setsEval Fs (pairInput u1 v1) → setsEval Fs (pairInput u2 v2) →
        setsEval Fs (pairInput u1 v2) ∧ setsEval Fs (pairInput u2 v1) := by
    intro Fs hFs c0 u1 u2 v1 v2 hu1 hu2 hv1 hv2 h1 h2
    have stepS : ∀ S ∈ Fs,
        (∃ x ∈ S, pairInput u1 v2 x = true) ∧ (∃ x ∈ S, pairInput u2 v1 x = true) := by
      intro S hS
      obtain ⟨cS, hcolS, _⟩ := hFs S hS
      obtain ⟨x1, hx1m, hx1p⟩ := h1 S hS
      obtain ⟨x2, hx2m, hx2p⟩ := h2 S hS
      have hc1 : col x1 = cS := hcolS x1 hx1m
      have hc2 : col x2 = cS := hcolS x2 hx2m
      rcases (pairInput_true u1 v1 x1).mp hx1p with rfl | rfl <;>
        rcases (pairInput_true u2 v2 x2).mp hx2p with rfl | rfl
      · exact ⟨⟨x1, hx1m, pairInput_left _ _⟩, ⟨x2, hx2m, pairInput_left _ _⟩⟩
      · have hcontra : c0 = !c0 := hu1.symm.trans (hc1.trans (hc2.symm.trans hv2))
        cases c0 <;> exact Bool.noConfusion hcontra
      · have hcontra : (!c0) = c0 := hv1.symm.trans (hc1.trans (hc2.symm.trans hu2))
        cases c0 <;> exact Bool.noConfusion hcontra
      · exact ⟨⟨x2, hx2m, pairInput_right _ _⟩, ⟨x1, hx1m, pairInput_right _ _⟩⟩
    exact ⟨fun S hS => (stepS S hS).1, fun S hS => (stepS S hS).2⟩
  have setsEval_same_v : ∀ (Fs : Finset (Finset (Fin n))), (∀ S ∈ Fs, MonoSet S) →
      ∀ (c0 : Bool) (u1 u2 v1 : Fin n),
        u1 ≠ u2 → col u1 = c0 → col u2 = c0 → col v1 = !c0 →
        G.Adj u1 v1 → G.Adj u2 v1 → s(u1, v1) ∈ Ustar G C →
        setsEval Fs (pairInput u1 v1) → setsEval Fs (pairInput u2 v1) →
        setsEval Fs (pairInput v1 v1) := by
    intro Fs hFs c0 u1 u2 v1 hne hu1 hu2 hv1 hadj1' hadj2' hu1U h1 h2 S hS
    obtain ⟨cS, hcolS, htwo⟩ := hFs S hS
    obtain ⟨x1, hx1m, hx1p⟩ := h1 S hS
    obtain ⟨x2, hx2m, hx2p⟩ := h2 S hS
    rcases (pairInput_true u1 v1 x1).mp hx1p with rfl | rfl
    · rcases (pairInput_true u2 v1 x2).mp hx2p with rfl | rfl
      · obtain ⟨t, ht, d, z, hz, hx1s, hx2s, hz1, hz2⟩ := htwo x1 x2 hne hx1m hx2m
        have hzv : z = v1 := by
          by_contra hzn
          have hcard := h4 z v1 hzn
          have h1m : x1 ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj v1 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1, hadj1'.symm⟩
          have h2m : x2 ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj v1 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2, hadj2'.symm⟩
          exact hne (Finset.card_le_one.mp hcard x1 h1m x2 h2m)
        subst z
        have hvs : v1 ∈ side (n := n) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self v1
        have hstar : s(x1, v1) ∈ starEdges G C := by
          rw [starEdges_def]
          refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
          fin_cases d
          · exact Finset.mem_image.mpr ⟨(x1, v1), Finset.mem_product.mpr ⟨hx1s, hvs⟩, rfl⟩
          · exact Finset.mem_image.mpr ⟨(v1, x1), Finset.mem_product.mpr ⟨hvs, hx1s⟩, Sym2.eq_swap⟩
        rw [Ustar_def] at hu1U
        exact False.elim ((Finset.mem_sdiff.mp hu1U).2 hstar)
      · have hcontra : c0 = !c0 := hu1.symm.trans ((hcolS x1 hx1m).trans ((hcolS x2 hx2m).symm.trans hv1))
        cases c0 <;> exact Bool.noConfusion hcontra
    · exact ⟨x1, hx1m, pairInput_left _ _⟩
  have orient_edge : ∀ (c0 : Bool) {e : Sym2 (Fin n)}, e ∈ Ustar G C →
      ∃ u v : Fin n, e = s(u, v) ∧ col u = c0 ∧ col v = !c0 ∧ G.Adj u v := by
    intro c0 e he
    induction e using Sym2.ind with
    | _ p q =>
      have hadjpq : G.Adj p q := by
        rw [Ustar_def] at he
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      have hcolne := hbip p q hadjpq
      have bool_ne_not : ∀ a b : Bool, a ≠ b → b = !a := by
        intro a b h; cases a <;> cases b <;> first | rfl | exact False.elim (h rfl)
      by_cases hcp : col p = c0
      · exact ⟨p, q, rfl, hcp, bool_ne_not c0 (col q) (hcp ▸ hcolne), hadjpq⟩
      · have hcp' : col p = !c0 := bool_ne_not c0 (col p) (fun h => hcp h.symm)
        have hcq' : col q = !(col p) := bool_ne_not (col p) (col q) hcolne
        refine ⟨q, p, Sym2.eq_swap, ?_, hcp', hadjpq.symm⟩
        rw [hcq', hcp', Bool.not_not]
  have conj_at_most_one_centreless : ∀ (Fs : Finset (Finset (Fin n))),
      (∀ S ∈ Fs, MonoSet S) →
      (∀ x : Fin n → Bool, setsEval Fs x → graphFun G ∅ x = true) →
      ∀ e1 ∈ Ustar G C, ∀ e2 ∈ Ustar G C,
        (∀ u v : Fin n, e1 = s(u, v) → setsEval Fs (pairInput u v)) →
        (∀ u v : Fin n, e2 = s(u, v) → setsEval Fs (pairInput u v)) →
        e1 = e2 := by
    intro Fs hFs hBelow e1 he1 e2 he2 hf1 hf2
    by_contra hne
    obtain ⟨u1, v1, rfl, hu1c, hv1c, hadj1'⟩ := orient_edge false he1
    obtain ⟨u2, v2, rfl, hu2c, hv2c, hadj2'⟩ := orient_edge false he2
    have h1 := hf1 u1 v1 rfl
    have h2 := hf2 u2 v2 rfl
    by_cases hu : u1 = u2
    · subst u2
      have hvne : v1 ≠ v2 := fun h => hne (by rw [h])
      have h1' : setsEval Fs (pairInput v1 u1) := by
        intro S hS
        obtain ⟨x, hxS, hxp⟩ := h1 S hS
        exact ⟨x, hxS, (pairInput_true v1 u1 x).mpr ((pairInput_true u1 v1 x).mp hxp).symm⟩
      have h2' : setsEval Fs (pairInput v2 u1) := by
        intro S hS
        obtain ⟨x, hxS, hxp⟩ := h2 S hS
        exact ⟨x, hxS, (pairInput_true v2 u1 x).mpr ((pairInput_true u1 v2 x).mp hxp).symm⟩
      have hsame := setsEval_same_v Fs hFs true v1 v2 u1 hvne hv1c hv2c (by rw [hu1c]; rfl)
        hadj1'.symm hadj2'.symm (by rw [Sym2.eq_swap]; exact he1) h1' h2'
      exact G.irrefl ((graphFun_pair u1 u1).mp (hBelow _ hsame))
    · by_cases hv : v1 = v2
      · subst v2
        have hsame := setsEval_same_v Fs hFs false u1 u2 v1 hu hu1c hu2c hv1c hadj1' hadj2' he1 h1 h2
        exact G.irrefl ((graphFun_pair v1 v1).mp (hBelow _ hsame))
      · obtain ⟨h12, h21⟩ := setsEval_rect Fs hFs false u1 u2 v1 v2 hu1c hu2c hv1c hv2c h1 h2
        have hadj12 : G.Adj u1 v2 := (graphFun_pair u1 v2).mp (hBelow _ h12)
        have hadj21 : G.Adj u2 v1 := (graphFun_pair u2 v1).mp (hBelow _ h21)
        have hcard := h4 u1 u2 hu
        have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1', hadj21⟩
        have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj12, hadj2'⟩
        exact hv (Finset.card_le_one.mp hcard v1 hm1 v2 hm2)
  have conj_at_most_one_via_z0 : ∀ (z0 : Fin n) (Fs : Finset (Finset (Fin n))),
      (∀ S ∈ Fs, MonoSet S) →
      ∀ e1 ∈ Ustar G C, ∀ e2 ∈ Ustar G C,
        (∀ u v : Fin n, col u = col z0 → col v = !(col z0) → e1 = s(u, v) →
          G.Adj z0 v ∧ u ≠ z0 ∧ setsEval Fs (pairInput u v) ∧
            ∀ w : Fin n, setsEval Fs (pairInput w v) → G.Adj w v) →
        (∀ u v : Fin n, col u = col z0 → col v = !(col z0) → e2 = s(u, v) →
          G.Adj z0 v ∧ u ≠ z0 ∧ setsEval Fs (pairInput u v) ∧
            ∀ w : Fin n, setsEval Fs (pairInput w v) → G.Adj w v) →
        e1 = e2 := by
    intro z0 Fs hFs e1 he1 e2 he2 hp1 hp2
    by_contra hne
    obtain ⟨u1, v1, rfl, hu1c, hv1c, hadj1'⟩ := orient_edge (col z0) he1
    obtain ⟨u2, v2, rfl, hu2c, hv2c, hadj2'⟩ := orient_edge (col z0) he2
    obtain ⟨hz1, hu1z, h1, hfire1⟩ := hp1 u1 v1 hu1c hv1c rfl
    obtain ⟨hz2, _, h2, hfire2⟩ := hp2 u2 v2 hu2c hv2c rfl
    by_cases hu : u1 = u2
    · subst u2
      have hvne : v1 ≠ v2 := fun h => hne (by rw [h])
      have hcard := h4 u1 z0 hu1z
      have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1', hz1⟩
      have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj2', hz2⟩
      exact hvne (Finset.card_le_one.mp hcard v1 hm1 v2 hm2)
    · by_cases hv : v1 = v2
      · subst v2
        have hsame := setsEval_same_v Fs hFs (col z0) u1 u2 v1 hu hu1c hu2c hv1c hadj1' hadj2' he1 h1 h2
        exact G.irrefl (hfire1 v1 hsame)
      · obtain ⟨h12, h21⟩ := setsEval_rect Fs hFs (col z0) u1 u2 v1 v2 hu1c hu2c hv1c hv2c h1 h2
        have hadj21 : G.Adj u2 v1 := hfire1 u2 h21
        have hadj12 : G.Adj u1 v2 := hfire2 u1 h12
        have hcard := h4 u1 u2 hu
        have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1', hadj21⟩
        have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj12, hadj2'⟩
        exact hv (Finset.card_le_one.mp hcard v1 hm1 v2 hm2)
  have pure_junk_at_most_one_Ustar : ∀ (j : ℕ) (Fs : Finset (Finset (Fin n))),
      j ∈ junk G C → (∀ S ∈ Fs, MonoSet S) →
      (∀ x : Fin n → Bool, gateVal n C j x = true ↔ setsEval Fs x) →
      ∀ (u1 v1 : Fin n), s(u1, v1) ∈ Ustar G C →
        (∀ w : Fin n, gateVal n C j (pairInput w v1) = true → G.Adj w v1) →
        gateVal n C j (pairInput u1 v1) = true →
        ∀ (u2 v2 : Fin n), s(u2, v2) ∈ Ustar G C → s(u1, v1) ≠ s(u2, v2) →
          gateVal n C j (pairInput u2 v2) = true → False := by
    intro j Fs hj hFs hjEq u1 v1 he1 hfire1 hj1 u2 v2 he2 hne12' hj2
    have hadj1' : G.Adj u1 v1 := by
      rw [Ustar_def] at he1
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he1).1
    have hadj2' : G.Adj u2 v2 := by
      rw [Ustar_def] at he2
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he2).1
    obtain ⟨c0, hc0⟩ : ∃ c0 : Bool, col u1 = c0 := ⟨col u1, rfl⟩
    have hv1c : col v1 = !c0 := by
      have hne := hbip u1 v1 hadj1'
      cases hcu : col u1 <;> cases hcv : col v1 <;> rw [hcu, hcv] at hne <;>
        rw [← hc0, hcu] <;> first | rfl | exact False.elim (hne rfl)
    obtain ⟨u2', v2', h2eq, hu2'c, hv2'c, hadj2''⟩ := orient_edge c0 he2
    have hj2' : gateVal n C j (pairInput u2' v2') = true := by
      rcases Sym2.eq_iff.mp h2eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hj2
      · have hpe : pairInput v2 u2 = pairInput u2 v2 := by
          exact pairInput_symm _ _
        rw [hpe]; exact hj2
    have h1 : setsEval Fs (pairInput u1 v1) := (hjEq _).mp hj1
    have h2 : setsEval Fs (pairInput u2' v2') := (hjEq _).mp hj2'
    by_cases hu : u1 = u2'
    · rcases hu with rfl
      have hvne : v1 ≠ v2' := fun h => hne12' (by rw [h, ← h2eq])
      have hnoOtherCol : ∀ S ∈ Fs, ∀ cS : Bool, (∀ v ∈ S, col v = cS) → cS = c0 := by
        intro S hS cS hcolS
        by_contra hneC
        have hcS : cS = !c0 := by cases c0 <;> cases cS <;> first | rfl | exact False.elim (hneC rfl)
        obtain ⟨x1, hx1m, hx1p⟩ := h1 S hS
        obtain ⟨x2, hx2m, hx2p⟩ := h2 S hS
        have hx1eq : x1 = v1 := by
          rcases (pairInput_true u1 v1 x1).mp hx1p with hx1 | hx1
          · rw [hx1] at hx1m
            have hcon : c0 = !c0 := hc0.symm.trans ((hcolS u1 hx1m).trans hcS)
            cases c0 <;> exact Bool.noConfusion hcon
          · exact hx1
        have hx2eq : x2 = v2' := by
          rcases (pairInput_true u1 v2' x2).mp hx2p with hx2 | hx2
          · rw [hx2] at hx2m
            have hcon : c0 = !c0 := hc0.symm.trans ((hcolS u1 hx2m).trans hcS)
            cases c0 <;> exact Bool.noConfusion hcon
          · exact hx2
        rw [hx1eq] at hx1m
        rw [hx2eq] at hx2m
        obtain ⟨_, _, htwo⟩ := hFs S hS
        obtain ⟨t, ht, d, z, hz, hv1s, hv2s, hz1, hz2⟩ := htwo v1 v2' hvne hx1m hx2m
        have hzu : z = u1 := by
          by_contra hzn
          have hcard := h4 z u1 hzn
          have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj u1 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1, hadj1'⟩
          have hm2 : v2' ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj u1 p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2, hadj2''⟩
          exact hvne (Finset.card_le_one.mp hcard v1 hm1 v2' hm2)
        subst z
        have hus : u1 ∈ side (n := n) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self u1
        have hstar : s(u1, v1) ∈ starEdges G C := by
          rw [starEdges_def]
          refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
          fin_cases d
          · exact Finset.mem_image.mpr ⟨(v1, u1), Finset.mem_product.mpr ⟨hv1s, hus⟩, Sym2.eq_swap⟩
          · exact Finset.mem_image.mpr ⟨(u1, v1), Finset.mem_product.mpr ⟨hus, hv1s⟩, rfl⟩
        rw [Ustar_def] at he1
        exact (Finset.mem_sdiff.mp he1).2 hstar
      have hu1InAll : ∀ S ∈ Fs, u1 ∈ S := by
        intro S hS
        obtain ⟨cS, hcolS, _⟩ := hFs S hS
        have hcS := hnoOtherCol S hS cS hcolS
        obtain ⟨x1, hx1m, hx1p⟩ := h1 S hS
        rcases (pairInput_true u1 v1 x1).mp hx1p with hx1 | hx1
        · rwa [hx1] at hx1m
        · rw [hx1] at hx1m
          have hcon : (!c0) = c0 := hv1c.symm.trans ((hcolS v1 hx1m).trans hcS)
          cases c0 <;> exact Bool.noConfusion hcon
      have hFsNe : Fs.Nonempty := by
        by_contra hEmp
        rw [Finset.not_nonempty_iff_eq_empty] at hEmp
        have hjv1 : gateVal n C j (pairInput v1 v1) = true := (hjEq _).mpr (by rw [hEmp]; exact setsEval_empty _)
        exact G.irrefl (hfire1 v1 hjv1)
      apply replace_gate_by_input j u1 (junkData hj).1 (junkNotBelow hj)
      · intro x hxu1
        exact (hjEq x).mpr (fun S hS => ⟨u1, hu1InAll S hS, hxu1⟩)
      · intro p q hpq hjpq
        obtain ⟨p', q', hpqeq, hp'c, hq'c, _⟩ : ∃ p' q' : Fin n, s(p, q) = s(p', q') ∧ col p' = c0 ∧ col q' = !c0 ∧ G.Adj p' q' := by
          have hne := hbip p q hpq
          by_cases hcp : col p = c0
          · refine ⟨p, q, rfl, hcp, ?_, hpq⟩
            cases h1' : col p <;> cases h2' : col q <;> rw [h1', h2'] at hne <;>
              rw [← hcp, h1'] <;> first | rfl | exact False.elim (hne rfl)
          · have hcq : col q = c0 := by
              cases h1' : col p <;> cases h2' : col q <;> rw [h1', h2'] at hne <;>
                cases h3' : c0 <;> rw [h1', h3'] at hcp <;>
                first | rfl | exact False.elim (hne rfl) | exact False.elim (hcp rfl)
            refine ⟨q, p, Sym2.eq_swap, hcq, ?_, hpq.symm⟩
            cases h1' : col p <;> cases h2' : col q <;> rw [h1', h2'] at hne <;>
              rw [← hcq, h2'] <;> first | rfl | exact False.elim (hne rfl)
        have hjpq' : setsEval Fs (pairInput p' q') := by
          have hpe : pairInput p' q' = pairInput p q := by
            rcases Sym2.eq_iff.mp hpqeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact pairInput_symm _ _
          rw [hpe]
          exact (hjEq _).mp hjpq
        have hp'InAll : ∀ S ∈ Fs, p' ∈ S := by
          intro S hS
          obtain ⟨cS, hcolS, _⟩ := hFs S hS
          have hcS := hnoOtherCol S hS cS hcolS
          obtain ⟨x, hxS, hxp⟩ := hjpq' S hS
          rcases (pairInput_true p' q' x).mp hxp with hx | hx
          · rwa [hx] at hxS
          · rw [hx] at hxS
            have hcon : (!c0) = c0 := hq'c.symm.trans ((hcolS q' hxS).trans hcS)
            cases c0 <;> exact Bool.noConfusion hcon
        have hp'eq : p' = u1 := by
          by_contra hp'ne
          have hjp'v1 : gateVal n C j (pairInput p' v1) = true :=
            (hjEq _).mpr (fun S hS => ⟨p', hp'InAll S hS, pairInput_left p' v1⟩)
          have hadjp'v1 : G.Adj p' v1 := hfire1 p' hjp'v1
          obtain ⟨S0, hS0⟩ := hFsNe
          obtain ⟨_, _, htwo⟩ := hFs S0 hS0
          obtain ⟨t, ht, d, z, hz, hu1s, hp's, hz1, hz2⟩ := htwo u1 p' (Ne.symm hp'ne) (hu1InAll S0 hS0) (hp'InAll S0 hS0)
          have hzv : z = v1 := by
            by_contra hzn
            have hcard := h4 z v1 hzn
            have hm1 : u1 ∈ Finset.univ.filter (fun w => G.Adj z w ∧ G.Adj v1 w) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1, hadj1'.symm⟩
            have hm2 : p' ∈ Finset.univ.filter (fun w => G.Adj z w ∧ G.Adj v1 w) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2, hadjp'v1.symm⟩
            exact Ne.symm hp'ne (Finset.card_le_one.mp hcard u1 hm1 p' hm2)
          subst z
          have hvs : v1 ∈ side (n := n) C t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self v1
          have hstar : s(u1, v1) ∈ starEdges G C := by
            rw [starEdges_def]
            refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
            fin_cases d
            · exact Finset.mem_image.mpr ⟨(u1, v1), Finset.mem_product.mpr ⟨hu1s, hvs⟩, rfl⟩
            · exact Finset.mem_image.mpr ⟨(v1, u1), Finset.mem_product.mpr ⟨hvs, hu1s⟩, Sym2.eq_swap⟩
          rw [Ustar_def] at he1
          exact (Finset.mem_sdiff.mp he1).2 hstar
        subst p'
        rcases Sym2.eq_iff.mp hpqeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact pairInput_left _ _
        · exact pairInput_right _ _
    · have hadj21 : G.Adj u2' v1 := by
        by_cases hv : v1 = v2'
        · rw [hv]; exact hadj2''
        · obtain ⟨_, h21⟩ := setsEval_rect Fs hFs c0 u1 u2' v1 v2' hc0 hu2'c hv1c hv2'c h1 h2
          exact hfire1 u2' ((hjEq _).mpr h21)
      have h2v1 : setsEval Fs (pairInput u2' v1) := by
        by_cases hv : v1 = v2'
        · rw [hv]; exact h2
        · exact (setsEval_rect Fs hFs c0 u1 u2' v1 v2' hc0 hu2'c hv1c hv2'c h1 h2).2
      have hsame := setsEval_same_v Fs hFs c0 u1 u2' v1 hu hc0 hu2'c hv1c hadj1' hadj21 he1 h1 h2v1
      exact G.irrefl (hfire1 v1 ((hjEq _).mpr hsame))
  have pure_no_R_eval : ∀ (L : ℕ), (∀ r ∈ orN G C \ lam G C, ¬ r < L) →
      ∀ w : ℕ, w < n + L →
        (w < n ∨ ∃ g, w = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g) →
        ∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
          ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ setsEval Fs x := by
    intro L hNoR w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt hkind
      rcases hkind with hwn | ⟨g, rfl, hglen, hgnb⟩
      · refine ⟨{({⟨w, hwn⟩} : Finset (Fin n))}, ?_, ?_⟩
        · intro S hS
          rw [Finset.mem_singleton.mp hS]
          exact monoSet_singleton ⟨w, hwn⟩
        · intro x
          rw [val_input List.length_ofFn hwn]
          have hget : (List.ofFn x).getD w false = x ⟨w, hwn⟩ := by
            simp [List.getD_eq_getElem?_getD, hwn]
          rw [hget]
          constructor
          · intro hx S hS
            rw [Finset.mem_singleton.mp hS]
            exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _, hx⟩
          · intro h
            obtain ⟨v, hv, hxv⟩ := h _ (Finset.mem_singleton_self _)
            rw [Finset.mem_singleton.mp hv] at hxv
            exact hxv
      · have hglt : g < L := by omega
        rcases hLeast.1.1 _ (gateAt_mem hglen) with hand | hor
        · have hsub : ∀ b : Fin 2, ∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔ setsEval Fs x := by
            intro b
            have hblt := opndBound hglen b
            refine ih (opnd C g b) hblt (by omega) ?_
            by_cases hbn : opnd C g b < n
            · exact Or.inl hbn
            · right
              refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
              intro hbelow
              have hcone : InCone n C (opnd C g b - n) g :=
                (inCone_iff _ g).mpr ⟨hglen, opnd C g b - n, by omega, by
                  have he : n + (opnd C g b - n) = opnd C g b := by omega
                  rw [he]; exact opndMem hglen b, Or.inl rfl⟩
              exact not_belowF_inCone_and (by omega) hbelow hglen hand hcone
          obtain ⟨Fs0, hM0, hE0⟩ := hsub 0
          obtain ⟨Fs1, hM1, hE1⟩ := hsub 1
          refine ⟨Fs0 ∪ Fs1, ?_, ?_⟩
          · intro S hS
            rcases Finset.mem_union.mp hS with h0 | h1
            · exact hM0 S h0
            · exact hM1 S h1
          · intro x
            rw [← gateVal_eq_val, andValBoth hglen hand, hE0, hE1, setsEval_union]
        · have hgN : g ∈ orN G C := (orN_mem C g).mpr ⟨hglen, hor, hgnb⟩
          have hgLam : g ∈ lam G C := by
            by_contra hnot
            exact hNoR g (Finset.mem_sdiff.mpr ⟨hgN, hnot⟩) hglt
          have hsub : ∀ b : Fin 2, opnd C g b < n ∨
              ∃ k, opnd C g b = n + k ∧ k < C.gates.length ∧ k ∈ lam G C := by
            intro b
            by_cases hbn : opnd C g b < n
            · exact Or.inl hbn
            · right
              let k := opnd C g b - n
              have hkeq : opnd C g b = n + k := by omega
              have hklt : k < g := by have := opndBound hglen b; omega
              have hknb : ¬ BelowF G C k := by
                intro hbk
                have hcone : InCone n C k g :=
                  (inCone_iff k g).mpr ⟨hglen, k, hklt, hkeq ▸ opndMem hglen b, Or.inl rfl⟩
                exact not_belowF_inCone_dirty (by omega) hbk hglen hgnb hcone
              have hkop : (gateAt C k).op = GateOp.or := by
                rcases hLeast.1.1 _ (gateAt_mem (j := k) (by omega)) with hkand | hkor
                · have hkj : k ∈ junk G C := by
                    refine (junk_mem C k).mpr ⟨by omega, hkand, ?_⟩
                    by_contra hnone
                    apply hknb
                    intro x hx
                    by_contra hf
                    exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
                  have hgR := lastOrOutside hkj hglen hor (hkeq ▸ opndMem hglen b) (by omega)
                  exact False.elim ((Finset.mem_sdiff.mp hgR).2 hgLam)
                · exact hkor
              have hkN : k ∈ orN G C := (orN_mem C k).mpr ⟨by omega, hkop, hknb⟩
              have hkLam : k ∈ lam G C := by
                by_contra hnot
                exact hNoR k (Finset.mem_sdiff.mpr ⟨hkN, hnot⟩) (by omega)
              exact ⟨k, hkeq, by omega, hkLam⟩
          have hPureOr : ∀ (w' : ℕ), w' < n + L →
              (w' < n ∨ ∃ k, w' = n + k ∧ k < C.gates.length ∧ k ∈ lam G C) →
              ∀ x : Fin n → Bool, val C (List.ofFn x) w' = true ↔ ∃ v ∈ orIn n C w', x v = true := by
            intro w'
            induction w' using Nat.strong_induction_on with
            | ind w' ih' =>
              intro hw'lt hw'kind x
              rcases hw'kind with hw'n | ⟨k, rfl, hklen, hklam⟩
              · rw [val_input List.length_ofFn hw'n]
                have hget : (List.ofFn x).getD w' false = x ⟨w', hw'n⟩ := by
                  simp [List.getD_eq_getElem?_getD, hw'n]
                rw [hget]
                constructor
                · intro hx
                  exact ⟨⟨w', hw'n⟩, reach_mem_orIn ⟨w', hw'n⟩ Relation.ReflTransGen.refl, hx⟩
                · rintro ⟨v, hv, hxv⟩
                  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨_, hstep, _⟩
                  · have : v = ⟨w', hw'n⟩ := Fin.ext he.symm
                    rwa [← this]
                  · obtain ⟨r, _, hr, _, _, _⟩ := hstep; omega
              · have hkN := (lam_mem C k).mp hklam
                have hkop := ((orN_mem C k).mp hkN.1).2.1
                have hknb := ((orN_mem C k).mp hkN.1).2.2
                rw [val_or List.length_ofFn hklen hkop]
                constructor
                · rintro ⟨i, hi, hilt, hvi⟩
                  have hikind : i < n ∨ ∃ r, i = n + r ∧ r < C.gates.length ∧ r ∈ lam G C := by
                    by_cases hin : i < n
                    · exact Or.inl hin
                    · right
                      let r := i - n
                      have hreq : i = n + r := by omega
                      have hrnb : ¬ BelowF G C r := by
                        intro hbr
                        have hcone : InCone n C r k :=
                          (inCone_iff r k).mpr ⟨hklen, r, by omega, hreq ▸ hi, Or.inl rfl⟩
                        exact not_belowF_inCone_dirty (by omega) hbr hklen hknb hcone
                      have hrop : (gateAt C r).op = GateOp.or := by
                        rcases hLeast.1.1 _ (gateAt_mem (j := r) (by omega)) with hrand | hror
                        · have hrj : r ∈ junk G C := by
                            refine (junk_mem C r).mpr ⟨by omega, hrand, ?_⟩
                            by_contra hnone
                            apply hrnb
                            intro y hy
                            by_contra hf
                            exact hnone ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
                          exact False.elim ((Finset.mem_sdiff.mp (lastOrOutside hrj hklen hkop (hreq ▸ hi) (by omega))).2 hklam)
                        · exact hror
                      have hrN : r ∈ orN G C := (orN_mem C r).mpr ⟨by omega, hrop, hrnb⟩
                      have hrLam : r ∈ lam G C := by
                        by_contra hnot
                        exact hNoR r (Finset.mem_sdiff.mpr ⟨hrN, hnot⟩) (by omega)
                      exact ⟨r, hreq, by omega, hrLam⟩
                  obtain ⟨v, hv, hxv⟩ := (ih' i hilt (by omega) hikind x).mp hvi
                  exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ (mem_orIn_reach v hv)), hxv⟩
                · rintro ⟨v, hv, hxv⟩
                  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨i, hstep, hrest⟩
                  · have := v.isLt; omega
                  · obtain ⟨k0, _, hek, _, hi, hilt⟩ := hstep
                    have : k0 = k := by omega
                    subst k0
                    exact ⟨i, hi, hilt, reach_var_val x i v hrest hxv⟩
          refine ⟨{orIn n C (n + g)}, ?_, ?_⟩
          · intro S hS
            rw [Finset.mem_singleton.mp hS]
            exact monoSet_lam hgLam
          · intro x
            rw [hPureOr (n + g) hwlt (Or.inr ⟨g, rfl, hglen, hgLam⟩) x]
            constructor
            · intro h S hS
              rw [Finset.mem_singleton.mp hS]
              exact h
            · intro h
              exact h _ (Finset.mem_singleton_self _)
  have hOneR : 1 ≤ (orN G C \ lam G C).card := by
    by_contra hZeroR
    have hRempty : orN G C \ lam G C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hNoR : ∀ r ∈ orN G C \ lam G C, ¬ r < C.gates.length := fun r hr _ => by
      rw [hRempty] at hr; exact Finset.notMem_empty _ hr
    have hEveryUstarInZ : ∀ e ∈ Ustar G C, ∃ z ∈ centreless G C,
        ∀ u v : Fin n, e = s(u, v) → gateVal n C z (pairInput u v) = true := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, hv, b, j, hj, hr, _⟩ := residualTrace he
        rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨r, hrlen, ho, hi, hb, _⟩
        · have hz : a ∈ centreless G C := emptySide ha (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)
          refine ⟨a, hz, ?_⟩
          intro u' v' heq'
          rcases Sym2.eq_iff.mp heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hv
          · have hpe : pairInput v u = pairInput u v := by
              exact pairInput_symm _ _
            rw [hpe]; exact hv
        · have hrR := lastOrOutside hj hrlen ho hi hb
          rw [hRempty] at hrR
          exact False.elim (Finset.notMem_empty _ hrR)
    have hZeval : ∀ z ∈ centreless G C, ∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
        ∀ x : Fin n → Bool, gateVal n C z x = true ↔ setsEval Fs x := by
      intro z hz
      obtain ⟨hzlen, hzop, _⟩ := topData ((centreless_mem C z).mp hz).1
      have hsub : ∀ b : Fin 2, ∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
          ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C z b) = true ↔ setsEval Fs x := by
        intro b
        have hblt := opndBound hzlen b
        refine pure_no_R_eval C.gates.length hNoR (opnd C z b) (by omega) ?_
        by_cases hbn : opnd C z b < n
        · exact Or.inl hbn
        · right
          refine ⟨opnd C z b - n, by omega, by omega, ?_⟩
          intro hbelow
          have hcone : InCone n C (opnd C z b - n) z :=
            (inCone_iff _ z).mpr ⟨hzlen, opnd C z b - n, by omega, by
              have he : n + (opnd C z b - n) = opnd C z b := by omega
              rw [he]; exact opndMem hzlen b, Or.inl rfl⟩
          exact not_belowF_inCone_and (by omega) hbelow hzlen hzop hcone
      obtain ⟨Fs0, hM0, hE0⟩ := hsub 0
      obtain ⟨Fs1, hM1, hE1⟩ := hsub 1
      refine ⟨Fs0 ∪ Fs1, ?_, ?_⟩
      · intro S hS
        rcases Finset.mem_union.mp hS with h0 | h1
        · exact hM0 S h0
        · exact hM1 S h1
      · intro x
        rw [andValBoth hzlen hzop, hE0, hE1, setsEval_union]
    choose fZ hfZmem hfZval using hEveryUstarInZ
    have hUleZ : (Ustar G C).card ≤ (centreless G C).card := by
      have hInj : Set.InjOn (fun e : Sym2 (Fin n) => if h : e ∈ Ustar G C then fZ e h else 0) ↑(Ustar G C) := by
        intro e1 he1 e2 he2 heq
        have he1' : e1 ∈ Ustar G C := Finset.mem_coe.mp he1
        have he2' : e2 ∈ Ustar G C := Finset.mem_coe.mp he2
        change (if h : e1 ∈ Ustar G C then fZ e1 h else 0) = (if h : e2 ∈ Ustar G C then fZ e2 h else 0) at heq
        rw [dif_pos he1', dif_pos he2'] at heq
        let z := fZ e1 he1'
        have hz : z ∈ centreless G C := hfZmem e1 he1'
        obtain ⟨Fs, hFs, hEq⟩ := hZeval z hz
        have hBelow : ∀ x : Fin n → Bool, setsEval Fs x → graphFun G ∅ x = true := fun x hx =>
          (topData ((centreless_mem C z).mp hz).1).2.2 x ((hEq x).mpr hx)
        refine conj_at_most_one_centreless Fs hFs hBelow e1 he1' e2 he2' ?_ ?_
        · intro u v huv; exact (hEq _).mp (hfZval e1 he1' u v huv)
        · intro u v huv
          have h2 := hfZval e2 he2' u v huv
          rw [← heq] at h2
          exact (hEq _).mp h2
      have hSub : (Ustar G C).image (fun e => if h : e ∈ Ustar G C then fZ e h else 0) ⊆ centreless G C := by
        intro z hz
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        rw [dif_pos he]
        exact hfZmem e he
      have hc := Finset.card_le_card hSub
      rwa [Finset.card_image_of_injOn hInj] at hc
    omega
  have hAtMostOneR_eval : ∀ (L m0 : ℕ), m0 < L → m0 ∈ orN G C \ lam G C →
      (∀ r ∈ orN G C \ lam G C, r < L → r = m0) →
      (orIn n C (n + m0) = ∅ →
        ∃ Fs0 Fs1 : Finset (Finset (Fin n)), (∀ S ∈ Fs0, MonoSet S) ∧ (∀ S ∈ Fs1, MonoSet S) ∧
          (∀ x : Fin n → Bool, gateVal n C m0 x = true ↔ setsEval Fs0 x ∨ setsEval Fs1 x) ∧
          ∀ w : ℕ, w < n + L →
            (w < n ∨ ∃ g, w = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g) →
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ setsEval Fs x) ∨
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔
                setsEval Fs x ∧ (setsEval Fs0 x ∨ setsEval Fs1 x))) ∧
      ((orIn n C (opnd C m0 0)).Nonempty → (orIn n C (opnd C m0 1)).Nonempty →
        ∃ Fs0 Fs1 : Finset (Finset (Fin n)), (∀ S ∈ Fs0, MonoSet S) ∧ (∀ S ∈ Fs1, MonoSet S) ∧
          (∀ x : Fin n → Bool, gateVal n C m0 x = true ↔ setsEval Fs0 x ∨ setsEval Fs1 x) ∧
          ∀ w : ℕ, w < n + L →
            (w < n ∨ ∃ g, w = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g) →
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ setsEval Fs x) ∨
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔
                setsEval Fs x ∧ (setsEval Fs0 x ∨ setsEval Fs1 x))) ∧
      (∀ d0 : Fin 2, orIn n C (opnd C m0 d0) = ∅ → (orIn n C (opnd C m0 (1 - d0))).Nonempty →
        ∃ j1 : ℕ, j1 < m0 ∧ j1 ∈ junk G C ∧ opnd C m0 d0 = n + j1 ∧
          (∃ FsJ : Finset (Finset (Fin n)), (∀ S ∈ FsJ, MonoSet S) ∧
            ∀ x : Fin n → Bool, gateVal n C j1 x = true ↔ setsEval FsJ x) ∧
          (∃ W0 : Finset (Fin n), MonoSet W0 ∧ orIn n C (n + m0) = W0 ∧
            ∀ x : Fin n → Bool, gateVal n C m0 x = true ↔ (∃ v ∈ W0, x v = true) ∨ gateVal n C j1 x = true) ∧
          ∀ w : ℕ, w < n + L →
            (w < n ∨ ∃ g, w = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g) →
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ setsEval Fs x) ∨
            (∃ FsA FsB : Finset (Finset (Fin n)), FsB ⊆ FsA ∧ (∀ S ∈ FsA, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔
                setsEval FsA x ∨ (setsEval FsB x ∧ gateVal n C j1 x = true))) := by
    intro L m0 hm0L hm0R hUniqR
    have hm0N := (Finset.mem_sdiff.mp hm0R).1
    obtain ⟨hm0len, hm0op, hm0nb⟩ := (orN_mem C m0).mp hm0N
    have hNoRBelow : ∀ r ∈ orN G C \ lam G C, ¬ r < m0 := fun r hr hlt =>
      Nat.ne_of_lt hlt (hUniqR r hr (lt_trans hlt hm0L))
    have hOpndBelow : ∀ b : Fin 2, ∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C m0 b) = true ↔ setsEval Fs x := by
      intro b
      have hblt := opndBound hm0len b
      refine pure_no_R_eval m0 hNoRBelow (opnd C m0 b) hblt ?_
      by_cases hbn : opnd C m0 b < n
      · exact Or.inl hbn
      · right
        refine ⟨opnd C m0 b - n, by omega, by omega, ?_⟩
        intro hbk
        have hcone : InCone n C (opnd C m0 b - n) m0 :=
          (inCone_iff _ m0).mpr ⟨hm0len, opnd C m0 b - n, by omega, by
            have he : n + (opnd C m0 b - n) = opnd C m0 b := by omega
            rw [he]; exact opndMem hm0len b, Or.inl rfl⟩
        exact not_belowF_inCone_dirty (by omega) hbk hm0len hm0nb hcone
    have hm0Val : ∀ x : Fin n → Bool, gateVal n C m0 x = true ↔
        val C (List.ofFn x) (opnd C m0 0) = true ∨ val C (List.ofFn x) (opnd C m0 1) = true := by
      intro x
      rw [gateVal_eq_val, val_or List.length_ofFn hm0len hm0op]
      constructor
      · rintro ⟨i, hi, _, hvi⟩
        obtain ⟨b, rfl⟩ := inputsAsOpnd hm0len hi
        fin_cases b
        · exact Or.inl hvi
        · exact Or.inr hvi
      · rintro (h0 | h1)
        · exact ⟨opnd C m0 0, opndMem hm0len 0, opndBound hm0len 0, h0⟩
        · exact ⟨opnd C m0 1, opndMem hm0len 1, opndBound hm0len 1, h1⟩
    have hNoLamAbove : (∀ h ∈ lam G C, h < L → ¬ OrReaches n C (n + h) m0) →
        ∃ Fs0 Fs1 : Finset (Finset (Fin n)), (∀ S ∈ Fs0, MonoSet S) ∧ (∀ S ∈ Fs1, MonoSet S) ∧
          (∀ x : Fin n → Bool, gateVal n C m0 x = true ↔ setsEval Fs0 x ∨ setsEval Fs1 x) ∧
          ∀ w : ℕ, w < n + L →
            (w < n ∨ ∃ g, w = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g) →
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔ setsEval Fs x) ∨
            (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) w = true ↔
                setsEval Fs x ∧ (setsEval Fs0 x ∨ setsEval Fs1 x)) := by
      intro hNoLam
      obtain ⟨Fs0, hM0, hE0⟩ := hOpndBelow 0
      obtain ⟨Fs1, hM1, hE1⟩ := hOpndBelow 1
      have hm0Eq : ∀ x : Fin n → Bool, gateVal n C m0 x = true ↔ setsEval Fs0 x ∨ setsEval Fs1 x := by
        intro x; rw [hm0Val, hE0, hE1]
      refine ⟨Fs0, Fs1, hM0, hM1, hm0Eq, ?_⟩
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hkind
        rcases hkind with hwn | ⟨g, rfl, hglen, hgnb⟩
        · left
          exact pure_no_R_eval m0 hNoRBelow w (by omega) (Or.inl hwn)
        · by_cases hgm0 : g = m0
          · subst g
            right
            refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ h), fun x => ?_⟩
            rw [← gateVal_eq_val, hm0Eq]
            exact ⟨fun h => ⟨setsEval_empty x, h⟩, fun h => h.2⟩
          · rcases hLeast.1.1 _ (gateAt_mem hglen) with hand | hor
            · have hsub : ∀ b : Fin 2,
                  (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
                    ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔ setsEval Fs x) ∨
                  (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
                    ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔
                      setsEval Fs x ∧ (setsEval Fs0 x ∨ setsEval Fs1 x)) := by
                intro b
                have hblt := opndBound hglen b
                refine ih (opnd C g b) hblt (by omega) ?_
                by_cases hbn : opnd C g b < n
                · exact Or.inl hbn
                · right
                  refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
                  intro hbk
                  have hcone : InCone n C (opnd C g b - n) g :=
                    (inCone_iff _ g).mpr ⟨hglen, opnd C g b - n, by omega, by
                      have he : n + (opnd C g b - n) = opnd C g b := by omega
                      rw [he]; exact opndMem hglen b, Or.inl rfl⟩
                  exact not_belowF_inCone_and (by omega) hbk hglen hand hcone
              rcases hsub 0 with ⟨A0, hMA0, hEA0⟩ | ⟨A0, hMA0, hEA0⟩ <;>
                rcases hsub 1 with ⟨A1, hMA1, hEA1⟩ | ⟨A1, hMA1, hEA1⟩
              · left
                refine ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union]
              · right
                refine ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union, and_assoc]
              · right
                refine ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union]
                exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
              · right
                refine ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union]
                exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
            · have hgN : g ∈ orN G C := (orN_mem C g).mpr ⟨hglen, hor, hgnb⟩
              have hgLam : g ∈ lam G C := by
                by_contra hnot
                exact hgm0 (hUniqR g (Finset.mem_sdiff.mpr ⟨hgN, hnot⟩) (by omega))
              have hPureOrLam : ∀ (k : ℕ), k < L → k ∈ lam G C →
                  ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true ↔ ∃ v ∈ orIn n C (n + k), x v = true := by
                intro k
                induction k using Nat.strong_induction_on with
                | ind k ihk =>
                  intro hkL hkLam x
                  have hkN := ((lam_mem C k).mp hkLam).1
                  obtain ⟨hklen, hkop, hknb⟩ := (orN_mem C k).mp hkN
                  rw [val_or List.length_ofFn hklen hkop]
                  constructor
                  · rintro ⟨i, hi, hilt, hvi⟩
                    by_cases hin : i < n
                    · have hv : x ⟨i, hin⟩ = true := by
                        have hget := val_ofFn C x ⟨i, hin⟩
                        exact hget.symm.trans hvi
                      exact ⟨⟨i, hin⟩, reach_mem_orIn ⟨i, hin⟩ (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ Relation.ReflTransGen.refl), hv⟩
                    · let r := i - n
                      have hreq : i = n + r := by omega
                      have hrnb : ¬ BelowF G C r := by
                        intro hbr
                        have hcone : InCone n C r k :=
                          (inCone_iff r k).mpr ⟨hklen, r, by omega, hreq ▸ hi, Or.inl rfl⟩
                        exact not_belowF_inCone_dirty (by omega) hbr hklen hknb hcone
                      have hrop : (gateAt C r).op = GateOp.or := by
                        rcases hLeast.1.1 _ (gateAt_mem (j := r) (by omega)) with hrand | hror
                        · have hrj : r ∈ junk G C := by
                            refine (junk_mem C r).mpr ⟨by omega, hrand, ?_⟩
                            by_contra hnone
                            apply hrnb
                            intro y hy
                            by_contra hf
                            exact hnone ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
                          exact False.elim ((Finset.mem_sdiff.mp (lastOrOutside hrj hklen hkop (hreq ▸ hi) (by omega))).2 hkLam)
                        · exact hror
                      have hrN : r ∈ orN G C := (orN_mem C r).mpr ⟨by omega, hrop, hrnb⟩
                      have hrLam : r ∈ lam G C := by
                        by_contra hnot
                        have hrm0 := hUniqR r (Finset.mem_sdiff.mpr ⟨hrN, hnot⟩) (by omega)
                        have him0 : i = n + m0 := by omega
                        have hkr : OrReaches n C (n + k) m0 :=
                          reach_orReaches (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, him0 ▸ hi, by omega⟩ Relation.ReflTransGen.refl) m0 rfl hm0len
                        exact hNoLam k hkLam hkL hkr
                      rw [hreq] at hvi
                      obtain ⟨v, hv, hxv⟩ := (ihk r (by omega) (by omega) hrLam x).mp hvi
                      exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ (mem_orIn_reach v (hreq.symm ▸ hv))), hxv⟩
                  · rintro ⟨v, hv, hxv⟩
                    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨i, hstep, hrest⟩
                    · have := v.isLt; omega
                    · obtain ⟨k0, _, hek, _, hi, hilt⟩ := hstep
                      have : k0 = k := by omega
                      subst k0
                      exact ⟨i, hi, hilt, reach_var_val x i v hrest hxv⟩
              left
              refine ⟨{orIn n C (n + g)}, ?_, ?_⟩
              · intro S hS; rw [Finset.mem_singleton.mp hS]; exact monoSet_lam hgLam
              · intro x
                rw [hPureOrLam g (by omega) hgLam x]
                exact ⟨fun h S hS => by rw [Finset.mem_singleton.mp hS]; exact h, fun h => h _ (Finset.mem_singleton_self _)⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hm0Empty
      apply hNoLamAbove
      intro h hh hhL hreach
      rcases lastOrBefore (orReaches_reach m0 _ hreach).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, hhr⟩
      · have hne : (orIn n C (n + h)).Nonempty := or_nonempty_of_lam hh
        rw [heq, hm0Empty] at hne
        exact Finset.not_nonempty_empty hne
      · have hrR : r ∈ orN G C \ lam G C := by
          have hrnb : ¬ BelowF G C r := by
            intro hrb'
            apply hm0nb
            intro x hx
            exact hrb' x ((val_or List.length_ofFn hrlen hrop).mpr ⟨n + m0, hrin, hrb, hx⟩)
          refine Finset.mem_sdiff.mpr ⟨(orN_mem C r).mpr ⟨hrlen, hrop, hrnb⟩, ?_⟩
          intro hrlam
          obtain ⟨_, h0, h1, _⟩ := (lam_mem C r).mp hrlam
          obtain ⟨b, hb⟩ := inputsAsOpnd hrlen hrin
          have hne : (orIn n C (opnd C r b)).Nonempty := by fin_cases b; exact h0; exact h1
          rw [← hb, hm0Empty] at hne
          exact Finset.not_nonempty_empty hne
        have hrle : r ≤ h := by
          have := orStep_le hhr
          omega
        have hrm0 := hUniqR r hrR (by omega)
        omega
    · intro h0 h1
      apply hNoLamAbove
      intro h hh _ hreach
      exact no_bothNonempty_R_below_lam hm0R hh h0 h1 hreach
    · intro d0 hEmp hNe
      have hd0_ge : n ≤ opnd C m0 d0 := by
        by_contra hlt
        have hmem : ⟨opnd C m0 d0, by omega⟩ ∈ orIn n C (opnd C m0 d0) :=
          reach_mem_orIn ⟨opnd C m0 d0, by omega⟩ Relation.ReflTransGen.refl
        rw [hEmp] at hmem
        exact Finset.notMem_empty _ hmem
      let j1 := opnd C m0 d0 - n
      have hj1eq : opnd C m0 d0 = n + j1 := by omega
      have hj1lt : j1 < m0 := by have := opndBound hm0len d0; omega
      have hj1len : j1 < C.gates.length := by omega
      have hj1nb : ¬ BelowF G C j1 := by
        intro hbj1
        have hcone : InCone n C j1 m0 :=
          (inCone_iff j1 m0).mpr ⟨hm0len, j1, hj1lt, hj1eq ▸ opndMem hm0len d0, Or.inl rfl⟩
        exact not_belowF_inCone_dirty hj1len hbj1 hm0len hm0nb hcone
      have hj1op : (gateAt C j1).op = GateOp.and := by
        rcases hLeast.1.1 _ (gateAt_mem hj1len) with hand | hor
        · exact hand
        · have hj1N : j1 ∈ orN G C := (orN_mem C j1).mpr ⟨hj1len, hor, hj1nb⟩
          have hj1notLam : j1 ∉ lam G C := fun hlam => by
            have hne := or_nonempty_of_lam hlam
            rw [← hj1eq, hEmp] at hne
            exact Finset.not_nonempty_empty hne
          exact False.elim (hNoRBelow j1 (Finset.mem_sdiff.mpr ⟨hj1N, hj1notLam⟩) hj1lt)
      have hj1Mem : j1 ∈ junk G C := by
        refine (junk_mem C j1).mpr ⟨hj1len, hj1op, ?_⟩
        by_contra hnone
        apply hj1nb
        intro x hx
        by_contra hf
        exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
      obtain ⟨FsJ, hMFsJ, hEFsJ⟩ := hOpndBelow d0
      have hEFsJ' : ∀ x : Fin n → Bool, gateVal n C j1 x = true ↔ setsEval FsJ x := by
        intro x
        rw [gateVal_eq_val, ← hj1eq]
        exact hEFsJ x
      have hW0_pure : ∃ W0 : Finset (Fin n), MonoSet W0 ∧ orIn n C (n + m0) = W0 ∧
          ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C m0 (1 - d0)) = true ↔ ∃ v ∈ W0, x v = true := by
        let w1 := opnd C m0 (1 - d0)
        have hw1lt : w1 < n + m0 := opndBound hm0len (1 - d0)
        have horEq : orIn n C (n + m0) = orIn n C w1 := by
          ext v
          constructor
          · intro hv
            rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨i, hstep, hrest⟩
            · have := v.isLt; omega
            · obtain ⟨k, _, hek, _, hi, _⟩ := hstep
              have : k = m0 := by omega
              subst k
              obtain ⟨b, rfl⟩ := inputsAsOpnd hm0len hi
              by_cases hb : b = d0
              · subst b
                have hv' := reach_mem_orIn v hrest
                rw [hEmp] at hv'
                exact False.elim (Finset.notMem_empty _ hv')
              · have hb' : b = 1 - d0 := by fin_cases d0 <;> fin_cases b <;> first | rfl | exact False.elim (hb rfl)
                subst b
                exact reach_mem_orIn v hrest
          · intro hv
            have hstep : OrStep (n + m0) w1 := ⟨m0, hm0len, rfl, hm0op, opndMem hm0len (1 - d0), hw1lt⟩
            exact reach_mem_orIn v (Relation.ReflTransGen.head hstep (mem_orIn_reach v hv))
        by_cases hw1n : w1 < n
        · have horSingle : orIn n C w1 = {⟨w1, hw1n⟩} := by
            ext v
            rw [Finset.mem_singleton]
            constructor
            · intro hv
              rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨_, hstep, _⟩
              · exact Fin.ext he.symm
              · obtain ⟨k, _, hk, _, _, _⟩ := hstep; omega
            · rintro rfl
              exact reach_mem_orIn ⟨w1, hw1n⟩ Relation.ReflTransGen.refl
          refine ⟨orIn n C w1, by rw [horSingle]; exact monoSet_singleton _, horEq, fun x => ?_⟩
          rw [horSingle, val_input List.length_ofFn hw1n]
          have hget : (List.ofFn x).getD w1 false = x ⟨w1, hw1n⟩ := by
            simp [List.getD_eq_getElem?_getD, hw1n]
          rw [hget]
          constructor
          · intro hx; exact ⟨⟨w1, hw1n⟩, Finset.mem_singleton_self _, hx⟩
          · rintro ⟨v, hv, hxv⟩; rwa [Finset.mem_singleton.mp hv] at hxv
        · let h1 := w1 - n
          have hh1eq : w1 = n + h1 := by omega
          have hh1lt : h1 < m0 := by omega
          have hh1len : h1 < C.gates.length := by omega
          have hh1nb : ¬ BelowF G C h1 := by
            intro hb1
            have hcone : InCone n C h1 m0 :=
              (inCone_iff h1 m0).mpr ⟨hm0len, h1, hh1lt, hh1eq ▸ opndMem hm0len (1 - d0), Or.inl rfl⟩
            exact not_belowF_inCone_dirty hh1len hb1 hm0len hm0nb hcone
          have hh1op : (gateAt C h1).op = GateOp.or := by
            rcases hLeast.1.1 _ (gateAt_mem hh1len) with hand | hor
            · have hne' := hNe
              change (orIn n C w1).Nonempty at hne'
              rw [hh1eq, andRawEmpty hand] at hne'
              exact False.elim (Finset.not_nonempty_empty hne')
            · exact hor
          have hh1Lam : h1 ∈ lam G C := by
            by_contra hnot
            exact hNoRBelow h1 (Finset.mem_sdiff.mpr ⟨(orN_mem C h1).mpr ⟨hh1len, hh1op, hh1nb⟩, hnot⟩) hh1lt
          have hPureBelow : ∀ w', w' < n + m0 →
              (w' < n ∨ ∃ k, w' = n + k ∧ k < C.gates.length ∧ k ∈ lam G C) →
              ∀ x : Fin n → Bool, val C (List.ofFn x) w' = true ↔ ∃ v ∈ orIn n C w', x v = true := by
            intro w'
            induction w' using Nat.strong_induction_on with
            | ind w' ih' =>
              intro hw'lt hw'kind x
              rcases hw'kind with hw'n | ⟨k, rfl, hklen, hklam⟩
              · rw [val_input List.length_ofFn hw'n]
                have hget : (List.ofFn x).getD w' false = x ⟨w', hw'n⟩ := by
                  simp [List.getD_eq_getElem?_getD, hw'n]
                rw [hget]
                constructor
                · intro hx; exact ⟨⟨w', hw'n⟩, reach_mem_orIn ⟨w', hw'n⟩ Relation.ReflTransGen.refl, hx⟩
                · rintro ⟨v, hv, hxv⟩
                  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨_, hstep, _⟩
                  · have : v = ⟨w', hw'n⟩ := Fin.ext he.symm
                    rwa [← this]
                  · obtain ⟨r, _, hr, _, _, _⟩ := hstep; omega
              · have hkN := ((lam_mem C k).mp hklam).1
                obtain ⟨_, hkop, hknb⟩ := (orN_mem C k).mp hkN
                rw [val_or List.length_ofFn hklen hkop]
                constructor
                · rintro ⟨i, hi, hilt, hvi⟩
                  have hikind : i < n ∨ ∃ r, i = n + r ∧ r < C.gates.length ∧ r ∈ lam G C := by
                    by_cases hin : i < n
                    · exact Or.inl hin
                    · right
                      let r := i - n
                      have hreq : i = n + r := by omega
                      have hrnb : ¬ BelowF G C r := by
                        intro hbr
                        have hcone : InCone n C r k :=
                          (inCone_iff r k).mpr ⟨hklen, r, by omega, hreq ▸ hi, Or.inl rfl⟩
                        exact not_belowF_inCone_dirty (by omega) hbr hklen hknb hcone
                      have hrop : (gateAt C r).op = GateOp.or := by
                        rcases hLeast.1.1 _ (gateAt_mem (j := r) (by omega)) with hrand | hror
                        · have hrj : r ∈ junk G C := by
                            refine (junk_mem C r).mpr ⟨by omega, hrand, ?_⟩
                            by_contra hnone
                            apply hrnb
                            intro y hy
                            by_contra hf
                            exact hnone ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
                          exact False.elim ((Finset.mem_sdiff.mp (lastOrOutside hrj hklen hkop (hreq ▸ hi) (by omega))).2 hklam)
                        · exact hror
                      have hrLam : r ∈ lam G C := by
                        by_contra hnot
                        exact hNoRBelow r (Finset.mem_sdiff.mpr ⟨(orN_mem C r).mpr ⟨by omega, hrop, hrnb⟩, hnot⟩) (by omega)
                      exact ⟨r, hreq, by omega, hrLam⟩
                  obtain ⟨v, hv, hxv⟩ := (ih' i hilt (by omega) hikind x).mp hvi
                  exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ (mem_orIn_reach v hv)), hxv⟩
                · rintro ⟨v, hv, hxv⟩
                  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨i, hstep, hrest⟩
                  · have := v.isLt; omega
                  · obtain ⟨k0, _, hek, _, hi, hilt⟩ := hstep
                    have : k0 = k := by omega
                    subst k0
                    exact ⟨i, hi, hilt, reach_var_val x i v hrest hxv⟩
          refine ⟨orIn n C w1, by rw [hh1eq]; exact monoSet_lam hh1Lam, horEq, ?_⟩
          exact hPureBelow w1 hw1lt (Or.inr ⟨h1, hh1eq, hh1len, hh1Lam⟩)
      obtain ⟨W0, hMW0, horM0Eq, hW0val⟩ := hW0_pure
      have hm0Eq : ∀ x : Fin n → Bool, gateVal n C m0 x = true ↔
          (∃ v ∈ W0, x v = true) ∨ gateVal n C j1 x = true := by
        intro x
        rw [hm0Val]
        fin_cases d0
        · have h0 : opnd C m0 0 = n + j1 := hj1eq
          have h1 : val C (List.ofFn x) (opnd C m0 1) = true ↔ ∃ v ∈ W0, x v = true := hW0val x
          rw [h0, ← gateVal_eq_val, h1, or_comm]
        · have h1 : opnd C m0 1 = n + j1 := hj1eq
          have h0 : val C (List.ofFn x) (opnd C m0 0) = true ↔ ∃ v ∈ W0, x v = true := hW0val x
          rw [h1, ← gateVal_eq_val, h0]
      have hLamEval : ∀ (k : ℕ), k < L → k ∈ lam G C →
          ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true ↔
            (∃ v ∈ orIn n C (n + k), x v = true) ∨ (OrReaches n C (n + k) m0 ∧ gateVal n C j1 x = true) := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ihk =>
          intro hkL hkLam x
          have hkN := ((lam_mem C k).mp hkLam).1
          obtain ⟨hklen, hkop, hknb⟩ := (orN_mem C k).mp hkN
          rw [val_or List.length_ofFn hklen hkop]
          constructor
          · rintro ⟨i, hi, hilt, hvi⟩
            by_cases hin : i < n
            · left
              have hv : x ⟨i, hin⟩ = true := (val_ofFn C x ⟨i, hin⟩).symm.trans hvi
              exact ⟨⟨i, hin⟩, reach_mem_orIn ⟨i, hin⟩ (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ Relation.ReflTransGen.refl), hv⟩
            · let r := i - n
              have hreq : i = n + r := by omega
              have hrnb : ¬ BelowF G C r := by
                intro hbr
                have hcone : InCone n C r k :=
                  (inCone_iff r k).mpr ⟨hklen, r, by omega, hreq ▸ hi, Or.inl rfl⟩
                exact not_belowF_inCone_dirty (by omega) hbr hklen hknb hcone
              have hrop : (gateAt C r).op = GateOp.or := by
                rcases hLeast.1.1 _ (gateAt_mem (j := r) (by omega)) with hrand | hror
                · have hrj : r ∈ junk G C := by
                    refine (junk_mem C r).mpr ⟨by omega, hrand, ?_⟩
                    by_contra hnone
                    apply hrnb
                    intro y hy
                    by_contra hf
                    exact hnone ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
                  exact False.elim ((Finset.mem_sdiff.mp (lastOrOutside hrj hklen hkop (hreq ▸ hi) (by omega))).2 hkLam)
                · exact hror
              by_cases hrLam : r ∈ lam G C
              · rw [hreq] at hvi
                rcases (ihk r (by omega) (by omega) hrLam x).mp hvi with ⟨v, hv, hxv⟩ | ⟨hrm0, hj1x⟩
                · left
                  exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head ⟨k, hklen, rfl, hkop, hi, hilt⟩ (mem_orIn_reach v (hreq.symm ▸ hv))), hxv⟩
                · right
                  have hstep : OrStep (n + k) (n + r) := ⟨k, hklen, rfl, hkop, hreq ▸ hi, by omega⟩
                  exact ⟨reach_orReaches (Relation.ReflTransGen.head hstep (orReaches_reach m0 _ hrm0).1) m0 rfl hm0len, hj1x⟩
              · have hrm0 := hUniqR r (Finset.mem_sdiff.mpr ⟨(orN_mem C r).mpr ⟨by omega, hrop, hrnb⟩, hrLam⟩) (by omega)
                have him0 : i = n + m0 := by omega
                rw [him0, ← gateVal_eq_val, hm0Eq] at hvi
                have hstep : OrStep (n + k) (n + m0) := ⟨k, hklen, rfl, hkop, him0 ▸ hi, by omega⟩
                rcases hvi with ⟨v, hvW0, hxv⟩ | hj1x
                · left
                  rw [← horM0Eq] at hvW0
                  exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head hstep (mem_orIn_reach v hvW0)), hxv⟩
                · right
                  exact ⟨reach_orReaches (Relation.ReflTransGen.head hstep Relation.ReflTransGen.refl) m0 rfl hm0len, hj1x⟩
          · rintro (⟨v, hv, hxv⟩ | ⟨hkm0, hj1x⟩)
            · rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨i, hstep, hrest⟩
              · have := v.isLt; omega
              · obtain ⟨k0, _, hek, _, hi, hilt⟩ := hstep
                have : k0 = k := by omega
                subst k0
                exact ⟨i, hi, hilt, reach_var_val x i v hrest hxv⟩
            · have hm0v : val C (List.ofFn x) (n + m0) = true := by
                rw [← gateVal_eq_val, hm0Eq]; exact Or.inr hj1x
              have hktrue := orStep_up List.length_ofFn (orReaches_reach m0 _ hkm0).1 hm0v
              exact (val_or List.length_ofFn hklen hkop).mp hktrue
      refine ⟨j1, hj1lt, hj1Mem, hj1eq, ⟨FsJ, hMFsJ, hEFsJ'⟩, ⟨W0, hMW0, horM0Eq, hm0Eq⟩, ?_⟩
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hkind
        rcases hkind with hwn | ⟨g, rfl, hglen, hgnb⟩
        · left
          exact pure_no_R_eval m0 hNoRBelow w (by omega) (Or.inl hwn)
        · by_cases hgm0 : g = m0
          · subst g
            right
            refine ⟨{W0}, ∅, Finset.empty_subset _, ?_, fun x => ?_⟩
            · intro S hS; rw [Finset.mem_singleton.mp hS]; exact hMW0
            · rw [← gateVal_eq_val, hm0Eq]
              constructor
              · rintro (hW | hj)
                · left; intro S hS; rw [Finset.mem_singleton.mp hS]; exact hW
                · right; exact ⟨setsEval_empty x, hj⟩
              · rintro (hA | ⟨_, hj⟩)
                · exact Or.inl (hA W0 (Finset.mem_singleton_self W0))
                · exact Or.inr hj
          · rcases hLeast.1.1 _ (gateAt_mem hglen) with hand | hor
            · have hsub : ∀ b : Fin 2,
                  (∃ Fs : Finset (Finset (Fin n)), (∀ S ∈ Fs, MonoSet S) ∧
                    ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔ setsEval Fs x) ∨
                  (∃ FsA FsB : Finset (Finset (Fin n)), FsB ⊆ FsA ∧ (∀ S ∈ FsA, MonoSet S) ∧
                    ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔
                      setsEval FsA x ∨ (setsEval FsB x ∧ gateVal n C j1 x = true)) := by
                intro b
                have hblt := opndBound hglen b
                refine ih (opnd C g b) hblt (by omega) ?_
                by_cases hbn : opnd C g b < n
                · exact Or.inl hbn
                · right
                  refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
                  intro hbk
                  have hcone : InCone n C (opnd C g b - n) g :=
                    (inCone_iff _ g).mpr ⟨hglen, opnd C g b - n, by omega, by
                      have he : n + (opnd C g b - n) = opnd C g b := by omega
                      rw [he]; exact opndMem hglen b, Or.inl rfl⟩
                  exact not_belowF_inCone_and (by omega) hbk hglen hand hcone
              rcases hsub 0 with ⟨A0, hMA0, hEA0⟩ | ⟨A0, B0, hBA0, hMA0, hEA0⟩ <;>
                rcases hsub 1 with ⟨A1, hMA1, hEA1⟩ | ⟨A1, B1, hBA1, hMA1, hEA1⟩
              · left
                refine ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union]
              · right
                refine ⟨A0 ∪ A1, A0 ∪ B1, Finset.union_subset_union_right hBA1,
                  fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union, setsEval_union]
                exact ⟨fun h => h.2.elim (fun a1 => Or.inl ⟨h.1, a1⟩) (fun h1 => Or.inr ⟨⟨h.1, h1.1⟩, h1.2⟩),
                  fun h => h.elim (fun h1 => ⟨h1.1, Or.inl h1.2⟩) (fun h1 => ⟨h1.1.1, Or.inr ⟨h1.1.2, h1.2⟩⟩)⟩
              · right
                refine ⟨A0 ∪ A1, B0 ∪ A1, Finset.union_subset_union_left hBA0,
                  fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union, setsEval_union]
                exact ⟨fun h => h.1.elim (fun a0 => Or.inl ⟨a0, h.2⟩) (fun h0 => Or.inr ⟨⟨h0.1, h.2⟩, h0.2⟩),
                  fun h => h.elim (fun h1 => ⟨Or.inl h1.1, h1.2⟩) (fun h1 => ⟨Or.inr ⟨h1.1.1, h1.2⟩, h1.1.2⟩)⟩
              · right
                refine ⟨A0 ∪ A1, B0 ∪ B1, Finset.union_subset_union hBA0 hBA1,
                  fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
                rw [← gateVal_eq_val, andValBoth hglen hand, hEA0, hEA1, setsEval_union, setsEval_union]
                constructor
                · rintro ⟨h0 | ⟨hb0, hj⟩, h1 | ⟨hb1, hj'⟩⟩
                  · exact Or.inl ⟨h0, h1⟩
                  · exact Or.inr ⟨⟨setsEval_mono_sub hBA0 h0, hb1⟩, hj'⟩
                  · exact Or.inr ⟨⟨hb0, setsEval_mono_sub hBA1 h1⟩, hj⟩
                  · exact Or.inr ⟨⟨hb0, hb1⟩, hj⟩
                · rintro (⟨h0, h1⟩ | ⟨⟨hb0, hb1⟩, hj⟩)
                  · exact ⟨Or.inl h0, Or.inl h1⟩
                  · exact ⟨Or.inr ⟨hb0, hj⟩, Or.inr ⟨hb1, hj⟩⟩
            · have hgN : g ∈ orN G C := (orN_mem C g).mpr ⟨hglen, hor, hgnb⟩
              have hgLam : g ∈ lam G C := by
                by_contra hnot
                exact hgm0 (hUniqR g (Finset.mem_sdiff.mpr ⟨hgN, hnot⟩) (by omega))
              by_cases hgm0r : OrReaches n C (n + g) m0
              · right
                refine ⟨{orIn n C (n + g)}, ∅, Finset.empty_subset _, ?_, fun x => ?_⟩
                · intro S hS; rw [Finset.mem_singleton.mp hS]; exact monoSet_lam hgLam
                · rw [hLamEval g (by omega) hgLam x]
                  constructor
                  · rintro (h | ⟨_, hj⟩)
                    · exact Or.inl (fun S hS => by rw [Finset.mem_singleton.mp hS]; exact h)
                    · exact Or.inr ⟨setsEval_empty x, hj⟩
                  · rintro (h | ⟨_, hj⟩)
                    · exact Or.inl (h _ (Finset.mem_singleton_self _))
                    · exact Or.inr ⟨hgm0r, hj⟩
              · left
                refine ⟨{orIn n C (n + g)}, ?_, fun x => ?_⟩
                · intro S hS; rw [Finset.mem_singleton.mp hS]; exact monoSet_lam hgLam
                · rw [hLamEval g (by omega) hgLam x]
                  constructor
                  · rintro (h | ⟨hr, _⟩)
                    · exact fun S hS => by rw [Finset.mem_singleton.mp hS]; exact h
                    · exact False.elim (hgm0r hr)
                  · intro h
                    exact Or.inl (h _ (Finset.mem_singleton_self _))
  have hZplusR_ge3 : 3 ≤ (centreless G C).card + (orN G C \ lam G C).card := by
    by_contra hLt3
    have hRle2 : (orN G C \ lam G C).card ≤ 2 := by omega
    have hZle1 : (centreless G C).card ≤ 1 := by omega
    have hCard_union_two : ∀ (U1 U2 : Finset (Sym2 (Fin n))),
        Ustar G C ⊆ U1 ∪ U2 → U1.card ≤ 1 → U2.card ≤ 1 → (Ustar G C).card ≤ 2 := by
      intro U1 U2 hsub h1 h2
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le U1 U2).trans (by omega))
    have hRouteSingleR : ∀ (m : ℕ), m ∈ orN G C \ lam G C → (orIn n C (n + m)).Nonempty →
        ∀ (j : ℕ), j ∈ junk G C →
        ∀ (u v : Fin n) (t : ℕ) (d : Fin 2), t ∈ tops G C → t ∉ centreless G C →
          gateVal n C t (pairInput u v) = true → s(u, v) ∈ Ustar G C →
          OrReaches n C (opnd C t d) m → OrReaches n C (opnd C t d) j →
          gateVal n C j (pairInput u v) = true →
          ∀ z0 ∈ orIn n C (n + m), col u = col z0 → col v = !(col z0) →
          ((∀ r ∈ orN G C \ lam G C, r = m) →
            G.Adj z0 v ∧ u ≠ z0 ∧
              ∀ w : Fin n, gateVal n C j (pairInput w v) = true → G.Adj w v) := by
      intro m hm _ j hj u v t d ht htnc htv heU hrm hrj _ z0 hz0 hcu hcv hAllM
      obtain ⟨htlen, htop, htb⟩ := topData ht
      have hz0_side : z0 ∈ side (n := n) C t d := by
        rw [side_def]
        exact orIn_mono hrm hz0
      have hnoOtherJunk : ∀ j' ∈ junk G C, ¬ OrReaches n C (opnd C t (1 - d)) j' := by
        intro j' hj' hr'
        rcases lastOrBefore (orReaches_reach j' _ hr').1 with heq | ⟨r, hrlen, ho, hi, hb, htr⟩
        · exact htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj').2.1))
        · have hrEq := hAllM r (lastOrOutside hj' hrlen ho hi hb)
          subst r
          have hmData := (orN_mem C m).mp (Finset.mem_sdiff.mp hm).1
          apply hmData.2.2
          intro x hx
          have h1 := orStep_up List.length_ofFn (orReaches_reach m _ hrm).1 hx
          have h2 := orStep_up List.length_ofFn htr hx
          exact htb x ((andValOperands htlen htop x).mpr (fun q => by
            fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2))
      have hOtherVal := (andValOperands htlen htop _).mp htv (1 - d)
      have hv_side : v ∈ side (n := n) C t (1 - d) := by
        rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', _⟩
        · subst x
          have hadjz0u : G.Adj z0 u := by
            fin_cases d
            · exact topAdj ht hz0_side hxs
            · exact (topAdj ht hxs hz0_side).symm
          exact False.elim (hbip z0 u hadjz0u hcu.symm)
        · subst x; exact hxs
        · exact False.elim (hnoOtherJunk j' hj' hr')
      have hadjz0v : G.Adj z0 v := by
        fin_cases d
        · exact topAdj ht hz0_side hv_side
        · exact (topAdj ht hv_side hz0_side).symm
      have huz0 : u ≠ z0 := by
        intro heq
        subst u
        have hstar : s(z0, v) ∈ starEdges G C := by
          rw [starEdges_def]
          refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
          fin_cases d
          · exact Finset.mem_image.mpr ⟨(z0, v), Finset.mem_product.mpr ⟨hz0_side, hv_side⟩, rfl⟩
          · exact Finset.mem_image.mpr ⟨(v, z0), Finset.mem_product.mpr ⟨hv_side, hz0_side⟩, Sym2.eq_swap⟩
        rw [Ustar_def] at heU
        exact (Finset.mem_sdiff.mp heU).2 hstar
      refine ⟨hadjz0v, huz0, fun w hjw => ?_⟩
      have h1 := orStep_up List.length_ofFn (orReaches_reach j _ hrj).1 hjw
      have h2 := sideVal hv_side (pairInput_right w v)
      exact (graphFun_pair w v).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
        fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
    by_cases hZ0 : (centreless G C).card = 0
    · have hZemp : centreless G C = ∅ := Finset.card_eq_zero.mp hZ0
      have hJunkNonempty : (junk G C).Nonempty := ⟨jw, hjwMem⟩
      let jmax := (junk G C).max' hJunkNonempty
      have hjmax : jmax ∈ junk G C := Finset.max'_mem _ hJunkNonempty
      have hjmaxGe : ∀ j ∈ junk G C, j ≤ jmax := fun j hj => Finset.le_max' _ j hj
      obtain ⟨rTop, hrTop⟩ := leastRead (junkData hjmax).1 (junkNotBelow hjmax)
      have hrTopLt : jmax < rTop := readLt hrTop
      have hrTopR : rTop ∈ orN G C \ lam G C := by
        rcases classifyReader (junkNotBelow hjmax) (andRawEmpty (junkData hjmax).2.1) hrTop with hj | hz | hr
        · have := hjmaxGe rTop hj; omega
        · rw [hZemp] at hz; exact False.elim (Finset.notMem_empty _ hz)
        · exact hr
      have hRne : (orN G C \ lam G C).Nonempty := ⟨rTop, hrTopR⟩
      let mMax := (orN G C \ lam G C).max' hRne
      have hmMax : mMax ∈ orN G C \ lam G C := Finset.max'_mem _ hRne
      have hmMaxGe : ∀ r ∈ orN G C \ lam G C, r ≤ mMax := fun r hr => Finset.le_max' _ r hr
      have hjmaxLtMmax : jmax < mMax := lt_of_lt_of_le hrTopLt (hmMaxGe rTop hrTopR)
      have hmMaxData := (orN_mem C mMax).mp (Finset.mem_sdiff.mp hmMax).1
      have hmMaxOrNe : (orIn n C (n + mMax)).Nonempty := by
        by_contra hme
        have hme0 : orIn n C (n + mMax) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hme
        obtain ⟨k, hk⟩ := leastRead hmMaxData.1 hmMaxData.2.2
        have hlt := readLt hk
        rcases classifyReader hmMaxData.2.2 hme0 hk with hj | hz | hr
        · have := hjmaxGe k hj; omega
        · rw [hZemp] at hz; exact False.elim (Finset.notMem_empty _ hz)
        · have := hmMaxGe k hr; omega
      by_cases hR1 : (orN G C \ lam G C).card = 1
      · have hAllM : ∀ r ∈ orN G C \ lam G C, r = mMax := fun r hr =>
          Finset.card_le_one.mp (by omega) r hr mMax hmMax
        have hNoRBelowMmax : ∀ r ∈ orN G C \ lam G C, ¬ r < mMax := fun r hr hlt =>
          Nat.ne_of_lt hlt (hAllM r hr)
        have hEmptyOpndMmax : ∃ d0 : Fin 2, opnd C mMax d0 = n + jmax ∧
            (orIn n C (opnd C mMax (1 - d0))).Nonempty ∧
            ∀ j ∈ junk G C, n + j ∈ (gateAt C mMax).inputs → j = jmax := by
          have hrEq : rTop = mMax := hAllM rTop hrTopR
          subst hrEq
          obtain ⟨d0, hd0⟩ := inputsAsOpnd hmMaxData.1 (readData hrTop).2
          have hd0Emp : orIn n C (opnd C mMax d0) = ∅ := by rw [← hd0]; exact andRawEmpty (junkData hjmax).2.1
          have hd1Ne : (orIn n C (opnd C mMax (1 - d0))).Nonempty := by
            by_contra h1e
            have h1e0 : orIn n C (opnd C mMax (1 - d0)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1e
            have htot := orEmpty (r := mMax) (fun w hw => by
              obtain ⟨b, rfl⟩ := inputsAsOpnd hmMaxData.1 hw
              fin_cases d0 <;> fin_cases b <;> first | exact hd0Emp | exact h1e0)
            rw [htot] at hmMaxOrNe
            exact Finset.not_nonempty_empty hmMaxOrNe
          refine ⟨d0, hd0.symm, hd1Ne, fun j hj hjm => ?_⟩
          obtain ⟨b, hb⟩ := inputsAsOpnd hmMaxData.1 hjm
          by_cases hbd : b = d0
          · subst b
            have : n + j = n + jmax := hb.trans hd0.symm
            omega
          · have hb1 : b = 1 - d0 := by fin_cases d0 <;> fin_cases b <;> first | rfl | exact False.elim (hbd rfl)
            subst b
            rw [← hb, andRawEmpty (junkData hj).2.1] at hd1Ne
            exact False.elim (Finset.not_nonempty_empty hd1Ne)
        obtain ⟨_, _, _, hUniqJ⟩ := hEmptyOpndMmax
        obtain ⟨FsJ, hMFsJ, hEFsJ⟩ := pure_no_R_eval mMax hNoRBelowMmax (n + jmax) (by omega)
          (Or.inr ⟨jmax, rfl, (junkData hjmax).1, junkNotBelow hjmax⟩)
        have hmMaxOrNe' := hmMaxOrNe
        obtain ⟨z0, hz0⟩ := hmMaxOrNe'
        have hTrace1 : ∀ e ∈ Ustar G C, ∀ u v : Fin n, col u = col z0 → col v = !(col z0) → e = s(u, v) →
            G.Adj z0 v ∧ u ≠ z0 ∧ setsEval FsJ (pairInput u v) ∧
              ∀ w : Fin n, setsEval FsJ (pairInput w v) → G.Adj w v := by
          intro e he u v hcu hcv rfl
          obtain ⟨t, ht, htv, d, j, hj, hrj, hjv⟩ := residualTrace he
          have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
          rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
          · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
          · have hrEq := hAllM r (lastOrOutside hj hrlen hrop hrin hrb)
            subst r
            have hjeq := hUniqJ j hj hrin
            subst j
            have hrm := reach_orReaches htr mMax rfl hmMaxData.1
            obtain ⟨hzv, huz, hfire⟩ := hRouteSingleR mMax hmMax hmMaxOrNe jmax hjmax u v t d ht htnc htv he hrm hrj hjv z0 hz0 hcu hcv hAllM
            refine ⟨hzv, huz, (hEFsJ _).mp hjv, fun w hw => hfire w ((hEFsJ _).mpr hw)⟩
        have hEq12 := conj_at_most_one_via_z0 z0 FsJ hMFsJ s(a1, b1) he1U s(a2, b2) he2U
          (hTrace1 _ he1U) (hTrace1 _ he2U)
        exact hne12 hEq12
      · have hR2 : (orN G C \ lam G C).card = 2 := by omega
        obtain ⟨m1, m2, hm12lt, hRpair⟩ : ∃ m1 m2 : ℕ, m1 < m2 ∧ orN G C \ lam G C = {m1, m2} := by
          obtain ⟨p, q, hpq, hpe⟩ := Finset.card_eq_two.mp hR2
          rcases lt_or_gt_of_ne hpq with hlt | hlt
          · exact ⟨p, q, hlt, hpe⟩
          · exact ⟨q, p, hlt, hpe.trans (Finset.pair_comm _ _)⟩
        have hm1 : m1 ∈ orN G C \ lam G C := by rw [hRpair]; exact Finset.mem_insert_self m1 {m2}
        have hm2 : m2 ∈ orN G C \ lam G C := by rw [hRpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self m2)
        have hm2Eq : m2 = mMax := by
          have h1 := hmMaxGe m2 hm2
          have h2 : mMax ∈ ({m1, m2} : Finset ℕ) := hRpair ▸ hmMax
          rcases Finset.mem_insert.mp h2 with heq | heq2
          · omega
          · rw [Finset.mem_singleton.mp heq2]
        subst hm2Eq
        have hUniqM1 : ∀ r ∈ orN G C \ lam G C, r < mMax → r = m1 := by
          intro r hr hlt
          rw [hRpair, Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl
          · rfl
          · omega
        have hmMaxOrNe' := hmMaxOrNe
        obtain ⟨z2, hz2⟩ := hmMaxOrNe'
        have hm1Data := (orN_mem C m1).mp (Finset.mem_sdiff.mp hm1).1
        have hM1Sub := hAtMostOneR_eval mMax m1 hm12lt hm1 hUniqM1
        have hRmem : ∀ r ∈ orN G C \ lam G C, m1 = r ∨ mMax = r := by
          intro r hr
          have hmem : r ∈ ({m1, mMax} : Finset ℕ) := hRpair ▸ hr
          rcases Finset.mem_insert.mp hmem with rfl | h2'
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_singleton.mp h2').symm
        have hViaMmaxTwoDisj : ∀ (b2 : Fin 2) (G0 G1 : Finset (Finset (Fin n))),
            (∀ S ∈ G0, MonoSet S) → (∀ S ∈ G1, MonoSet S) →
            (∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C mMax b2) = true ↔
              setsEval G0 x ∨ setsEval G1 x) →
            (∀ t ∈ tops G C, ∀ q : Fin 2, ∀ j ∈ junk G C, OrReaches n C (opnd C t q) j →
              OrReaches n C (opnd C t q) mMax ∧ OrReaches n C (opnd C mMax b2) j) →
            False := by
          intro b2 G0 G1 hMG0 hMG1 hEqB2 hAllVia
          have hTraceAll : ∀ e ∈ Ustar G C, ∀ u v : Fin n, col u = col z2 → col v = !(col z2) → e = s(u, v) →
              G.Adj z2 v ∧ u ≠ z2 ∧ (setsEval G0 (pairInput u v) ∨ setsEval G1 (pairInput u v)) ∧
                ∀ w : Fin n, (setsEval G0 (pairInput w v) ∨ setsEval G1 (pairInput w v)) → G.Adj w v := by
            intro e he u v hcu hcv rfl
            obtain ⟨t, ht, htv, d, j, hj, hrj, hjv⟩ := residualTrace he
            obtain ⟨htlen, htop, htb⟩ := topData ht
            obtain ⟨hrm, hrb2⟩ := hAllVia t ht d j hj hrj
            have hz2_side : z2 ∈ side (n := n) C t d := by rw [side_def]; exact orIn_mono hrm hz2
            have hOtherVal := (andValOperands htlen htop _).mp htv (1 - d)
            have hv_side : v ∈ side (n := n) C t (1 - d) := by
              rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', _⟩
              · subst x
                have hadjz2u : G.Adj z2 u := by
                  fin_cases d
                  · exact topAdj ht hz2_side hxs
                  · exact (topAdj ht hxs hz2_side).symm
                exact False.elim (hbip z2 u hadjz2u hcu.symm)
              · subst x; exact hxs
              · exfalso
                obtain ⟨hrm', _⟩ := hAllVia t ht (1 - d) j' hj' hr'
                apply hmMaxData.2.2
                intro x hx
                have h1 := orStep_up List.length_ofFn (orReaches_reach mMax _ hrm).1 hx
                have h2 := orStep_up List.length_ofFn (orReaches_reach mMax _ hrm').1 hx
                exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                  fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2))
            have hadjz2v : G.Adj z2 v := by
              fin_cases d
              · exact topAdj ht hz2_side hv_side
              · exact (topAdj ht hv_side hz2_side).symm
            have huz2 : u ≠ z2 := by
              intro heq
              subst u
              have hstar : s(z2, v) ∈ starEdges G C := by
                rw [starEdges_def]
                refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
                fin_cases d
                · exact Finset.mem_image.mpr ⟨(z2, v), Finset.mem_product.mpr ⟨hz2_side, hv_side⟩, rfl⟩
                · exact Finset.mem_image.mpr ⟨(v, z2), Finset.mem_product.mpr ⟨hv_side, hz2_side⟩, Sym2.eq_swap⟩
              rw [Ustar_def] at he
              exact (Finset.mem_sdiff.mp he).2 hstar
            have hb2uv : val C (List.ofFn (pairInput u v)) (opnd C mMax b2) = true :=
              orStep_up List.length_ofFn (orReaches_reach j _ hrb2).1 (gateVal_eq_val C j (pairInput u v) ▸ hjv)
            refine ⟨hadjz2v, huz2, (hEqB2 _).mp hb2uv, fun w hw => ?_⟩
            have hb2wv : val C (List.ofFn (pairInput w v)) (opnd C mMax b2) = true := (hEqB2 _).mpr hw
            have hmMaxwv : val C (List.ofFn (pairInput w v)) (n + mMax) = true :=
              (val_or List.length_ofFn hmMaxData.1 hmMaxData.2.1).mpr
                ⟨opnd C mMax b2, opndMem hmMaxData.1 b2, opndBound hmMaxData.1 b2, hb2wv⟩
            have h1 := orStep_up List.length_ofFn (orReaches_reach mMax _ hrm).1 hmMaxwv
            have h2 := sideVal hv_side (pairInput_right w v)
            exact (graphFun_pair w v).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
              fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
          let U0 := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → setsEval G0 (pairInput u v))
          let U1 := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → setsEval G1 (pairInput u v))
          have hSub : Ustar G C ⊆ U0 ∪ U1 := by
            intro e he
            obtain ⟨u, v, heq, hcu, hcv, _⟩ := orient_edge (col z2) he
            obtain ⟨_, _, h01, _⟩ := hTraceAll e he u v hcu hcv heq
            rcases h01 with h0 | h1
            · apply Finset.mem_union_left
              refine Finset.mem_filter.mpr ⟨he, fun u' v' heq' => ?_⟩
              have hpe : pairInput u' v' = pairInput u v := by
                rcases Sym2.eq_iff.mp (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact pairInput_symm _ _
              rw [hpe]; exact h0
            · apply Finset.mem_union_right
              refine Finset.mem_filter.mpr ⟨he, fun u' v' heq' => ?_⟩
              have hpe : pairInput u' v' = pairInput u v := by
                rcases Sym2.eq_iff.mp (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact pairInput_symm _ _
              rw [hpe]; exact h1
          have hU0le : U0.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
            conj_at_most_one_via_z0 z2 G0 hMG0 e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
              (fun u v hcu hcv heq => by
                obtain ⟨hzv, huz, _, hfire⟩ := hTraceAll e1 (Finset.mem_filter.mp h1).1 u v hcu hcv heq
                exact ⟨hzv, huz, (Finset.mem_filter.mp h1).2 u v heq, fun w hw => hfire w (Or.inl hw)⟩)
              (fun u v hcu hcv heq => by
                obtain ⟨hzv, huz, _, hfire⟩ := hTraceAll e2 (Finset.mem_filter.mp h2).1 u v hcu hcv heq
                exact ⟨hzv, huz, (Finset.mem_filter.mp h2).2 u v heq, fun w hw => hfire w (Or.inl hw)⟩))
          have hU1le : U1.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
            conj_at_most_one_via_z0 z2 G1 hMG1 e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
              (fun u v hcu hcv heq => by
                obtain ⟨hzv, huz, _, hfire⟩ := hTraceAll e1 (Finset.mem_filter.mp h1).1 u v hcu hcv heq
                exact ⟨hzv, huz, (Finset.mem_filter.mp h1).2 u v heq, fun w hw => hfire w (Or.inr hw)⟩)
              (fun u v hcu hcv heq => by
                obtain ⟨hzv, huz, _, hfire⟩ := hTraceAll e2 (Finset.mem_filter.mp h2).1 u v hcu hcv heq
                exact ⟨hzv, huz, (Finset.mem_filter.mp h2).2 u v heq, fun w hw => hfire w (Or.inr hw)⟩))
          have hUle2 := hCard_union_two U0 U1 hSub hU0le hU1le
          omega
        have hOpndMmaxDirty : ∀ b2 : Fin 2, orIn n C (opnd C mMax b2) = ∅ →
            opnd C mMax b2 < n ∨ ∃ g, opnd C mMax b2 = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g := by
          intro b2 hb2e
          right
          have hge : n ≤ opnd C mMax b2 := by
            by_contra hlt
            have hm : ⟨opnd C mMax b2, by omega⟩ ∈ orIn n C (opnd C mMax b2) :=
              reach_mem_orIn ⟨opnd C mMax b2, by omega⟩ Relation.ReflTransGen.refl
            rw [hb2e] at hm; exact Finset.notMem_empty _ hm
          have hblt := opndBound hmMaxData.1 b2
          refine ⟨opnd C mMax b2 - n, by omega, by omega, ?_⟩
          intro hbg
          have hcone : InCone n C (opnd C mMax b2 - n) mMax :=
            (inCone_iff _ mMax).mpr ⟨hmMaxData.1, opnd C mMax b2 - n, by omega, by
              have he : n + (opnd C mMax b2 - n) = opnd C mMax b2 := by omega
              rw [he]; exact opndMem hmMaxData.1 b2, Or.inl rfl⟩
          exact not_belowF_inCone_dirty (by omega) hbg hmMaxData.1 hmMaxData.2.2 hcone
        by_cases hm1Emp : orIn n C (n + m1) = ∅
        · have hM1ToMmax : ∀ t ∈ tops G C, ∀ q : Fin 2,
              Relation.ReflTransGen OrStep (opnd C t q) (n + m1) →
              Relation.ReflTransGen OrStep (opnd C t q) (n + mMax) ∧
                n + m1 ∈ (gateAt C mMax).inputs := by
            intro t ht q htr1
            have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
            rcases lastOrBefore htr1 with heq | ⟨r2, hr2len, hr2op, hr2in, hr2b, htr2⟩
            · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact hm1Emp)))
            · have hr2nb : ¬ BelowF G C r2 := by
                intro hrb
                apply hm1Data.2.2
                intro x hx
                exact hrb x ((val_or List.length_ofFn hr2len hr2op).mpr ⟨n + m1, hr2in, hr2b, hx⟩)
              have hr2R : r2 ∈ orN G C \ lam G C := by
                refine Finset.mem_sdiff.mpr ⟨(orN_mem C r2).mpr ⟨hr2len, hr2op, hr2nb⟩, ?_⟩
                intro hr2l
                obtain ⟨_, h0, h1, _⟩ := (lam_mem C r2).mp hr2l
                obtain ⟨b, hb⟩ := inputsAsOpnd hr2len hr2in
                have hne : (orIn n C (opnd C r2 b)).Nonempty := by fin_cases b; exact h0; exact h1
                rw [← hb, hm1Emp] at hne
                exact Finset.not_nonempty_empty hne
              rcases hRmem r2 hr2R with rfl | rfl
              · omega
              · exact ⟨htr2, hr2in⟩
          have hExB2 : ∃ b2 : Fin 2, orIn n C (opnd C mMax b2) = ∅ ∧
              (orIn n C (opnd C mMax (1 - b2))).Nonempty := by
            obtain ⟨t, ht, _, d, j, hj, hrj, _⟩ := residualTrace he1U
            have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
            have hHasEmpIn : ∃ b2 : Fin 2, orIn n C (opnd C mMax b2) = ∅ := by
              rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
              · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
              · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
                · obtain ⟨_, hm1in⟩ := hM1ToMmax t ht d htr
                  obtain ⟨b2, hb2⟩ := inputsAsOpnd hmMaxData.1 hm1in
                  exact ⟨b2, by rw [← hb2]; exact hm1Emp⟩
                · obtain ⟨b2, hb2⟩ := inputsAsOpnd hmMaxData.1 hrin
                  exact ⟨b2, by rw [← hb2]; exact andRawEmpty (junkData hj).2.1⟩
            obtain ⟨b2, hb2e⟩ := hHasEmpIn
            have hb2ne : (orIn n C (opnd C mMax (1 - b2))).Nonempty := by
              by_contra h1e
              have htot := orEmpty (r := mMax) (fun w hw => by
                obtain ⟨b', rfl⟩ := inputsAsOpnd hmMaxData.1 hw
                fin_cases b2 <;> fin_cases b' <;> first | exact hb2e | exact Finset.not_nonempty_iff_eq_empty.mp h1e)
              rw [htot] at hmMaxOrNe
              exact Finset.not_nonempty_empty hmMaxOrNe
            exact ⟨b2, hb2e, hb2ne⟩
          obtain ⟨b2, hb2e, hb2ne⟩ := hExB2
          obtain ⟨Fs0, Fs1, hM0, hM1, _, hEv⟩ := hM1Sub.1 hm1Emp
          have hG01 : ∃ G0 G1 : Finset (Finset (Fin n)), (∀ S ∈ G0, MonoSet S) ∧ (∀ S ∈ G1, MonoSet S) ∧
              ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C mMax b2) = true ↔ setsEval G0 x ∨ setsEval G1 x := by
            rcases hEv (opnd C mMax b2) (opndBound hmMaxData.1 b2) (hOpndMmaxDirty b2 hb2e) with
              ⟨Fs, hMFs, hEFs⟩ | ⟨Fs, hMFs, hEFs⟩
            · exact ⟨Fs, Fs, hMFs, hMFs, fun x => by rw [hEFs, or_self]⟩
            · refine ⟨Fs ∪ Fs0, Fs ∪ Fs1,
                fun S hS => (Finset.mem_union.mp hS).elim (hMFs S) (hM0 S),
                fun S hS => (Finset.mem_union.mp hS).elim (hMFs S) (hM1 S), fun x => ?_⟩
              rw [hEFs, setsEval_union, setsEval_union]
              exact ⟨fun h => h.2.elim (fun b => Or.inl ⟨h.1, b⟩) (fun c => Or.inr ⟨h.1, c⟩),
                fun h => h.elim (fun h1 => ⟨h1.1, Or.inl h1.2⟩) (fun h1 => ⟨h1.1, Or.inr h1.2⟩)⟩
          obtain ⟨G0, G1, hMG0, hMG1, hEqB2⟩ := hG01
          refine hViaMmaxTwoDisj b2 G0 G1 hMG0 hMG1 hEqB2 (fun t ht q j hj hrj => ?_)
          have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
          rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
          · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
          · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
            · obtain ⟨htrM, hm1in⟩ := hM1ToMmax t ht q htr
              obtain ⟨b', hb'⟩ := inputsAsOpnd hmMaxData.1 hm1in
              have hbeq : b' = b2 := by
                by_contra hne
                have hb1 : b' = 1 - b2 := by fin_cases b2 <;> fin_cases b' <;> first | rfl | exact False.elim (hne rfl)
                subst b'
                rw [← hb', hm1Emp] at hb2ne
                exact Finset.not_nonempty_empty hb2ne
              subst b'
              refine ⟨reach_orReaches htrM mMax rfl hmMaxData.1, ?_⟩
              rw [← hb']
              exact reach_orReaches (Relation.ReflTransGen.head ⟨m1, hm1Data.1, rfl, hm1Data.2.1, hrin, hrb⟩
                Relation.ReflTransGen.refl) j rfl (junkData hj).1
            · obtain ⟨b', hb'⟩ := inputsAsOpnd hmMaxData.1 hrin
              have hbeq : b' = b2 := by
                by_contra hne
                have hb1 : b' = 1 - b2 := by fin_cases b2 <;> fin_cases b' <;> first | rfl | exact False.elim (hne rfl)
                subst b'
                rw [← hb', andRawEmpty (junkData hj).2.1] at hb2ne
                exact Finset.not_nonempty_empty hb2ne
              subst b'
              refine ⟨reach_orReaches htr mMax rfl hmMaxData.1, ?_⟩
              rw [← hb']
              exact reach_orReaches Relation.ReflTransGen.refl j rfl (junkData hj).1
        · have hm1Ne : (orIn n C (n + m1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hm1Emp
          by_cases hm1Both : (orIn n C (opnd C m1 0)).Nonempty ∧ (orIn n C (opnd C m1 1)).Nonempty
          · have hNoJunkInM1 : ∀ j ∈ junk G C, n + j ∉ (gateAt C m1).inputs := by
              intro j hj hjm
              obtain ⟨b, hb⟩ := inputsAsOpnd hm1Data.1 hjm
              have hne : (orIn n C (opnd C m1 b)).Nonempty := by fin_cases b; exact hm1Both.1; exact hm1Both.2
              rw [← hb, andRawEmpty (junkData hj).2.1] at hne
              exact Finset.not_nonempty_empty hne
            have hExB2 : ∃ b2 : Fin 2, orIn n C (opnd C mMax b2) = ∅ ∧
                (orIn n C (opnd C mMax (1 - b2))).Nonempty := by
              obtain ⟨t, ht, _, d, j, hj, hrj, _⟩ := residualTrace he1U
              have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
              rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, _⟩
              · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
              · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
                · exact False.elim (hNoJunkInM1 j hj hrin)
                · obtain ⟨b2, hb2⟩ := inputsAsOpnd hmMaxData.1 hrin
                  have hb2e : orIn n C (opnd C mMax b2) = ∅ := by rw [← hb2]; exact andRawEmpty (junkData hj).2.1
                  have hb2ne : (orIn n C (opnd C mMax (1 - b2))).Nonempty := by
                    by_contra h1e
                    have htot := orEmpty (r := mMax) (fun w hw => by
                      obtain ⟨b', rfl⟩ := inputsAsOpnd hmMaxData.1 hw
                      fin_cases b2 <;> fin_cases b' <;> first | exact hb2e | exact Finset.not_nonempty_iff_eq_empty.mp h1e)
                    rw [htot] at hmMaxOrNe
                    exact Finset.not_nonempty_empty hmMaxOrNe
                  exact ⟨b2, hb2e, hb2ne⟩
            obtain ⟨b2, hb2e, hb2ne⟩ := hExB2
            obtain ⟨Fs0, Fs1, hM0, hM1, _, hEv⟩ := hM1Sub.2.1 hm1Both.1 hm1Both.2
            have hG01 : ∃ G0 G1 : Finset (Finset (Fin n)), (∀ S ∈ G0, MonoSet S) ∧ (∀ S ∈ G1, MonoSet S) ∧
                ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C mMax b2) = true ↔ setsEval G0 x ∨ setsEval G1 x := by
              rcases hEv (opnd C mMax b2) (opndBound hmMaxData.1 b2) (hOpndMmaxDirty b2 hb2e) with
                ⟨Fs, hMFs, hEFs⟩ | ⟨Fs, hMFs, hEFs⟩
              · exact ⟨Fs, Fs, hMFs, hMFs, fun x => by rw [hEFs, or_self]⟩
              · refine ⟨Fs ∪ Fs0, Fs ∪ Fs1,
                  fun S hS => (Finset.mem_union.mp hS).elim (hMFs S) (hM0 S),
                  fun S hS => (Finset.mem_union.mp hS).elim (hMFs S) (hM1 S), fun x => ?_⟩
                rw [hEFs, setsEval_union, setsEval_union]
                exact ⟨fun h => h.2.elim (fun b => Or.inl ⟨h.1, b⟩) (fun c => Or.inr ⟨h.1, c⟩),
                  fun h => h.elim (fun h1 => ⟨h1.1, Or.inl h1.2⟩) (fun h1 => ⟨h1.1, Or.inr h1.2⟩)⟩
            obtain ⟨G0, G1, hMG0, hMG1, hEqB2⟩ := hG01
            refine hViaMmaxTwoDisj b2 G0 G1 hMG0 hMG1 hEqB2 (fun t ht q j hj hrj => ?_)
            have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
            rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
            · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
            · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
              · exact False.elim (hNoJunkInM1 j hj hrin)
              · obtain ⟨b', hb'⟩ := inputsAsOpnd hmMaxData.1 hrin
                have hbeq : b' = b2 := by
                  by_contra hne
                  have hb1 : b' = 1 - b2 := by fin_cases b2 <;> fin_cases b' <;> first | rfl | exact False.elim (hne rfl)
                  subst b'
                  rw [← hb', andRawEmpty (junkData hj).2.1] at hb2ne
                  exact Finset.not_nonempty_empty hb2ne
                subst b'
                refine ⟨reach_orReaches htr mMax rfl hmMaxData.1, ?_⟩
                rw [← hb']
                exact reach_orReaches Relation.ReflTransGen.refl j rfl (junkData hj).1
          · have hM1Mixed : ∃ d0 : Fin 2, orIn n C (opnd C m1 d0) = ∅ ∧ (orIn n C (opnd C m1 (1 - d0))).Nonempty := by
              by_cases h0 : (orIn n C (opnd C m1 0)).Nonempty
              · have h1 : ¬ (orIn n C (opnd C m1 1)).Nonempty := fun h => hm1Both ⟨h0, h⟩
                exact ⟨1, Finset.not_nonempty_iff_eq_empty.mp h1, h0⟩
              · by_cases h1 : (orIn n C (opnd C m1 1)).Nonempty
                · exact ⟨0, Finset.not_nonempty_iff_eq_empty.mp h0, h1⟩
                · have htot := orEmpty (r := m1) (fun w hw => by
                    obtain ⟨b, rfl⟩ := inputsAsOpnd hm1Data.1 hw
                    fin_cases b
                    · exact Finset.not_nonempty_iff_eq_empty.mp h0
                    · exact Finset.not_nonempty_iff_eq_empty.mp h1)
                  rw [htot] at hm1Ne
                  exact False.elim (Finset.not_nonempty_empty hm1Ne)
            obtain ⟨d0, hd0e, hd1ne⟩ := hM1Mixed
            obtain ⟨j1, _, hj1mem, hj1op, ⟨FsJ1, hMFsJ1, hEFsJ1⟩, _, hEvalBelow⟩ := hM1Sub.2.2 d0 hd0e hd1ne
            have hm1Ne' := hm1Ne
            obtain ⟨z1, hz1⟩ := hm1Ne'
            have hUniqJ1 : ∀ j ∈ junk G C, n + j ∈ (gateAt C m1).inputs → j = j1 := by
              intro j hj hjm
              obtain ⟨b, hb⟩ := inputsAsOpnd hm1Data.1 hjm
              by_cases hbd : b = d0
              · subst b
                have : n + j = n + j1 := hb.trans hj1op
                omega
              · have hb1 : b = 1 - d0 := by fin_cases d0 <;> fin_cases b <;> first | rfl | exact False.elim (hbd rfl)
                subst b
                rw [← hb, andRawEmpty (junkData hj).2.1] at hd1ne
                exact False.elim (Finset.not_nonempty_empty hd1ne)
            by_cases hmMaxBoth : (orIn n C (opnd C mMax 0)).Nonempty ∧ (orIn n C (opnd C mMax 1)).Nonempty
            · have hNoJunkInMmax : ∀ j ∈ junk G C, n + j ∉ (gateAt C mMax).inputs := by
                intro j hj hjm
                obtain ⟨b, hb⟩ := inputsAsOpnd hmMaxData.1 hjm
                have hne : (orIn n C (opnd C mMax b)).Nonempty := by fin_cases b; exact hmMaxBoth.1; exact hmMaxBoth.2
                rw [← hb, andRawEmpty (junkData hj).2.1] at hne
                exact Finset.not_nonempty_empty hne
              have hTraceM1 : ∀ e ∈ Ustar G C, ∀ u v : Fin n, col u = col z1 → col v = !(col z1) → e = s(u, v) →
                  G.Adj z1 v ∧ u ≠ z1 ∧ setsEval FsJ1 (pairInput u v) ∧
                    ∀ w : Fin n, setsEval FsJ1 (pairInput w v) → G.Adj w v := by
                intro e he u v hcu hcv rfl
                obtain ⟨t, ht, htv, d, j, hj, hrj, hjv⟩ := residualTrace he
                obtain ⟨htlen, htop, htb⟩ := topData ht
                have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
                rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
                · exact False.elim (htnc (emptySide ht (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
                · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
                  · have hjeq := hUniqJ1 j hj hrin
                    subst j
                    have hrm1 := reach_orReaches htr m1 rfl hm1Data.1
                    have hz1_side : z1 ∈ side (n := n) C t d := by rw [side_def]; exact orIn_mono hrm1 hz1
                    have hOtherVal := (andValOperands htlen htop _).mp htv (1 - d)
                    have hv_side : v ∈ side (n := n) C t (1 - d) := by
                      rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', _⟩
                      · subst x
                        have hadjz1u : G.Adj z1 u := by
                          fin_cases d
                          · exact topAdj ht hz1_side hxs
                          · exact (topAdj ht hxs hz1_side).symm
                        exact False.elim (hbip z1 u hadjz1u hcu.symm)
                      · subst x; exact hxs
                      · exfalso
                        rcases lastOrBefore (orReaches_reach j' _ hr').1 with heq' | ⟨r', hr'len, hr'op, hr'in, hr'b, htr'⟩
                        · exact htnc (emptySide ht (by rw [side_def, heq']; exact andRawEmpty (junkData hj').2.1))
                        · rcases hRmem r' (lastOrOutside hj' hr'len hr'op hr'in hr'b) with rfl | rfl
                          · apply hm1Data.2.2
                            intro x hx
                            have h1 := orStep_up List.length_ofFn htr hx
                            have h2 := orStep_up List.length_ofFn htr' hx
                            exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                              fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2))
                          · exact hNoJunkInMmax j' hj' hr'in
                    have hadjz1v : G.Adj z1 v := by
                      fin_cases d
                      · exact topAdj ht hz1_side hv_side
                      · exact (topAdj ht hv_side hz1_side).symm
                    have huz1 : u ≠ z1 := by
                      intro heq
                      subst u
                      have hstar : s(z1, v) ∈ starEdges G C := by
                        rw [starEdges_def]
                        refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
                        fin_cases d
                        · exact Finset.mem_image.mpr ⟨(z1, v), Finset.mem_product.mpr ⟨hz1_side, hv_side⟩, rfl⟩
                        · exact Finset.mem_image.mpr ⟨(v, z1), Finset.mem_product.mpr ⟨hv_side, hz1_side⟩, Sym2.eq_swap⟩
                      rw [Ustar_def] at he
                      exact (Finset.mem_sdiff.mp he).2 hstar
                    refine ⟨hadjz1v, huz1, (hEFsJ1 _).mp hjv, fun w hw => ?_⟩
                    have h1 := orStep_up List.length_ofFn (orReaches_reach j1 _ hrj).1
                      (gateVal_eq_val C j1 (pairInput w v) ▸ (hEFsJ1 _).mpr hw)
                    have h2 := sideVal hv_side (pairInput_right w v)
                    exact (graphFun_pair w v).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
                      fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
                  · exact False.elim (hNoJunkInMmax j hj hrin)
              exact hne12 (conj_at_most_one_via_z0 z1 FsJ1 hMFsJ1 s(a1, b1) he1U s(a2, b2) he2U
                (hTraceM1 _ he1U) (hTraceM1 _ he2U))
            · have hmMaxMixed : ∃ b2 : Fin 2, orIn n C (opnd C mMax b2) = ∅ ∧ (orIn n C (opnd C mMax (1 - b2))).Nonempty := by
                by_cases h0 : (orIn n C (opnd C mMax 0)).Nonempty
                · have h1 : ¬ (orIn n C (opnd C mMax 1)).Nonempty := fun h => hmMaxBoth ⟨h0, h⟩
                  exact ⟨1, Finset.not_nonempty_iff_eq_empty.mp h1, h0⟩
                · by_cases h1 : (orIn n C (opnd C mMax 1)).Nonempty
                  · exact ⟨0, Finset.not_nonempty_iff_eq_empty.mp h0, h1⟩
                  · have htot := orEmpty (r := mMax) (fun w hw => by
                      obtain ⟨b, rfl⟩ := inputsAsOpnd hmMaxData.1 hw
                      fin_cases b
                      · exact Finset.not_nonempty_iff_eq_empty.mp h0
                      · exact Finset.not_nonempty_iff_eq_empty.mp h1)
                    rw [htot] at hmMaxOrNe
                    exact False.elim (Finset.not_nonempty_empty hmMaxOrNe)
              obtain ⟨b2, hb2e, hb2ne⟩ := hmMaxMixed
              have hJ2 : ∃ j2 : ℕ, j2 < mMax ∧ j2 ∈ junk G C ∧ opnd C mMax b2 = n + j2 := by
                have hge : n ≤ opnd C mMax b2 := by
                  by_contra hlt
                  have hm : ⟨opnd C mMax b2, by omega⟩ ∈ orIn n C (opnd C mMax b2) :=
                    reach_mem_orIn ⟨opnd C mMax b2, by omega⟩ Relation.ReflTransGen.refl
                  rw [hb2e] at hm; exact Finset.notMem_empty _ hm
                let j2 := opnd C mMax b2 - n
                have hj2eq : opnd C mMax b2 = n + j2 := by omega
                have hj2lt : j2 < mMax := by have := opndBound hmMaxData.1 b2; omega
                have hj2len : j2 < C.gates.length := by omega
                have hj2nb : ¬ BelowF G C j2 := by
                  intro hbj
                  have hcone : InCone n C j2 mMax :=
                    (inCone_iff j2 mMax).mpr ⟨hmMaxData.1, j2, hj2lt, hj2eq ▸ opndMem hmMaxData.1 b2, Or.inl rfl⟩
                  exact not_belowF_inCone_dirty hj2len hbj hmMaxData.1 hmMaxData.2.2 hcone
                have hj2op : (gateAt C j2).op = GateOp.and := by
                  rcases hLeast.1.1 _ (gateAt_mem hj2len) with hand | hor
                  · exact hand
                  · have hj2N : j2 ∈ orN G C := (orN_mem C j2).mpr ⟨hj2len, hor, hj2nb⟩
                    have hj2notLam : j2 ∉ lam G C := fun hlam => by
                      have hne := or_nonempty_of_lam hlam
                      rw [← hj2eq, hb2e] at hne
                      exact Finset.not_nonempty_empty hne
                    have hj2eqM1 := hUniqM1 j2 (Finset.mem_sdiff.mpr ⟨hj2N, hj2notLam⟩) hj2lt
                    have hm1eq : opnd C mMax b2 = n + m1 := by omega
                    rw [hm1eq] at hb2e
                    exact False.elim (hm1Emp hb2e)
                refine ⟨j2, hj2lt, (junk_mem C j2).mpr ⟨hj2len, hj2op, ?_⟩, hj2eq⟩
                by_contra hnone
                apply hj2nb
                intro x hx
                by_contra hf
                exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
              obtain ⟨j2, hj2lt, hj2mem, hj2op⟩ := hJ2
              have hUniqJ2 : ∀ j ∈ junk G C, n + j ∈ (gateAt C mMax).inputs → j = j2 := by
                intro j hj hjm
                obtain ⟨b, hb⟩ := inputsAsOpnd hmMaxData.1 hjm
                by_cases hbd : b = b2
                · subst b
                  have : n + j = n + j2 := hb.trans hj2op
                  omega
                · have hb1 : b = 1 - b2 := by fin_cases b2 <;> fin_cases b <;> first | rfl | exact False.elim (hbd rfl)
                  subst b
                  rw [← hb, andRawEmpty (junkData hj).2.1] at hb2ne
                  exact False.elim (Finset.not_nonempty_empty hb2ne)
              have hJ2Decomp : ∃ FsA FsB : Finset (Finset (Fin n)), FsB ⊆ FsA ∧ (∀ S ∈ FsA, MonoSet S) ∧
                  ∀ x : Fin n → Bool, gateVal n C j2 x = true ↔
                    setsEval FsA x ∨ (setsEval FsB x ∧ gateVal n C j1 x = true) := by
                rcases hEvalBelow (n + j2) (by omega) (Or.inr ⟨j2, rfl, (junkData hj2mem).1, junkNotBelow hj2mem⟩) with
                  ⟨Fs, hMFs, hEFs⟩ | ⟨FsA, FsB, hBA, hMFsA, hEFs⟩
                · refine ⟨Fs, Fs, Finset.Subset.refl Fs, hMFs, fun x => ?_⟩
                  rw [gateVal_eq_val, hEFs]
                  exact ⟨Or.inl, fun h => h.elim id And.left⟩
                · exact ⟨FsA, FsB, hBA, hMFsA, fun x => by rw [gateVal_eq_val, hEFs]⟩
              obtain ⟨FsA, FsB, hBA, hMFsA, hEqJ2⟩ := hJ2Decomp
              have hMFsB : ∀ S ∈ FsB, MonoSet S := fun S hS => hMFsA S (hBA hS)
              let U1 := (Ustar G C).filter (fun e =>
                ∀ u v : Fin n, col u = col z2 → col v = !(col z2) → e = s(u, v) →
                  G.Adj z2 v ∧ u ≠ z2 ∧ setsEval FsA (pairInput u v) ∧
                    ∀ w : Fin n, setsEval FsA (pairInput w v) → G.Adj w v)
              let U2 := Ustar G C \ U1
              have hSub12 : Ustar G C ⊆ U1 ∪ U2 := by
                intro e he
                by_cases h1 : e ∈ U1
                · exact Finset.mem_union_left _ h1
                · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, h1⟩)
              have hU1le : U1.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
                conj_at_most_one_via_z0 z2 FsA hMFsA e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
                  (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
              have hU2_class : ∀ e ∈ U2, ∀ u v : Fin n, col u = col z2 → col v = !(col z2) → e = s(u, v) →
                  gateVal n C j1 (pairInput u v) = true ∧
                  ((∀ w : Fin n, gateVal n C j1 (pairInput w v) = true → G.Adj w v) ∨
                   (∀ w : Fin n, gateVal n C j1 (pairInput w u) = true → G.Adj w u) ∨
                   (setsEval (FsB ∪ FsJ1) (pairInput u v) ∧
                     ((∀ x : Fin n → Bool, setsEval (FsB ∪ FsJ1) x → graphFun G ∅ x = true) ∨
                      (G.Adj z2 v ∧ u ≠ z2 ∧ ∀ w : Fin n, setsEval (FsB ∪ FsJ1) (pairInput w v) → G.Adj w v)))) := by
                intro e heU2 u v hcu hcv heq
                have heU := (Finset.mem_sdiff.mp heU2).1
                have heNotU1 := (Finset.mem_sdiff.mp heU2).2
                obtain ⟨t, ht, htv, d, j, hj, hrj, hjv⟩ := residualTrace (heq ▸ heU)
                obtain ⟨htlen, htop, htb⟩ := topData ht
                have htnc : t ∉ centreless G C := by rw [hZemp]; exact Finset.notMem_empty _
                have hOtherVal := (andValOperands htlen htop _).mp htv (1 - d)
                have hCross : OrReaches n C (opnd C t d) j1 → OrReaches n C (opnd C t (1 - d)) j2 →
                    gateVal n C j1 (pairInput u v) = true → gateVal n C j2 (pairInput u v) = true →
                    setsEval (FsB ∪ FsJ1) (pairInput u v) ∧
                      ∀ x : Fin n → Bool, setsEval (FsB ∪ FsJ1) x → graphFun G ∅ x = true := by
                  intro h1r h2r h1v h2v
                  have hBuv : setsEval FsB (pairInput u v) := by
                    rcases (hEqJ2 _).mp h2v with hA | ⟨hB, _⟩
                    · exact setsEval_mono_sub hBA hA
                    · exact hB
                  refine ⟨(setsEval_union FsB FsJ1 _).mpr ⟨hBuv, (hEFsJ1 _).mp h1v⟩, fun x hx => ?_⟩
                  obtain ⟨hBx, hJx⟩ := (setsEval_union FsB FsJ1 x).mp hx
                  have hj1x : gateVal n C j1 x = true := (hEFsJ1 x).mpr hJx
                  have hj2x : gateVal n C j2 x = true := (hEqJ2 x).mpr (Or.inr ⟨hBx, hj1x⟩)
                  have ha := orStep_up List.length_ofFn (orReaches_reach j1 _ h1r).1 (gateVal_eq_val C j1 x ▸ hj1x)
                  have hb := orStep_up List.length_ofFn (orReaches_reach j2 _ h2r).1 (gateVal_eq_val C j2 x ▸ hj2x)
                  exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                    fin_cases d <;> fin_cases q <;> first | exact ha | exact hb))
                have hCrossRev : OrReaches n C (opnd C t d) j2 → OrReaches n C (opnd C t (1 - d)) j1 →
                    gateVal n C j1 (pairInput u v) = true → gateVal n C j2 (pairInput u v) = true →
                    setsEval (FsB ∪ FsJ1) (pairInput u v) ∧
                      ∀ x : Fin n → Bool, setsEval (FsB ∪ FsJ1) x → graphFun G ∅ x = true := by
                  intro h2r h1r h1v h2v
                  have hBuv : setsEval FsB (pairInput u v) := by
                    rcases (hEqJ2 _).mp h2v with hA | ⟨hB, _⟩
                    · exact setsEval_mono_sub hBA hA
                    · exact hB
                  refine ⟨(setsEval_union FsB FsJ1 _).mpr ⟨hBuv, (hEFsJ1 _).mp h1v⟩, fun x hx => ?_⟩
                  obtain ⟨hBx, hJx⟩ := (setsEval_union FsB FsJ1 x).mp hx
                  have hj1x : gateVal n C j1 x = true := (hEFsJ1 x).mpr hJx
                  have hj2x : gateVal n C j2 x = true := (hEqJ2 x).mpr (Or.inr ⟨hBx, hj1x⟩)
                  have ha := orStep_up List.length_ofFn (orReaches_reach j2 _ h2r).1 (gateVal_eq_val C j2 x ▸ hj2x)
                  have hb := orStep_up List.length_ofFn (orReaches_reach j1 _ h1r).1 (gateVal_eq_val C j1 x ▸ hj1x)
                  exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                    fin_cases d <;> fin_cases q <;> first | exact ha | exact hb))
                rcases lastOrBefore (orReaches_reach j _ hrj).1 with heq' | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
                · exact False.elim (htnc (emptySide ht (by rw [side_def, heq']; exact andRawEmpty (junkData hj).2.1)))
                · rcases hRmem r (lastOrOutside hj hrlen hrop hrin hrb) with rfl | rfl
                  · have hjeq := hUniqJ1 j hj hrin
                    subst j
                    refine ⟨hjv, ?_⟩
                    rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', hj'v⟩
                    · right; left
                      rw [hxu] at hxs
                      intro w hjw
                      have h1 := orStep_up List.length_ofFn (orReaches_reach j1 _ hrj).1 (gateVal_eq_val C j1 _ ▸ hjw)
                      have h2 := sideVal hxs (pairInput_right w u)
                      exact (graphFun_pair w u).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
                        fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
                    · left
                      rw [hxv] at hxs
                      intro w hjw
                      have h1 := orStep_up List.length_ofFn (orReaches_reach j1 _ hrj).1 (gateVal_eq_val C j1 _ ▸ hjw)
                      have h2 := sideVal hxs (pairInput_right w v)
                      exact (graphFun_pair w v).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
                        fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
                    · rcases lastOrBefore (orReaches_reach j' _ hr').1 with heq2 | ⟨r', hr'len, hr'op, hr'in, hr'b, htr'⟩
                      · exact False.elim (htnc (emptySide ht (by rw [side_def, heq2]; exact andRawEmpty (junkData hj').2.1)))
                      · rcases hRmem r' (lastOrOutside hj' hr'len hr'op hr'in hr'b) with rfl | rfl
                        · exfalso
                          apply hm1Data.2.2
                          intro x hx
                          have h1 := orStep_up List.length_ofFn htr hx
                          have h2 := orStep_up List.length_ofFn htr' hx
                          exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                            fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2))
                        · have hj'eq := hUniqJ2 j' hj' hr'in
                          subst j'
                          obtain ⟨hBJ, hBel⟩ := hCross hrj hr' hjv hj'v
                          exact Or.inr (Or.inr ⟨hBJ, Or.inl hBel⟩)
                  · have hjeq := hUniqJ2 j hj hrin
                    subst j
                    have hrm2 := reach_orReaches htr mMax rfl hmMaxData.1
                    have hz2_side : z2 ∈ side (n := n) C t d := by rw [side_def]; exact orIn_mono hrm2 hz2
                    rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', hj'v⟩
                    · subst x
                      have hadjz2u : G.Adj z2 u := by
                        fin_cases d
                        · exact topAdj ht hz2_side hxs
                        · exact (topAdj ht hxs hz2_side).symm
                      exact False.elim (hbip z2 u hadjz2u hcu.symm)
                    · subst x
                      have hadjz2v : G.Adj z2 v := by
                        fin_cases d
                        · exact topAdj ht hz2_side hxs
                        · exact (topAdj ht hxs hz2_side).symm
                      have huz2 : u ≠ z2 := by
                        intro hu_eq
                        subst u
                        have hstar : s(z2, v) ∈ starEdges G C := by
                          rw [starEdges_def]
                          refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
                          fin_cases d
                          · exact Finset.mem_image.mpr ⟨(z2, v), Finset.mem_product.mpr ⟨hz2_side, hxs⟩, rfl⟩
                          · exact Finset.mem_image.mpr ⟨(v, z2), Finset.mem_product.mpr ⟨hxs, hz2_side⟩, Sym2.eq_swap⟩
                        rw [heq, Ustar_def] at heU
                        exact (Finset.mem_sdiff.mp heU).2 hstar
                      have hfireJ2 : ∀ w : Fin n, gateVal n C j2 (pairInput w v) = true → G.Adj w v := by
                        intro w hjw
                        have h1 := orStep_up List.length_ofFn (orReaches_reach j2 _ hrj).1 (gateVal_eq_val C j2 _ ▸ hjw)
                        have h2 := sideVal hxs (pairInput_right w v)
                        exact (graphFun_pair w v).mp (htb _ ((andValOperands htlen htop _).mpr (fun q => by
                          fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)))
                      rcases (hEqJ2 _).mp hjv with hAuv | ⟨hBuv, hj1uv⟩
                      · exfalso
                        apply heNotU1
                        refine Finset.mem_filter.mpr ⟨heU, fun u' v' hcu' hcv' heq' => ?_⟩
                        rcases Sym2.eq_iff.mp (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact ⟨hadjz2v, huz2, hAuv, fun w hw => hfireJ2 w ((hEqJ2 _).mpr (Or.inl hw))⟩
                        · exfalso
                          have hcon : col z2 = !(col z2) := hcu.symm.trans hcv'
                          cases hz2c : col z2 <;> rw [hz2c] at hcon <;> exact Bool.noConfusion hcon
                      · refine ⟨hj1uv, Or.inr (Or.inr ⟨(setsEval_union FsB FsJ1 _).mpr ⟨hBuv, (hEFsJ1 _).mp hj1uv⟩,
                          Or.inr ⟨hadjz2v, huz2, fun w hw => hfireJ2 w ((hEqJ2 _).mpr (Or.inr
                            ⟨((setsEval_union FsB FsJ1 _).mp hw).1, (hEFsJ1 _).mpr ((setsEval_union FsB FsJ1 _).mp hw).2⟩))⟩⟩)⟩
                    · rcases lastOrBefore (orReaches_reach j' _ hr').1 with heq2 | ⟨r', hr'len, hr'op, hr'in, hr'b, htr'⟩
                      · exact False.elim (htnc (emptySide ht (by rw [side_def, heq2]; exact andRawEmpty (junkData hj').2.1)))
                      · rcases hRmem r' (lastOrOutside hj' hr'len hr'op hr'in hr'b) with rfl | rfl
                        · have hj'eq := hUniqJ1 j' hj' hr'in
                          subst j'
                          obtain ⟨hBJ, hBel⟩ := hCrossRev hrj hr' hj'v hjv
                          exact ⟨hj'v, Or.inr (Or.inr ⟨hBJ, Or.inl hBel⟩)⟩
                        · exfalso
                          apply hmMaxData.2.2
                          intro x hx
                          have h1 := orStep_up List.length_ofFn htr hx
                          have h2 := orStep_up List.length_ofFn htr' hx
                          exact htb x ((andValOperands htlen htop x).mpr (fun q => by
                            fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2))
              have hU2le : U2.card ≤ 1 := by
                by_cases hHasCleanJ1 : ∃ e0 ∈ U2, ∃ u0 v0 : Fin n, e0 = s(u0, v0) ∧
                    (∀ w : Fin n, gateVal n C j1 (pairInput w v0) = true → G.Adj w v0)
                · obtain ⟨e0, he0U2, u0, v0, he0eq, hfire0⟩ := hHasCleanJ1
                  have he0U := (Finset.mem_sdiff.mp he0U2).1
                  obtain ⟨u0', v0', h0eq, hu0'c, hv0'c, _⟩ := orient_edge (col z2) he0U
                  have hj1_0' := (hU2_class e0 he0U2 u0' v0' hu0'c hv0'c h0eq).1
                  have hj1_0 : gateVal n C j1 (pairInput u0 v0) = true := by
                    have hpe : pairInput u0 v0 = pairInput u0' v0' := by
                      rcases Sym2.eq_iff.mp (h0eq.symm.trans he0eq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · rfl
                      · exact pairInput_symm _ _
                    rw [hpe]; exact hj1_0'
                  refine Finset.card_le_one.mpr (fun e1 h1 e2 h2 => ?_)
                  have hEq0 : ∀ e ∈ U2, e = e0 := by
                    intro e he
                    by_contra hne
                    have heU := (Finset.mem_sdiff.mp he).1
                    obtain ⟨u, v, heq, hcu, hcv, _⟩ := orient_edge (col z2) heU
                    have hj1v := (hU2_class e he u v hcu hcv heq).1
                    exact pure_junk_at_most_one_Ustar j1 FsJ1 hj1mem hMFsJ1 hEFsJ1 u0 v0 (he0eq ▸ he0U) hfire0 hj1_0
                      u v (heq ▸ heU) (fun h => hne (heq.trans (h.symm.trans he0eq.symm))) hj1v
                  exact (hEq0 e1 h1).trans (hEq0 e2 h2).symm
                · have hU2_BJ : ∀ e ∈ U2, ∀ u v : Fin n, col u = col z2 → col v = !(col z2) → e = s(u, v) →
                      setsEval (FsB ∪ FsJ1) (pairInput u v) ∧
                      ((∀ x : Fin n → Bool, setsEval (FsB ∪ FsJ1) x → graphFun G ∅ x = true) ∨
                       (G.Adj z2 v ∧ u ≠ z2 ∧ ∀ w : Fin n, setsEval (FsB ∪ FsJ1) (pairInput w v) → G.Adj w v)) := by
                    intro e he u v hcu hcv heq
                    obtain ⟨_, h1 | h2 | h3⟩ := hU2_class e he u v hcu hcv heq
                    · exact False.elim (hHasCleanJ1 ⟨e, he, u, v, heq, h1⟩)
                    · exact False.elim (hHasCleanJ1 ⟨e, he, v, u, heq.trans Sym2.eq_swap, h2⟩)
                    · exact h3
                  have hMBJ : ∀ S ∈ FsB ∪ FsJ1, MonoSet S := fun S hS =>
                    (Finset.mem_union.mp hS).elim (hMFsB S) (hMFsJ1 S)
                  by_cases hHasBel : ∀ x : Fin n → Bool, setsEval (FsB ∪ FsJ1) x → graphFun G ∅ x = true
                  · refine Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
                      conj_at_most_one_centreless (FsB ∪ FsJ1) hMBJ hHasBel
                        e1 (Finset.mem_sdiff.mp h1).1 e2 (Finset.mem_sdiff.mp h2).1 ?_ ?_)
                    · intro u v heq
                      obtain ⟨u', v', heq', hcu', hcv', _⟩ := orient_edge (col z2) (Finset.mem_sdiff.mp h1).1
                      have hpe : pairInput u v = pairInput u' v' := by
                        rcases Sym2.eq_iff.mp (heq'.symm.trans heq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · rfl
                        · exact pairInput_symm _ _
                      rw [hpe]; exact (hU2_BJ e1 h1 u' v' hcu' hcv' heq').1
                    · intro u v heq
                      obtain ⟨u', v', heq', hcu', hcv', _⟩ := orient_edge (col z2) (Finset.mem_sdiff.mp h2).1
                      have hpe : pairInput u v = pairInput u' v' := by
                        rcases Sym2.eq_iff.mp (heq'.symm.trans heq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · rfl
                        · exact pairInput_symm _ _
                      rw [hpe]; exact (hU2_BJ e2 h2 u' v' hcu' hcv' heq').1
                  · refine Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
                      conj_at_most_one_via_z0 z2 (FsB ∪ FsJ1) hMBJ
                        e1 (Finset.mem_sdiff.mp h1).1 e2 (Finset.mem_sdiff.mp h2).1 ?_ ?_)
                    · intro u v hcu hcv heq
                      obtain ⟨hBJ, hBel | ⟨hzv, huz, hfire⟩⟩ := hU2_BJ e1 h1 u v hcu hcv heq
                      · exact False.elim (hHasBel hBel)
                      · exact ⟨hzv, huz, hBJ, hfire⟩
                    · intro u v hcu hcv heq
                      obtain ⟨hBJ, hBel | ⟨hzv, huz, hfire⟩⟩ := hU2_BJ e2 h2 u v hcu hcv heq
                      · exact False.elim (hHasBel hBel)
                      · exact ⟨hzv, huz, hBJ, hfire⟩
              have hUle2 := hCard_union_two U1 U2 hSub12 hU1le hU2le
              omega
    · have hZ1 : (centreless G C).card = 1 := by omega
      have hR1 : (orN G C \ lam G C).card = 1 := by omega
      obtain ⟨zc, hZeq⟩ := Finset.card_eq_one.mp hZ1
      obtain ⟨m0, hReq⟩ := Finset.card_eq_one.mp hR1
      have hzcMem : zc ∈ centreless G C := by rw [hZeq]; exact Finset.mem_singleton_self zc
      have hm0Mem : m0 ∈ orN G C \ lam G C := by rw [hReq]; exact Finset.mem_singleton_self m0
      have hAllM0 : ∀ r ∈ orN G C \ lam G C, r = m0 := fun r hr => Finset.mem_singleton.mp (hReq ▸ hr)
      have hAllZ : ∀ z ∈ centreless G C, z = zc := fun z hz => Finset.mem_singleton.mp (hZeq ▸ hz)
      have hm0Data := (orN_mem C m0).mp (Finset.mem_sdiff.mp hm0Mem).1
      obtain ⟨hzclen, hzcop, hzcb⟩ := topData ((centreless_mem C zc).mp hzcMem).1
      have hEvalZ_case : ∀ (P0 P1 : (Fin n → Bool) → Prop),
          (∃ Fs0 : Finset (Finset (Fin n)), (∀ S ∈ Fs0, MonoSet S) ∧ ∀ x, P0 x ↔ setsEval Fs0 x) →
          (∃ Fs1 : Finset (Finset (Fin n)), (∀ S ∈ Fs1, MonoSet S) ∧ ∀ x, P1 x ↔ setsEval Fs1 x) →
          (∀ x : Fin n → Bool, gateVal n C zc x = true → P0 x ∨ P1 x) →
          (∀ x : Fin n → Bool, P0 x → gateVal n C zc x = true) →
          (∀ x : Fin n → Bool, P1 x → gateVal n C zc x = true) →
          (∀ e ∈ Ustar G C, ∀ u v : Fin n, e = s(u, v) → gateVal n C zc (pairInput u v) = true) →
          False := by
        intro P0 P1 hP0ex hP1ex hZimp hP0Z hP1Z hAllUinZ
        obtain ⟨Fs0, hM0, hE0⟩ := hP0ex
        obtain ⟨Fs1, hM1, hE1⟩ := hP1ex
        let U0 := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → setsEval Fs0 (pairInput u v))
        let U1 := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → setsEval Fs1 (pairInput u v))
        have hsub : Ustar G C ⊆ U0 ∪ U1 := by
          intro e he
          induction e using Sym2.ind with
          | _ u v =>
            have hzv := hAllUinZ s(u, v) he u v rfl
            rcases hZimp (pairInput u v) hzv with hp0 | hp1
            · apply Finset.mem_union_left
              refine Finset.mem_filter.mpr ⟨he, fun u' v' heq => ?_⟩
              have hpe : pairInput u' v' = pairInput u v := by
                rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact pairInput_symm _ _
              rw [hpe]; exact (hE0 _).mp hp0
            · apply Finset.mem_union_right
              refine Finset.mem_filter.mpr ⟨he, fun u' v' heq => ?_⟩
              have hpe : pairInput u' v' = pairInput u v := by
                rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact pairInput_symm _ _
              rw [hpe]; exact (hE1 _).mp hp1
        have hU0le : U0.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
          conj_at_most_one_centreless Fs0 hM0 (fun x hx => hzcb x (hP0Z x ((hE0 x).mpr hx)))
            e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
            (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
        have hU1le : U1.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
          conj_at_most_one_centreless Fs1 hM1 (fun x hx => hzcb x (hP1Z x ((hE1 x).mpr hx)))
            e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
            (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
        have hUle2 := hCard_union_two U0 U1 hsub hU0le hU1le
        omega
      have hSubM0 := hAtMostOneR_eval C.gates.length m0 hm0Data.1 hm0Mem (fun r hr _ => hAllM0 r hr)
      have hZ_opnd_kind : ∀ b : Fin 2, opnd C zc b < n ∨
          ∃ g, opnd C zc b = n + g ∧ g < C.gates.length ∧ ¬ BelowF G C g := by
        intro b
        by_cases hbn : opnd C zc b < n
        · exact Or.inl hbn
        · right
          refine ⟨opnd C zc b - n, by omega, by have := opndBound hzclen b; omega, ?_⟩
          intro hbk
          have hcone : InCone n C (opnd C zc b - n) zc :=
            (inCone_iff _ zc).mpr ⟨hzclen, opnd C zc b - n, by have := opndBound hzclen b; omega, by
              have he : n + (opnd C zc b - n) = opnd C zc b := by omega
              rw [he]; exact opndMem hzclen b, Or.inl rfl⟩
          exact not_belowF_inCone_and (by have := opndBound hzclen b; omega) hbk hzclen hzcop hcone
      by_cases hm0Empty : orIn n C (n + m0) = ∅
      · obtain ⟨Fs0, Fs1, hM0, hM1, _, hEv⟩ := hSubM0.1 hm0Empty
        have hAllInZ : ∀ e ∈ Ustar G C, ∀ u v : Fin n, e = s(u, v) → gateVal n C zc (pairInput u v) = true := by
          intro e he u v rfl
          obtain ⟨a, ha, hv, b, j, hj, hr, _⟩ := residualTrace he
          by_cases haZ : a ∈ centreless G C
          · rw [← hAllZ a haZ]; exact hv
          · exfalso
            rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
            · exact haZ (emptySide ha (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1))
            · have hrEq := hAllM0 r (lastOrOutside hj hrlen hrop hrin hrb)
              subst r
              rcases lastOrBefore htr with heq2 | ⟨r2, hr2len, hr2op, hr2in, hr2b, _⟩
              · exact haZ (emptySide ha (by rw [side_def, heq2]; exact hm0Empty))
              · have hr2R : r2 ∈ orN G C \ lam G C := by
                  have hr2nb : ¬ BelowF G C r2 := by
                    intro hrb2
                    apply hm0Data.2.2
                    intro x hx
                    exact hrb2 x ((val_or List.length_ofFn hr2len hr2op).mpr ⟨n + m0, hr2in, hr2b, hx⟩)
                  refine Finset.mem_sdiff.mpr ⟨(orN_mem C r2).mpr ⟨hr2len, hr2op, hr2nb⟩, ?_⟩
                  intro hr2l
                  obtain ⟨_, h0, h1, _⟩ := (lam_mem C r2).mp hr2l
                  obtain ⟨b2, hb2⟩ := inputsAsOpnd hr2len hr2in
                  have hne2 : (orIn n C (opnd C r2 b2)).Nonempty := by fin_cases b2; exact h0; exact h1
                  rw [← hb2, hm0Empty] at hne2
                  exact Finset.not_nonempty_empty hne2
                have := hAllM0 r2 hr2R
                omega
        have hz0 := hEv (opnd C zc 0) (by have := opndBound hzclen 0; omega) (hZ_opnd_kind 0)
        have hz1 := hEv (opnd C zc 1) (by have := opndBound hzclen 1; omega) (hZ_opnd_kind 1)
        rcases hz0 with ⟨A0, hMA0, hEA0⟩ | ⟨A0, hMA0, hEA0⟩ <;>
          rcases hz1 with ⟨A1, hMA1, hEA1⟩ | ⟨A1, hMA1, hEA1⟩
        · exact hEvalZ_case (setsEval (A0 ∪ A1)) (setsEval (A0 ∪ A1))
            ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun _ => Iff.rfl⟩
            ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun _ => Iff.rfl⟩
            (fun x hx => Or.inl ((setsEval_union A0 A1 x).mpr (by rw [← hEA0, ← hEA1, ← andValBoth hzclen hzcop]; exact hx)))
            (fun x hx => (andValBoth hzclen hzcop x).mpr (by rw [hEA0, hEA1, ← setsEval_union]; exact hx))
            (fun x hx => (andValBoth hzclen hzcop x).mpr (by rw [hEA0, hEA1, ← setsEval_union]; exact hx))
            hAllInZ
        · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
            ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
            ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
            (fun x hx => by
              have h := (andValBoth hzclen hzcop x).mp hx
              rw [hEA0, hEA1] at h
              rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
              rcases h with ⟨a0, a1, f0 | f1⟩
              · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
              · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨hx.1.1, hx.1.2, Or.inl hx.2⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨hx.1.1, hx.1.2, Or.inr hx.2⟩)
            hAllInZ
        · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
            ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
            ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
            (fun x hx => by
              have h := (andValBoth hzclen hzcop x).mp hx
              rw [hEA0, hEA1] at h
              rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
              rcases h with ⟨⟨a0, f0 | f1⟩, a1⟩
              · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
              · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨⟨hx.1.1, Or.inl hx.2⟩, hx.1.2⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨⟨hx.1.1, Or.inr hx.2⟩, hx.1.2⟩)
            hAllInZ
        · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
            ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
            ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
            (fun x hx => by
              have h := (andValBoth hzclen hzcop x).mp hx
              rw [hEA0, hEA1] at h
              rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
              rcases h with ⟨⟨a0, f0 | f1⟩, ⟨a1, _⟩⟩
              · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
              · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨⟨hx.1.1, Or.inl hx.2⟩, ⟨hx.1.2, Or.inl hx.2⟩⟩)
            (fun x hx => by
              rw [setsEval_union, setsEval_union] at hx
              rw [andValBoth hzclen hzcop, hEA0, hEA1]
              exact ⟨⟨hx.1.1, Or.inr hx.2⟩, ⟨hx.1.2, Or.inr hx.2⟩⟩)
            hAllInZ
      · have hm0Ne : (orIn n C (n + m0)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hm0Empty
        by_cases hBothNe : (orIn n C (opnd C m0 0)).Nonempty ∧ (orIn n C (opnd C m0 1)).Nonempty
        · obtain ⟨Fs0, Fs1, hM0, hM1, _, hEv⟩ := hSubM0.2.1 hBothNe.1 hBothNe.2
          have hAllInZ : ∀ e ∈ Ustar G C, ∀ u v : Fin n, e = s(u, v) → gateVal n C zc (pairInput u v) = true := by
            intro e he u v rfl
            obtain ⟨a, ha, hv, b, j, hj, hr, _⟩ := residualTrace he
            by_cases haZ : a ∈ centreless G C
            · rw [← hAllZ a haZ]; exact hv
            · exfalso
              rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, _⟩
              · exact haZ (emptySide ha (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1))
              · have hrEq := hAllM0 r (lastOrOutside hj hrlen hrop hrin hrb)
                subst r
                obtain ⟨b0, hb0⟩ := inputsAsOpnd hm0Data.1 hrin
                have he0 : orIn n C (opnd C m0 b0) = ∅ := by rw [← hb0]; exact andRawEmpty (junkData hj).2.1
                fin_cases b0
                · have h0e : orIn n C (opnd C m0 0) = ∅ := he0
                  rw [h0e] at hBothNe; exact Finset.not_nonempty_empty hBothNe.1
                · have h1e : orIn n C (opnd C m0 1) = ∅ := he0
                  rw [h1e] at hBothNe; exact Finset.not_nonempty_empty hBothNe.2
          have hz0 := hEv (opnd C zc 0) (by have := opndBound hzclen 0; omega) (hZ_opnd_kind 0)
          have hz1 := hEv (opnd C zc 1) (by have := opndBound hzclen 1; omega) (hZ_opnd_kind 1)
          rcases hz0 with ⟨A0, hMA0, hEA0⟩ | ⟨A0, hMA0, hEA0⟩ <;>
            rcases hz1 with ⟨A1, hMA1, hEA1⟩ | ⟨A1, hMA1, hEA1⟩
          · exact hEvalZ_case (setsEval (A0 ∪ A1)) (setsEval (A0 ∪ A1))
              ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun _ => Iff.rfl⟩
              ⟨A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun _ => Iff.rfl⟩
              (fun x hx => Or.inl ((setsEval_union A0 A1 x).mpr (by rw [← hEA0, ← hEA1, ← andValBoth hzclen hzcop]; exact hx)))
              (fun x hx => (andValBoth hzclen hzcop x).mpr (by rw [hEA0, hEA1, ← setsEval_union]; exact hx))
              (fun x hx => (andValBoth hzclen hzcop x).mpr (by rw [hEA0, hEA1, ← setsEval_union]; exact hx))
              hAllInZ
          · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
              ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
              ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
              (fun x hx => by
                have h := (andValBoth hzclen hzcop x).mp hx; rw [hEA0, hEA1] at h
                rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
                rcases h with ⟨a0, a1, f0 | f1⟩
                · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
                · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨hx.1.1, hx.1.2, Or.inl hx.2⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨hx.1.1, hx.1.2, Or.inr hx.2⟩)
              hAllInZ
          · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
              ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
              ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
              (fun x hx => by
                have h := (andValBoth hzclen hzcop x).mp hx; rw [hEA0, hEA1] at h
                rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
                rcases h with ⟨⟨a0, f0 | f1⟩, a1⟩
                · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
                · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨⟨hx.1.1, Or.inl hx.2⟩, hx.1.2⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨⟨hx.1.1, Or.inr hx.2⟩, hx.1.2⟩)
              hAllInZ
          · exact hEvalZ_case (setsEval (A0 ∪ A1 ∪ Fs0)) (setsEval (A0 ∪ A1 ∪ Fs1))
              ⟨A0 ∪ A1 ∪ Fs0, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM0 S), fun _ => Iff.rfl⟩
              ⟨A0 ∪ A1 ∪ Fs1, fun S hS => (Finset.mem_union.mp hS).elim (fun h => (Finset.mem_union.mp h).elim (hMA0 S) (hMA1 S)) (hM1 S), fun _ => Iff.rfl⟩
              (fun x hx => by
                have h := (andValBoth hzclen hzcop x).mp hx; rw [hEA0, hEA1] at h
                rw [setsEval_union, setsEval_union, setsEval_union, setsEval_union]
                rcases h with ⟨⟨a0, f0 | f1⟩, ⟨a1, _⟩⟩
                · exact Or.inl ⟨⟨a0, a1⟩, f0⟩
                · exact Or.inr ⟨⟨a0, a1⟩, f1⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨⟨hx.1.1, Or.inl hx.2⟩, ⟨hx.1.2, Or.inl hx.2⟩⟩)
              (fun x hx => by rw [setsEval_union, setsEval_union] at hx; rw [andValBoth hzclen hzcop, hEA0, hEA1]; exact ⟨⟨hx.1.1, Or.inr hx.2⟩, ⟨hx.1.2, Or.inr hx.2⟩⟩)
              hAllInZ
        · have hMixed : ∃ d0 : Fin 2, orIn n C (opnd C m0 d0) = ∅ ∧ (orIn n C (opnd C m0 (1 - d0))).Nonempty := by
            by_cases h0 : (orIn n C (opnd C m0 0)).Nonempty
            · have h1 : ¬ (orIn n C (opnd C m0 1)).Nonempty := fun h => hBothNe ⟨h0, h⟩
              exact ⟨1, Finset.not_nonempty_iff_eq_empty.mp h1, h0⟩
            · by_cases h1 : (orIn n C (opnd C m0 1)).Nonempty
              · exact ⟨0, Finset.not_nonempty_iff_eq_empty.mp h0, h1⟩
              · have htot := orEmpty (r := m0) (fun w hw => by
                  obtain ⟨b, rfl⟩ := inputsAsOpnd hm0Data.1 hw
                  fin_cases b
                  · exact Finset.not_nonempty_iff_eq_empty.mp h0
                  · exact Finset.not_nonempty_iff_eq_empty.mp h1)
                rw [htot] at hm0Ne
                exact False.elim (Finset.not_nonempty_empty hm0Ne)
          obtain ⟨d0, hd0e, hd1ne⟩ := hMixed
          obtain ⟨j1, _, hj1mem, hj1op, ⟨FsJ1, hMFsJ1, hEFsJ1⟩, ⟨_, _, _, _⟩, hEv⟩ :=
            hSubM0.2.2 d0 hd0e hd1ne
          have hZ_decomp : ∃ FsA FsB : Finset (Finset (Fin n)), (∀ S ∈ FsA, MonoSet S) ∧ (∀ S ∈ FsB, MonoSet S) ∧
              ∀ x : Fin n → Bool, gateVal n C zc x = true ↔ setsEval FsA x ∨ (setsEval FsB x ∧ gateVal n C j1 x = true) := by
            have hz0 := hEv (opnd C zc 0) (by have := opndBound hzclen 0; omega) (hZ_opnd_kind 0)
            have hz1 := hEv (opnd C zc 1) (by have := opndBound hzclen 1; omega) (hZ_opnd_kind 1)
            rcases hz0 with ⟨A0, hMA0, hEA0⟩ | ⟨A0, B0, hBA0, hMA0, hEA0⟩ <;>
              rcases hz1 with ⟨A1, hMA1, hEA1⟩ | ⟨A1, B1, hBA1, hMA1, hEA1⟩
            · refine ⟨A0 ∪ A1, A0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S),
                fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S), fun x => ?_⟩
              rw [andValBoth hzclen hzcop, hEA0, hEA1, setsEval_union]
              exact ⟨Or.inl, fun h => h.elim id And.left⟩
            · refine ⟨A0 ∪ A1, A0 ∪ B1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S),
                fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (fun h => hMA1 S (hBA1 h)), fun x => ?_⟩
              rw [andValBoth hzclen hzcop, hEA0, hEA1, setsEval_union, setsEval_union]
              exact ⟨fun h => h.2.elim (fun a1 => Or.inl ⟨h.1, a1⟩) (fun h1 => Or.inr ⟨⟨h.1, h1.1⟩, h1.2⟩),
                fun h => h.elim (fun h1 => ⟨h1.1, Or.inl h1.2⟩) (fun h1 => ⟨h1.1.1, Or.inr ⟨h1.1.2, h1.2⟩⟩)⟩
            · refine ⟨A0 ∪ A1, B0 ∪ A1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S),
                fun S hS => (Finset.mem_union.mp hS).elim (fun h => hMA0 S (hBA0 h)) (hMA1 S), fun x => ?_⟩
              rw [andValBoth hzclen hzcop, hEA0, hEA1, setsEval_union, setsEval_union]
              exact ⟨fun h => h.1.elim (fun a0 => Or.inl ⟨a0, h.2⟩) (fun h0 => Or.inr ⟨⟨h0.1, h.2⟩, h0.2⟩),
                fun h => h.elim (fun h1 => ⟨Or.inl h1.1, h1.2⟩) (fun h1 => ⟨Or.inr ⟨h1.1.1, h1.2⟩, h1.1.2⟩)⟩
            · refine ⟨A0 ∪ A1, B0 ∪ B1, fun S hS => (Finset.mem_union.mp hS).elim (hMA0 S) (hMA1 S),
                fun S hS => (Finset.mem_union.mp hS).elim (fun h => hMA0 S (hBA0 h)) (fun h => hMA1 S (hBA1 h)), fun x => ?_⟩
              rw [andValBoth hzclen hzcop, hEA0, hEA1, setsEval_union, setsEval_union]
              constructor
              · rintro ⟨h0 | ⟨hb0, hj⟩, h1 | ⟨hb1, hj'⟩⟩
                · exact Or.inl ⟨h0, h1⟩
                · exact Or.inr ⟨⟨setsEval_mono_sub hBA0 h0, hb1⟩, hj'⟩
                · exact Or.inr ⟨⟨hb0, setsEval_mono_sub hBA1 h1⟩, hj⟩
                · exact Or.inr ⟨⟨hb0, hb1⟩, hj⟩
              · rintro (⟨h0, h1⟩ | ⟨⟨hb0, hb1⟩, hj⟩)
                · exact ⟨Or.inl h0, Or.inl h1⟩
                · exact ⟨Or.inr ⟨hb0, hj⟩, Or.inr ⟨hb1, hj⟩⟩
          obtain ⟨FsA, FsB, hMFsA, hMFsB, hZeqEval⟩ := hZ_decomp
          have hm0Ne' := hm0Ne
          obtain ⟨z0, hz0⟩ := hm0Ne'
          let U_w := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → setsEval FsA (pairInput u v))
          let U_j := (Ustar G C).filter (fun e => ∀ u v : Fin n, e = s(u, v) → gateVal n C j1 (pairInput u v) = true)
          have hUniqJ1 : ∀ j ∈ junk G C, n + j ∈ (gateAt C m0).inputs → j = j1 := by
            intro j hj hjm
            obtain ⟨b, hb⟩ := inputsAsOpnd hm0Data.1 hjm
            by_cases hbd : b = d0
            · subst b
              have : n + j = n + j1 := hb.trans hj1op
              omega
            · have hb1 : b = 1 - d0 := by fin_cases d0 <;> fin_cases b <;> first | rfl | exact False.elim (hbd rfl)
              subst b
              rw [← hb, andRawEmpty (junkData hj).2.1] at hd1ne
              exact False.elim (Finset.not_nonempty_empty hd1ne)
          have hSubUJ : Ustar G C ⊆ U_w ∪ U_j := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              obtain ⟨a, ha, hv, b, j, hj, hr, hjv⟩ := residualTrace he
              by_cases haZ : a ∈ centreless G C
              · rw [hAllZ a haZ] at hv
                rcases (hZeqEval _).mp hv with hA | ⟨_, hj1v⟩
                · apply Finset.mem_union_left
                  refine Finset.mem_filter.mpr ⟨he, fun u' v' heq => ?_⟩
                  have hpe : pairInput u' v' = pairInput u v := by
                    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact pairInput_symm _ _
                  rw [hpe]; exact hA
                · apply Finset.mem_union_right
                  refine Finset.mem_filter.mpr ⟨he, fun u' v' heq => ?_⟩
                  have hpe : pairInput u' v' = pairInput u v := by
                    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact pairInput_symm _ _
                  rw [hpe]; exact hj1v
              · rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨r, hrlen, hrop, hrin, hrb, _⟩
                · exact False.elim (haZ (emptySide ha (by rw [side_def, heq]; exact andRawEmpty (junkData hj).2.1)))
                · have hrEq := hAllM0 r (lastOrOutside hj hrlen hrop hrin hrb)
                  subst r
                  have hjEq := hUniqJ1 j hj hrin
                  subst j
                  apply Finset.mem_union_right
                  refine Finset.mem_filter.mpr ⟨he, fun u' v' heq => ?_⟩
                  have hpe : pairInput u' v' = pairInput u v := by
                    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact pairInput_symm _ _
                  rw [hpe]; exact hjv
          have hUwLe : U_w.card ≤ 1 := Finset.card_le_one.mpr (fun e1 h1 e2 h2 =>
            conj_at_most_one_centreless FsA hMFsA (fun x hx => hzcb x ((hZeqEval x).mpr (Or.inl hx)))
              e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
              (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
          have hUjLe : U_j.card ≤ 1 := by
            by_cases hHasNonZ : ∃ e ∈ U_j, ∃ u v : Fin n, e = s(u, v) ∧
                ∃ a ∈ tops G C, a ∉ centreless G C ∧ gateVal n C a (pairInput u v) = true ∧
                ∃ b : Fin 2, OrReaches n C (opnd C a b) m0 ∧ OrReaches n C (opnd C a b) j1
            · obtain ⟨e0, he0Uj, u0, v0, he0eq, a0, ha0, ha0nc, ha0v, b0, hrm0, hrj1⟩ := hHasNonZ
              have he0U := (Finset.mem_filter.mp he0Uj).1
              have hj1v0 := (Finset.mem_filter.mp he0Uj).2 u0 v0 he0eq
              obtain ⟨u0', v0', h0eq, hu0'c, hv0'c, _⟩ := orient_edge (col z0) he0U
              have hpe0 : pairInput u0' v0' = pairInput u0 v0 := by
                have h := he0eq.symm.trans h0eq
                rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact pairInput_symm _ _
              rw [← hpe0] at ha0v hj1v0
              obtain ⟨_, _, hfire0⟩ := hRouteSingleR m0 hm0Mem hm0Ne j1 hj1mem u0' v0' a0 b0 ha0 ha0nc ha0v
                (h0eq ▸ he0U) hrm0 hrj1 hj1v0 z0 hz0 hu0'c hv0'c hAllM0
              refine Finset.card_le_one.mpr (fun e1 h1 e2 h2 => ?_)
              have hEq0 : ∀ e ∈ U_j, e = e0 := by
                intro e he
                by_contra hne
                obtain ⟨u, v, rfl, _, _, _⟩ := orient_edge (col z0) (Finset.mem_filter.mp he).1
                have hjv := (Finset.mem_filter.mp he).2 u v rfl
                exact pure_junk_at_most_one_Ustar j1 FsJ1 hj1mem hMFsJ1 hEFsJ1 u0' v0' (h0eq ▸ he0U) hfire0 hj1v0
                  u v (Finset.mem_filter.mp he).1 (fun h => hne (h.symm.trans h0eq.symm)) hjv
              exact (hEq0 e1 h1).trans (hEq0 e2 h2).symm
            · refine Finset.card_le_one.mpr (fun e1 h1 e2 h2 => ?_)
              have hInZ_j : ∀ e ∈ U_j, ∀ u v : Fin n, e = s(u, v) →
                  setsEval (FsB ∪ FsJ1) (pairInput u v) ∨ setsEval FsA (pairInput u v) := by
                intro e he u v heq
                have heU := (Finset.mem_filter.mp he).1
                have hj1v := (Finset.mem_filter.mp he).2 u v heq
                obtain ⟨a, ha, hv, b, j, hj, hr, _⟩ := residualTrace (heq ▸ heU)
                by_cases haZ : a ∈ centreless G C
                · rw [hAllZ a haZ] at hv
                  rcases (hZeqEval _).mp hv with hA | ⟨hB, hj1'⟩
                  · exact Or.inr hA
                  · exact Or.inl ((setsEval_union FsB FsJ1 _).mpr ⟨hB, (hEFsJ1 _).mp hj1'⟩)
                · exfalso
                  rcases lastOrBefore (orReaches_reach j _ hr).1 with heq' | ⟨r, hrlen, hrop, hrin, hrb, htr⟩
                  · exact haZ (emptySide ha (by rw [side_def, heq']; exact andRawEmpty (junkData hj).2.1))
                  · have hrEq := hAllM0 r (lastOrOutside hj hrlen hrop hrin hrb)
                    subst r
                    have hjEq := hUniqJ1 j hj hrin
                    subst j
                    exact hHasNonZ ⟨e, he, u, v, heq, a, ha, haZ, hv, b, reach_orReaches htr m0 rfl hm0Data.1, hr⟩
              by_contra hne
              have hNotInA : ∀ e ∈ U_j, e ∉ U_w → ∀ u v : Fin n, e = s(u, v) →
                  setsEval (FsB ∪ FsJ1) (pairInput u v) := by
                intro e he hnw u v heq
                rcases hInZ_j e he u v heq with hBJ | hA
                · exact hBJ
                · exfalso
                  apply hnw
                  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, fun u' v' heq' => ?_⟩
                  have hpe : pairInput u' v' = pairInput u v := by
                    have h := heq.symm.trans heq'
                    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact pairInput_symm _ _
                  rw [hpe]; exact hA
              have hU_j_sdiff_le : (U_j \ U_w).card ≤ 1 := Finset.card_le_one.mpr (fun x1 hx1 x2 hx2 =>
                conj_at_most_one_centreless (FsB ∪ FsJ1)
                  (fun S hS => (Finset.mem_union.mp hS).elim (hMFsB S) (hMFsJ1 S))
                  (fun x hx => hzcb x ((hZeqEval x).mpr (Or.inr
                    ⟨((setsEval_union FsB FsJ1 x).mp hx).1, (hEFsJ1 x).mpr ((setsEval_union FsB FsJ1 x).mp hx).2⟩)))
                  x1 (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx1).1).1
                  x2 (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx2).1).1
                  (hNotInA x1 (Finset.mem_sdiff.mp hx1).1 (Finset.mem_sdiff.mp hx1).2)
                  (hNotInA x2 (Finset.mem_sdiff.mp hx2).1 (Finset.mem_sdiff.mp hx2).2))
              have hSub2 : Ustar G C ⊆ U_w ∪ (U_j \ U_w) := by
                intro e he
                rcases Finset.mem_union.mp (hSubUJ he) with hw | hj
                · exact Finset.mem_union_left _ hw
                · by_cases hw : e ∈ U_w
                  · exact Finset.mem_union_left _ hw
                  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj, hw⟩)
              have hUle2 := hCard_union_two U_w (U_j \ U_w) hSub2 hUwLe hU_j_sdiff_le
              omega
          have hUle2 := hCard_union_two U_w U_j hSubUJ hUwLe hUjLe
          omega
  have hBudgetGe5 : 5 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
    omega
  have hUstarGe3 : 3 ≤ (Ustar G C).card := by
    omega
  exact hResidual n G C ⟨fCol⟩ hCyc h4 hLeast hTop hAllBad hJunkGe2 hOneR hZplusR_ge3 hBudgetGe5 hUstarGe3
    hBudgetLtCov ⟨jw, hjwMem, a1, b1, a2, b2, he1U, he2U, hne12, hgv1, hgv2⟩
