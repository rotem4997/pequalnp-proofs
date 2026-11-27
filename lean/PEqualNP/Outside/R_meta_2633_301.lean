import Mathlib
import PEqualNP.Defs

-- Eliminate every bipartite graph and every circuit whose size meets or exceeds the
-- vertex-cover star bound |A| + |E(G)| + tau(G) - 1 (by slot counting plus edge-cover
-- construction on G - z). Then split the tight non-bipartite residual into monotone
-- circuits (Monotone2) versus circuits containing at least one NOT gate.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2633_301 :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1))
    (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
    have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) =>
      List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) =>
        (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7)
        x5.gates;
    ¬x2.Colorable (2 : ℕ) →
    (∀ T : Finset (Fin x1), (∀ u v : Fin x1, x2.Adj u v → u ∈ T ∨ v ∈ T) →
      x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + T.card) →
    PEqualNP.MetaComplexity.Monotone2 x5 →
    (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
    (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
    (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
    (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
    PEqualNP.MetaComplexity.FanInTwo x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
    (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
    (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧
      ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) →
    ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) →
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1))
    (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
    have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) =>
      List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) =>
        (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7)
        x5.gates;
    ¬x2.Colorable (2 : ℕ) →
    (∀ T : Finset (Fin x1), (∀ u v : Fin x1, x2.Adj u v → u ∈ T ∨ v ∈ T) →
      x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + T.card) →
    (∃ g ∈ x5.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
    (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
    (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
    (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
    (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
    PEqualNP.MetaComplexity.FanInTwo x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
    (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
    (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧
      ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) →
    ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1))
    (x5 : PEqualNP.CircuitLowerBounds.Circuit),
    have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
    have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) =>
      List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) =>
        (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7)
        x5.gates;
    (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
    (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
    (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
    (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
    PEqualNP.MetaComplexity.FanInTwo x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
    (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
    (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧
      ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) →
    ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  classical
  intro hmono hnot n G instG A C
  dsimp only
  intro hdeg hgirth hnoA hedge hfan heval hmin hread hallOr htwo
  let f : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G A
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let runW : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs w =>
    gs.foldl step w
  have hrun_nil : ∀ w, runW [] w = w := fun _ => rfl
  have hrun_cons : ∀ g gs w, runW (g :: gs) w = runW gs (step w g) := fun _ _ _ => rfl
  have hrun_append : ∀ gs1 gs2 w, runW (gs1 ++ gs2) w = runW gs2 (runW gs1 w) := by
    intro gs1 gs2 w
    exact List.foldl_append
  have hrun_len : ∀ gs w, (runW gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [runW]
    | cons g gs ih =>
      intro w
      rw [hrun_cons, ih]
      simp [step]
      omega
  have hgetD_snoc_lt : ∀ (l : List Bool) (b : Bool) (i : ℕ), i < l.length →
      (l ++ [b]).getD i false = l.getD i false := by
    intro l b i hi
    simp [List.getD, List.getElem?_append_left hi]
  have hgetD_snoc_eq : ∀ (l : List Bool) (b : Bool),
      (l ++ [b]).getD l.length false = b := by
    intro l b
    simp [List.getD]
  have hrun_getD_lt : ∀ gs w i, i < w.length →
      (runW gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [hrun_cons, ih (step w g) i (by simp [step]; omega)]
      exact hgetD_snoc_lt w _ i hi
  have hofFn_getD : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
  have hf_iff : ∀ x : Fin n → Bool, f x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change (decide (∃ a ∈ A, x a = true) || decide (∃ u v : Fin n, G.Adj u v ∧
      x u = true ∧ x v = true)) = true ↔ _
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have hcircuitFun_eq : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool),
      PEqualNP.MetaComplexity.circuitFun n D x = (runW D.gates (List.ofFn x)).getD D.output false :=
    fun _ _ => rfl
  have hsize_eq : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have hand_eval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hor_eval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  -- Part 1: Modular FanInTwo circuit builder for graphFun (G - z) A given a vertex cover T of G.
  let Bld : ((Fin n → Bool) → Bool) → ℕ → Prop := fun h k =>
    ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, out⟩ ∧ gs.length ≤ k ∧ out < n + gs.length ∧
      ∀ x : Fin n → Bool, (runW gs (List.ofFn x)).getD out false = h x
  have hbld_mono : ∀ h k1 k2, Bld h k1 → k1 ≤ k2 → Bld h k2 := by
    intro h k1 k2 hb hle
    rcases hb with ⟨gs, out, hfa, hlen, hout, hok⟩
    exact ⟨gs, out, hfa, hlen.trans hle, hout, hok⟩
  have hbld_congr : ∀ h1 h2 k, Bld h1 k → (∀ x, h1 x = h2 x) → Bld h2 k := by
    intro h1 h2 k hb heq
    rcases hb with ⟨gs, out, hfa, hlen, hout, hok⟩
    exact ⟨gs, out, hfa, hlen, hout, fun x => (hok x).trans (heq x)⟩
  have hbld_hasSize : ∀ h k, Bld h k → PEqualNP.MetaComplexity.HasCircuitSize n h k := by
    intro h k hb
    rcases hb with ⟨gs, out, hfa, hlen, _, hok⟩
    exact ⟨⟨gs, out⟩, hfa, hlen, hok⟩
  have hbld_var : ∀ v : Fin n, Bld (fun x => x v) 0 := by
    intro v
    refine ⟨[], v.val, ?_, Nat.le_refl 0, by simp, ?_⟩
    · intro g hg; cases hg
    · intro x
      rw [hrun_nil, hofFn_getD x v.val v.isLt]
  have hbld_bin : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp)
      (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (h1 h2 : (Fin n → Bool) → Bool) (k1 k2 : ℕ),
      Bld h1 k1 → Bld h2 k2 →
      Bld (fun x => op.eval [h1 x, h2 x]) (k1 + k2 + 1) := by
    intro op hop h1 h2 k1 k2 hb1 hb2
    rcases hb1 with ⟨gs1, out1, hfa1, hlen1, hout1, hok1⟩
    rcases hb2 with ⟨gs2, out2, hfa2, hlen2, hout2, hok2⟩
    let sh : ℕ → ℕ := fun i => if i < n then i else i + gs1.length
    let shG : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
      ⟨g.op, g.inputs.map sh⟩
    let gs2' := gs2.map shG
    have hsh_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
        w1.length = n + gs1.length → w2.length = n →
        (∀ i, i < n → w1.getD i false = w2.getD i false) →
        ∀ (w1' w2' : List Bool),
          w1'.length = w1.length + gs.length →
          w2'.length = w2.length + gs.length →
          (∀ i, i < w2.length → w1'.getD (sh i) false = w2'.getD i false) →
          True := fun _ _ _ _ _ _ _ _ _ _ _ => trivial
    have hsh_sim : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
        w1.length = w2.length + gs1.length →
        n ≤ w2.length →
        (∀ i, i < w2.length → w1.getD (sh i) false = w2.getD i false) →
        (runW (gs.map shG) w1).length = (runW gs w2).length + gs1.length ∧
        (∀ i, i < (runW gs w2).length →
          (runW (gs.map shG) w1).getD (sh i) false = (runW gs w2).getD i false) := by
      intro gs
      induction gs with
      | nil =>
        intro w1 w2 hlen hn hagr
        exact ⟨hlen, hagr⟩
      | cons g gs ih =>
        intro w1 w2 hlen hn hagr
        rw [List.map_cons, hrun_cons, hrun_cons]
        have hmap_eq : ((shG g).inputs.map (fun i => w1.getD i false)) =
            (g.inputs.map (fun i => w2.getD i false)) := by
          change ((g.inputs.map sh).map (fun i => w1.getD i false)) = _
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          change w1.getD (sh i) false = w2.getD i false
          by_cases hi : i < w2.length
          · exact hagr i hi
          · have hsh_ge : w1.length ≤ sh i := by
              dsimp only [sh]
              split_ifs <;> omega
            rw [List.getD_eq_default _ _ hsh_ge, List.getD_eq_default _ _ (by omega)]
        have hval_eq : (shG g).op.eval ((shG g).inputs.map (fun i => w1.getD i false)) =
            g.op.eval (g.inputs.map (fun i => w2.getD i false)) :=
          congrArg g.op.eval hmap_eq
        apply ih (step w1 (shG g)) (step w2 g)
        · simp [step, hlen]; omega
        · simp [step]; omega
        · intro i hi
          simp only [step, List.length_append, List.length_singleton] at hi
          by_cases hlt : i < w2.length
          · have hsh_lt : sh i < w1.length := by
              dsimp only [sh]; split_ifs <;> omega
            rw [hgetD_snoc_lt w1 _ (sh i) hsh_lt, hgetD_snoc_lt w2 _ i hlt]
            exact hagr i hlt
          · have heq : i = w2.length := by omega
            subst heq
            have hsh_eq : sh w2.length = w1.length := by
              dsimp only [sh]
              have hnot : ¬ w2.length < n := by omega
              rw [if_neg hnot, hlen]
            dsimp only [step]
            rw [hsh_eq, hgetD_snoc_eq, hgetD_snoc_eq, hval_eq]
    let gtop : PEqualNP.CircuitLowerBounds.Gate := ⟨op, [out1, sh out2]⟩
    refine ⟨gs1 ++ gs2' ++ [gtop], n + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg1 | hg2) | hg3
      · exact hfa1 g hg1
      · rcases List.mem_map.mp hg2 with ⟨g0, hg0, rfl⟩
        have hf0 := hfa2 g0 hg0
        exact ⟨hf0.1, by simp [shG, hf0.2]⟩
      · subst hg3
        refine ⟨?_, by simp [gtop]⟩
        rcases hop with rfl | rfl <;> simp [gtop]
    · simp only [List.length_append, List.length_singleton, List.length_map, gs2']
      omega
    · simp only [List.length_append, List.length_singleton, List.length_map, gs2']
      omega
    · intro x
      rw [hrun_append, hrun_append]
      have hlen1' : (runW gs1 (List.ofFn x)).length = n + gs1.length := by
        rw [hrun_len, List.length_ofFn]
      have hsim := hsh_sim gs2 (runW gs1 (List.ofFn x)) (List.ofFn x)
        (by rw [hlen1', List.length_ofFn]) (by simp) (by
          intro i hi
          rw [List.length_ofFn] at hi
          have hshi : sh i = i := if_pos hi
          rw [hshi, hrun_getD_lt gs1 (List.ofFn x) i (by simp; exact hi)])
      have hlen2' : (runW gs2' (runW gs1 (List.ofFn x))).length = n + gs1.length + gs2.length := by
        rw [hsim.1, hrun_len, List.length_ofFn]; omega
      have hres1 : (runW gs2' (runW gs1 (List.ofFn x))).getD out1 false = h1 x := by
        rw [hrun_getD_lt gs2' (runW gs1 (List.ofFn x)) out1 (by rw [hlen1']; exact hout1)]
        exact hok1 x
      have hres2 : (runW gs2' (runW gs1 (List.ofFn x))).getD (sh out2) false = h2 x := by
        rw [hsim.2 out2 (by rw [hrun_len, List.length_ofFn]; exact hout2)]
        exact hok2 x
      rw [hrun_cons, hrun_nil]
      dsimp only [step]
      rw [← hlen2', hgetD_snoc_eq]
      change op.eval [(runW gs2' (runW gs1 (List.ofFn x))).getD out1 false,
        (runW gs2' (runW gs1 (List.ofFn x))).getD (sh out2) false] = op.eval [h1 x, h2 x]
      rw [hres1, hres2]
  have hbld_orFinset : ∀ S : Finset (Fin n), S.Nonempty →
      Bld (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
    intro S hS
    refine Finset.Nonempty.cons_induction ?_ ?_ hS
    · intro a
      refine hbld_congr (fun x => x a) _ 0 (hbld_var a) ?_
      intro x; simp
    · intro a s ha hs ih
      have hstep := hbld_bin PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl)
        (fun x => x a) (fun x => decide (∃ v ∈ s, x v = true)) 0 (s.card - 1) (hbld_var a) ih
      have hpos : 0 < s.card := hs.card_pos
      refine hbld_congr _ _ ((s.cons a ha).card - 1) (hbld_mono _ _ _ hstep (by rw [Finset.card_cons]; omega)) ?_
      intro x
      rw [hor_eval]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_cons]
      constructor
      · intro h
        rcases h with h | ⟨v, hv, hxv⟩
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨v, Or.inr hv, hxv⟩
      · intro h
        rcases h with ⟨v, hv, hxv⟩
        rcases hv with rfl | hv
        · exact Or.inl hxv
        · exact Or.inr ⟨v, hv, hxv⟩
  have hbld_edges : ∀ (U : Finset (Fin n)) (E : Finset (Sym2 (Fin n))),
      E.Nonempty → (∀ e ∈ E, ¬e.IsDiag) → (∀ e ∈ E, ∃ t ∈ U, t ∈ e) →
      Bld (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + U.card - 1) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro E hE _ hcov
      rcases hE with ⟨e, he⟩
      rcases hcov e he with ⟨t, ht, _⟩
      exact absurd ht (Finset.notMem_empty t)
    | insert t U ht ih =>
      intro E hE hnd hcov
      let E1 := E.filter (fun e => t ∈ e)
      let E2 := E.filter (fun e => t ∉ e)
      have hsplit : E1.card + E2.card = E.card :=
        Finset.card_filter_add_card_filter_not (s := E) (fun e => t ∈ e)
      have hUcard : (insert t U).card = U.card + 1 := Finset.card_insert_of_notMem ht
      have hcov2 : ∀ e ∈ E2, ∃ u ∈ U, u ∈ e := by
        intro e he
        have he' := Finset.mem_filter.mp he
        rcases hcov e he'.1 with ⟨u, hu, hue⟩
        rcases Finset.mem_insert.mp hu with rfl | huU
        · exact absurd hue he'.2
        · exact ⟨u, huU, hue⟩
      have hnd2 : ∀ e ∈ E2, ¬e.IsDiag := fun e he => hnd e (Finset.mem_filter.mp he).1
      have hstar : E1.Nonempty →
          Bld (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) E1.card := by
        intro hE1
        let N : Finset (Fin n) := Finset.univ.filter (fun u => s(t, u) ∈ E1)
        have hNcard : N.card = E1.card := by
          refine Finset.card_bij (fun u _ => s(t, u)) ?_ ?_ ?_
          · intro u hu
            exact (Finset.mem_filter.mp hu).2
          · intro u1 hu1 u2 hu2 heq
            have h1 := Sym2.eq_iff.mp heq
            rcases h1 with ⟨_, h⟩ | ⟨_, h2⟩
            · exact h
            · exfalso
              have hm : s(t, u1) ∈ E := (Finset.mem_filter.mp (Finset.mem_filter.mp hu1).2).1
              exact hnd s(t, u1) hm (by rw [h2]; exact Sym2.mk_isDiag_iff.mpr rfl)
          · intro e he
            have hte : t ∈ e := (Finset.mem_filter.mp he).2
            rcases Sym2.mem_iff_exists.mp hte with ⟨u, rfl⟩
            exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, he⟩, rfl⟩
        have hNne : N.Nonempty := Finset.card_pos.mp (by rw [hNcard]; exact hE1.card_pos)
        have horN := hbld_orFinset N hNne
        have handN := hbld_bin PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl)
          (fun x => x t) (fun x => decide (∃ u ∈ N, x u = true)) 0 (N.card - 1) (hbld_var t) horN
        have hNpos : 0 < N.card := hNne.card_pos
        refine hbld_congr _ _ E1.card (hbld_mono _ _ _ handN (by omega)) ?_
        intro x
        rw [hand_eval]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h
          rcases h with ⟨hxt, u, huN, hxu⟩
          have huE1 : s(t, u) ∈ E1 := (Finset.mem_filter.mp huN).2
          refine ⟨s(t, u), huE1, ?_⟩
          intro v hv
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hxt
          · exact hxu
        · intro h
          rcases h with ⟨e, he1, hxe⟩
          have hte : t ∈ e := (Finset.mem_filter.mp he1).2
          rcases Sym2.mem_iff_exists.mp hte with ⟨u, rfl⟩
          exact ⟨hxe t (Sym2.mem_mk_left t u), u,
            Finset.mem_filter.mpr ⟨Finset.mem_univ u, he1⟩, hxe u (Sym2.mem_mk_right t u)⟩
      have hkey : ∀ x : Fin n → Bool,
          decide (∃ e ∈ E, ∀ v ∈ e, x v = true) =
            (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · intro h
          rcases h with ⟨e, he, hxe⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, Finset.mem_filter.mpr ⟨he, hte⟩, hxe⟩
          · exact Or.inr ⟨e, Finset.mem_filter.mpr ⟨he, hte⟩, hxe⟩
        · intro h
          rcases h with ⟨e, he, hxe⟩ | ⟨e, he, hxe⟩
          · exact ⟨e, (Finset.mem_filter.mp he).1, hxe⟩
          · exact ⟨e, (Finset.mem_filter.mp he).1, hxe⟩
      by_cases h1 : E1.Nonempty
      · by_cases h2 : E2.Nonempty
        · have hb1 := hstar h1
          have hb2 := ih E2 h2 hnd2 hcov2
          have hor12 := hbld_bin PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl) _ _ _ _ hb1 hb2
          have hp2 : 0 < E2.card := h2.card_pos
          refine hbld_congr _ _ _ (hbld_mono _ _ _ hor12 (by omega)) (fun x => ?_)
          rw [hor_eval, hkey x]
        · have hE2e : E2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
          have hE1c : E1.card = E.card := by rw [hE2e, Finset.card_empty] at hsplit; omega
          refine hbld_congr _ _ _ (hbld_mono _ _ _ (hstar h1) (by omega)) (fun x => ?_)
          rw [hkey x, hE2e]; simp
      · have hE1e : E1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1
        have hE2c : E2.card = E.card := by rw [hE1e, Finset.card_empty] at hsplit; omega
        have h2 : E2.Nonempty := Finset.card_pos.mp (by rw [hE2c]; exact hE.card_pos)
        refine hbld_congr _ _ _ (hbld_mono _ _ _ (ih E2 h2 hnd2 hcov2) (by omega)) (fun x => ?_)
        rw [hkey x, hE1e]; simp
  -- Part 2: If a vertex cover T of G satisfies A.card + G.edgeFinset.card + T.card ≤ C.size + 1,
  -- then deleting any z ∈ T \ A gives a circuit of size ≤ C.size - 4.
  have hcover_solve : ∀ T : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
      A.card + G.edgeFinset.card + T.card ≤ C.size + 1 →
      ∃ z ∉ A, ∃ s, s + 4 ≤ C.size ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x z false)) s := by
    intro T hcov hle
    rcases hedge with ⟨u0, v0, huv0⟩
    have hz_ex : ∃ z : Fin n, z ∈ T ∧ z ∉ A := by
      rcases hcov u0 v0 huv0 with hu | hv
      · exact ⟨u0, hu, hnoA u0 v0 huv0⟩
      · exact ⟨v0, hv, hnoA v0 u0 huv0.symm⟩
    rcases hz_ex with ⟨z, hzT, hzA⟩
    let G' := G.deleteEdges (G.incidenceSet z)
    let T' := T.erase z
    have hdegz : G.degree z = 3 := by
      rw [← G.ncard_neighborSet]
      exact hdeg z hzA
    have hnz_pos : 0 < (G.neighborFinset z).card := by
      rw [G.card_neighborFinset_eq_degree, hdegz]; omega
    rcases Finset.card_pos.mp hnz_pos with ⟨w, hw⟩
    have hzw : G.Adj z w := (SimpleGraph.mem_neighborFinset G z w).mp hw
    have hwA : w ∉ A := hnoA w z hzw.symm
    have hdegw : G.degree w = 3 := by
      rw [← G.ncard_neighborSet]
      exact hdeg w hwA
    have hnw_gt : 1 < (G.neighborFinset w).card := by
      rw [G.card_neighborFinset_eq_degree, hdegw]; omega
    have hw_ex : ∃ w' : Fin n, w' ∈ G.neighborFinset w ∧ w' ≠ z := by
      by_contra hno
      push Not at hno
      have hsub : G.neighborFinset w ⊆ {z} := by
        intro y hy
        exact Finset.mem_singleton.mpr (hno y hy)
      have hc := Finset.card_le_card hsub
      simp at hc
      omega
    rcases hw_ex with ⟨w', hw', hw'z⟩
    have hww' : G.Adj w w' := (SimpleGraph.mem_neighborFinset G w w').mp hw'
    have hG'adj : ∀ u v : Fin n, G'.Adj u v ↔ G.Adj u v ∧ u ≠ z ∧ v ≠ z :=
      fun u v => SimpleGraph.deleteIncidenceSet_adj
    have hG'edge : G'.Adj w w' := (hG'adj w w').mpr ⟨hww', hzw.ne.symm, hw'z⟩
    have hG'ne : G'.edgeFinset.Nonempty := ⟨s(w, w'), by simpa using hG'edge⟩
    have hG'card : G'.edgeFinset.card = G.edgeFinset.card - 3 := by
      have h1 := G.card_edgeFinset_deleteIncidenceSet z
      rw [hdegz] at h1
      exact h1
    have hEge4 : 4 ≤ G.edgeFinset.card := by
      have hpos : 0 < G'.edgeFinset.card := hG'ne.card_pos
      omega
    have hT'card : T'.card = T.card - 1 := Finset.card_erase_of_mem hzT
    have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨z, hzT⟩
    have hcov' : ∀ e ∈ G'.edgeFinset, ∃ t ∈ T', t ∈ e := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have h1 := (hG'adj u v).mp he
      rcases hcov u v h1.1 with hu | hv
      · exact ⟨u, Finset.mem_erase.mpr ⟨h1.2.1, hu⟩, Sym2.mem_mk_left u v⟩
      · exact ⟨v, Finset.mem_erase.mpr ⟨h1.2.2, hv⟩, Sym2.mem_mk_right u v⟩
    have hnd' : ∀ e ∈ G'.edgeFinset, ¬e.IsDiag := by
      intro e he
      exact G'.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
    have hbE := hbld_edges T' G'.edgeFinset hG'ne hnd' hcov'
    have hfun_eq : ∀ x : Fin n → Bool,
        f (Function.update x z false) =
          (decide (∃ a ∈ A, x a = true) || decide (∃ e ∈ G'.edgeFinset, ∀ v ∈ e, x v = true)) := by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [hf_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        rcases h with ⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩
        · have haz : a ≠ z := fun he => hzA (he ▸ ha)
          rw [Function.update_of_ne haz] at hxa
          exact Or.inl ⟨a, ha, hxa⟩
        · have huz : u ≠ z := by intro he; rw [he, Function.update_self] at hxu; exact Bool.false_ne_true hxu
          have hvz : v ≠ z := by intro he; rw [he, Function.update_self] at hxv; exact Bool.false_ne_true hxv
          rw [Function.update_of_ne huz] at hxu
          rw [Function.update_of_ne hvz] at hxv
          refine Or.inr ⟨s(u, v), ?_, ?_⟩
          · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact (hG'adj u v).mpr ⟨huv, huz, hvz⟩
          · intro y hy
            rcases Sym2.mem_iff.mp hy with rfl | rfl
            · exact hxu
            · exact hxv
      · intro h
        rcases h with ⟨a, ha, hxa⟩ | ⟨e, he, hxe⟩
        · have haz : a ≠ z := fun he => hzA (he ▸ ha)
          exact Or.inl ⟨a, ha, by rw [Function.update_of_ne haz]; exact hxa⟩
        · revert he hxe
          refine Sym2.ind (fun u v => ?_) e
          intro he hxe
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          have h1 := (hG'adj u v).mp he
          exact Or.inr ⟨u, v, h1.1,
            by rw [Function.update_of_ne h1.2.1]; exact hxe u (Sym2.mem_mk_left u v),
            by rw [Function.update_of_ne h1.2.2]; exact hxe v (Sym2.mem_mk_right u v)⟩
    have hb_all : Bld (fun x => f (Function.update x z false))
        (A.card + G'.edgeFinset.card + T'.card - 1) := by
      by_cases hA : A.Nonempty
      · have hbA := hbld_orFinset A hA
        have horA := hbld_bin PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl) _ _ _ _ hbA hbE
        have hAp : 0 < A.card := hA.card_pos
        have hEp : 0 < G'.edgeFinset.card := hG'ne.card_pos
        refine hbld_congr _ _ _ (hbld_mono _ _ _ horA (by omega)) (fun x => ?_)
        rw [hor_eval, ← hfun_eq x]
      · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
        refine hbld_congr _ _ _ (hbld_mono _ _ _ hbE (by simp [hAe])) (fun x => ?_)
        rw [hfun_eq x, hAe]; simp
    refine ⟨z, hzA, A.card + G'.edgeFinset.card + T'.card - 1, ?_, hbld_hasSize _ _ hb_all⟩
    omega
  -- Part 3: If some cover T satisfies the bound, solve immediately.
  by_cases hcov_small : ∃ T : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      A.card + G.edgeFinset.card + T.card ≤ C.size + 1
  · rcases hcov_small with ⟨T, hcov, hle⟩
    exact hcover_solve T hcov hle
  have htight : ∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
      C.size + 1 < A.card + G.edgeFinset.card + T.card := by
    intro T hcov
    have hnot_le : ¬ (A.card + G.edgeFinset.card + T.card ≤ C.size + 1) :=
      fun hle => hcov_small ⟨T, hcov, hle⟩
    omega
  -- Part 4: Slot counting proves A.card + 2 * Aᶜ.card ≤ C.size + 1, ruling out G.Colorable 2.
  have hnot_bip : ¬ G.Colorable 2 := by
    intro hcol
    rcases hcol with ⟨col⟩
    let L : Finset (Fin n) := Aᶜ.filter (fun v => col v = 0)
    let R : Finset (Fin n) := Aᶜ.filter (fun v => col v = 1)
    have hLR_sum : L.card + R.card = Aᶜ.card := by
      have hdisj : Disjoint L R := by
        rw [Finset.disjoint_left]
        intro v hvL hvR
        have h0 := (Finset.mem_filter.mp hvL).2
        have h1 := (Finset.mem_filter.mp hvR).2
        rw [h0] at h1
        exact absurd h1 (by decide)
      have hunion : L ∪ R = Aᶜ := by
        ext v
        simp only [Finset.mem_union, Finset.mem_filter, L, R]
        constructor
        · intro h; rcases h with ⟨hv, _⟩ | ⟨hv, _⟩ <;> exact hv
        · intro hv
          have hcv := (col v).isLt
          have h01 : col v = 0 ∨ col v = 1 := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hcv with hlt | heq
            · left; exact Fin.ext (Nat.lt_one_iff.mp hlt)
            · right; exact Fin.ext heq
          rcases h01 with h0 | h1
          · exact Or.inl ⟨hv, h0⟩
          · exact Or.inr ⟨hv, h1⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hcovL : ∀ u v : Fin n, G.Adj u v → u ∈ L ∨ v ∈ L := by
      intro u v huv
      have huA : u ∈ Aᶜ := Finset.mem_compl.mpr (hnoA u v huv)
      have hvA : v ∈ Aᶜ := Finset.mem_compl.mpr (hnoA v u huv.symm)
      have hne : col u ≠ col v := col.valid huv
      have hcu : col u = 0 ∨ col u = 1 := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (col u).isLt with hlt | heq
        · left; exact Fin.ext (Nat.lt_one_iff.mp hlt)
        · right; exact Fin.ext heq
      have hcv : col v = 0 ∨ col v = 1 := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (col v).isLt with hlt | heq
        · left; exact Fin.ext (Nat.lt_one_iff.mp hlt)
        · right; exact Fin.ext heq
      rcases hcu with hu0 | hu1
      · exact Or.inl (Finset.mem_filter.mpr ⟨huA, hu0⟩)
      · rcases hcv with hv0 | hv1
        · exact Or.inr (Finset.mem_filter.mpr ⟨hvA, hv0⟩)
        · exact absurd (hu1.trans hv1.symm) hne
    have hcovR : ∀ u v : Fin n, G.Adj u v → u ∈ R ∨ v ∈ R := by
      intro u v huv
      have huA : u ∈ Aᶜ := Finset.mem_compl.mpr (hnoA u v huv)
      have hvA : v ∈ Aᶜ := Finset.mem_compl.mpr (hnoA v u huv.symm)
      have hne : col u ≠ col v := col.valid huv
      have hcu : col u = 0 ∨ col u = 1 := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (col u).isLt with hlt | heq
        · left; exact Fin.ext (Nat.lt_one_iff.mp hlt)
        · right; exact Fin.ext heq
      have hcv : col v = 0 ∨ col v = 1 := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (col v).isLt with hlt | heq
        · left; exact Fin.ext (Nat.lt_one_iff.mp hlt)
        · right; exact Fin.ext heq
      rcases hcu with hu0 | hu1
      · rcases hcv with hv0 | hv1
        · exact absurd (hu0.trans hv0.symm) hne
        · exact Or.inr (Finset.mem_filter.mpr ⟨hvA, hv1⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨huA, hu1⟩)
    -- Slot counting on C:
    let slots : List ℕ := C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
    let cnt : ℕ → ℕ := fun i => slots.count i
    have hwires_agree : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (b : ℕ)
        (w1 w2 : List Bool), w1.length = w2.length → b < w1.length →
        (∀ i, i ≠ b → w1.getD i false = w2.getD i false) →
        (∀ g ∈ gs, b ∉ g.inputs) →
        (runW gs w1).length = (runW gs w2).length ∧
        ∀ i, i ≠ b → (runW gs w1).getD i false = (runW gs w2).getD i false := by
      intro gs
      induction gs with
      | nil => intro b w1 w2 hl _ ha _; exact ⟨hl, ha⟩
      | cons g gs ih =>
        intro b w1 w2 hl hb ha hno
        rw [hrun_cons, hrun_cons]
        have hmap : (g.inputs.map (fun i => w1.getD i false)) =
            (g.inputs.map (fun i => w2.getD i false)) := by
          apply List.map_congr_left
          intro i hi
          exact ha i (fun he => hno g List.mem_cons_self (he ▸ hi))
        apply ih b (step w1 g) (step w2 g)
        · simp [step, hl]
        · simp [step]; omega
        · intro i hib
          dsimp only [step]
          rw [hmap]
          by_cases hlt : i < w1.length
          · rw [hgetD_snoc_lt w1 _ i hlt, hgetD_snoc_lt w2 _ i (by omega)]
            exact ha i hib
          · by_cases heq : i = w1.length
            · subst heq
              rw [hgetD_snoc_eq w1, hl, hgetD_snoc_eq w2]
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)]
        · intro g' hg'; exact hno g' (List.mem_cons_of_mem g hg')
    have hmarked : ∀ a ∈ A, 1 ≤ cnt a.val := by
      intro a ha
      apply List.count_pos_iff.mpr
      by_contra hns
      have hout : C.output ≠ a.val := fun he => hns (by simp [slots, he])
      have hno : ∀ g ∈ C.gates, a.val ∉ g.inputs := fun g hg hi =>
        hns (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))
      let z0 : Fin n → Bool := fun _ => false
      let y0 : Fin n → Bool := fun i => decide (i = a)
      have hagr := (hwires_agree C.gates a.val (List.ofFn z0) (List.ofFn y0)
        (by simp) (by simp) (by
          intro i hia
          by_cases hi : i < n
          · rw [hofFn_getD z0 i hi, hofFn_getD y0 i hi]
            have hne : (⟨i, hi⟩ : Fin n) ≠ a := fun he => hia (congrArg Fin.val he)
            simp [z0, y0, hne]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]) hno).2 C.output hout
      have hcz : f z0 = (runW C.gates (List.ofFn z0)).getD C.output false := by
        rw [← hcircuitFun_eq C z0, heval]
      have hcy : f y0 = (runW C.gates (List.ofFn y0)).getD C.output false := by
        rw [← hcircuitFun_eq C y0, heval]
      have hfz : f z0 ≠ true := by
        intro ht
        rcases (hf_iff z0).mp ht with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> exact Bool.false_ne_true h
      have hfy : f y0 = true := (hf_iff y0).mpr (Or.inl ⟨a, ha, by simp [y0]⟩)
      exact hfz ((hcz.trans hagr).trans hcy.symm |>.trans hfy)
    have hfiltered : ∀ (v : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (gs.filter (fun g =>
          (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v)).length ≤
        (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v := by
      intro v gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons, List.count_append, List.filter_cons]
        split
        next h =>
          have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
          have hp := List.count_pos_iff.mpr hm
          simp only [List.length_cons]
          omega
        next => omega
    have hunmarked : ∀ v ∈ Aᶜ, 2 ≤ cnt v.val := by
      intro v hv
      have h2 := (hread v (Finset.mem_compl.mp hv)).1
      have h1 := hfiltered v.val C.gates
      simp only [cnt, slots, List.count_cons]
      omega
    have hinternal : ∀ i ∈ Finset.range C.gates.length, 1 ≤ cnt (n + i) := by
      intro i hi
      have hilt : i < C.gates.length := Finset.mem_range.mp hi
      apply List.count_pos_iff.mpr
      by_contra hns
      have hout : C.output ≠ n + i := fun he => hns (by simp [slots, he])
      have hno : ∀ g ∈ C.gates, n + i ∉ g.inputs := fun g hg hm =>
        hns (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hm⟩))
      -- Delete dead gate i by shifting all wire indices > n + i down by 1.
      let del : ℕ → ℕ := fun j => if j < n + i then j else j - 1
      let delG : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
        ⟨g.op, g.inputs.map del⟩
      let gs1 := C.gates.take i
      let gs2 := C.gates.drop (i + 1)
      let gs' := gs1 ++ gs2.map delG
      have hsplit : C.gates = gs1 ++ C.gates[i] :: gs2 := by
        have h1 := (List.take_append_drop i C.gates).symm
        rw [List.drop_eq_getElem_cons hilt] at h1
        exact h1
      have hdel_sim : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
          w1.length = w2.length + 1 → n + i < w1.length →
          (∀ j, j ≠ n + i → j < w1.length → w2.getD (del j) false = w1.getD j false) →
          (∀ g ∈ gs, n + i ∉ g.inputs) →
          (runW gs w1).length = (runW (gs.map delG) w2).length + 1 ∧
          (∀ j, j ≠ n + i → j < (runW gs w1).length →
            (runW (gs.map delG) w2).getD (del j) false = (runW gs w1).getD j false) := by
        intro gs
        induction gs with
        | nil => intro w1 w2 hl _ ha _; exact ⟨hl, ha⟩
        | cons g gs ih =>
          intro w1 w2 hl hni ha hnog
          rw [List.map_cons, hrun_cons, hrun_cons]
          have hmap : ((delG g).inputs.map (fun j => w2.getD j false)) =
              (g.inputs.map (fun j => w1.getD j false)) := by
            change ((g.inputs.map del).map (fun j => w2.getD j false)) = _
            rw [List.map_map]
            apply List.map_congr_left
            intro j hj
            change w2.getD (del j) false = w1.getD j false
            have hjne : j ≠ n + i := fun he => hnog g List.mem_cons_self (he ▸ hj)
            by_cases hlt : j < w1.length
            · exact ha j hjne hlt
            · have hdj : w2.length ≤ del j := by dsimp only [del]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hdj, List.getD_eq_default _ _ (by omega)]
          have hval : (delG g).op.eval ((delG g).inputs.map (fun j => w2.getD j false)) =
              g.op.eval (g.inputs.map (fun j => w1.getD j false)) :=
            congrArg g.op.eval hmap
          apply ih (step w1 g) (step w2 (delG g))
          · simp [step, hl]
          · simp [step]; omega
          · intro j hjne hjlt
            simp only [step, List.length_append, List.length_singleton] at hjlt
            by_cases hlt : j < w1.length
            · have hdj : del j < w2.length := by dsimp only [del]; split_ifs <;> omega
              rw [hgetD_snoc_lt w2 _ (del j) hdj, hgetD_snoc_lt w1 _ j hlt]
              exact ha j hjne hlt
            · have heq : j = w1.length := by omega
              subst heq
              have hdj : del w1.length = w2.length := by
                dsimp only [del]
                have hnot : ¬ w1.length < n + i := by omega
                rw [if_neg hnot]; omega
              dsimp only [step]
              rw [hdj, hgetD_snoc_eq, hgetD_snoc_eq, hval]
          · intro g' hg'; exact hnog g' (List.mem_cons_of_mem g hg')
      have hsmall : PEqualNP.MetaComplexity.HasCircuitSize n f (C.gates.length - 1) := by
        refine ⟨⟨gs', del C.output⟩, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.mp hg with hg1 | hg2
          · exact hfan g (List.mem_of_mem_take hg1)
          · rcases List.mem_map.mp hg2 with ⟨g0, hg0, rfl⟩
            have h0 := hfan g0 (List.mem_of_mem_drop hg0)
            exact ⟨h0.1, by simp [delG, h0.2]⟩
        · change gs'.length ≤ C.gates.length - 1
          simp only [gs', gs1, gs2, List.length_append, List.length_take, List.length_map,
            List.length_drop]
          omega
        · intro x
          have hlen1 : (runW gs1 (List.ofFn x)).length = n + i := by
            rw [hrun_len, List.length_ofFn, List.length_take, min_eq_left (Nat.le_of_lt hilt)]
          have hsim := hdel_sim gs2 (step (runW gs1 (List.ofFn x)) C.gates[i])
            (runW gs1 (List.ofFn x)) (by simp [step]) (by simp [step, hlen1])
            (by
              intro j hjne hjlt
              simp only [step, List.length_append, List.length_singleton, hlen1] at hjlt
              have hjlt' : j < n + i := by omega
              have hdj : del j = j := if_pos hjlt'
              rw [hdj]
              dsimp only [step]
              rw [hgetD_snoc_lt _ _ j (by rw [hlen1]; exact hjlt')])
            (fun g hg => hno g (List.mem_of_mem_drop hg))
          have hCeq : runW C.gates (List.ofFn x) =
              runW gs2 (step (runW gs1 (List.ofFn x)) C.gates[i]) := by
            conv_lhs => rw [hsplit]
            rw [hrun_append, hrun_cons]
          have hgeq : runW gs' (List.ofFn x) = runW (gs2.map delG) (runW gs1 (List.ofFn x)) := by
            dsimp only [gs']; rw [hrun_append]
          change (runW gs' (List.ofFn x)).getD (del C.output) false = f x
          dsimp only [f]
          rw [← heval, hcircuitFun_eq C x, hgeq, hCeq]
          by_cases hlt : C.output < (runW gs2 (step (runW gs1 (List.ofFn x)) C.gates[i])).length
          · exact hsim.2 C.output hout hlt
          · have hdo : (runW (gs2.map delG) (runW gs1 (List.ofFn x))).length ≤ del C.output := by
              have h1 := hsim.1
              have hni : n + i < (runW gs2 (step (runW gs1 (List.ofFn x)) C.gates[i])).length := by
                rw [hrun_len]; simp [step, hlen1]; omega
              dsimp only [del]; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hdo, List.getD_eq_default _ _ (by omega)]
      have hbad := hmin (C.gates.length - 1) hsmall
      rw [hsize_eq C] at hbad
      omega
    have hcount_bound : ∀ (xs : List ℕ) (S : Finset ℕ), ∑ i ∈ S, xs.count i ≤ xs.length := by
      intro xs
      induction xs with
      | nil => intro S; simp
      | cons a xs ih =>
        intro S
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        have h0 := ih S
        by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega
    have hslot_len : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤
        2 * C.gates.length := by
      have haux : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
          (∀ g ∈ gs, g.inputs.length ≤ 2) →
          (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 * gs.length := by
        intro gs
        induction gs with
        | nil => intro _; simp
        | cons g gs ih =>
          intro h
          have h1 := h g List.mem_cons_self
          have h2 := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
      exact haux C.gates (fun g hg => (hfan g hg).2)
    have hlowA := Finset.sum_le_sum hmarked
    have hlowB := Finset.sum_le_sum hunmarked
    have hlowI := Finset.sum_le_sum hinternal
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at hlowA hlowB hlowI
    have hinSum := A.sum_add_sum_compl (fun a : Fin n => cnt a.val)
    rw [Fin.sum_univ_eq_sum_range (fun i => cnt i)] at hinSum
    have hcb := hcount_bound slots (Finset.range (n + C.gates.length))
    change ∑ i ∈ Finset.range (n + C.gates.length), cnt i ≤ slots.length at hcb
    rw [Finset.sum_range_add] at hcb
    simp only [slots, List.length_cons] at hcb
    have hslot_ineq : A.card + 2 * Aᶜ.card ≤ C.size + 1 := by
      rw [hsize_eq C]; omega
    -- Handshaking lemma: 3 * Aᶜ.card = 2 * G.edgeFinset.card.
    have hdA : ∀ a ∈ A, G.degree a = 0 := by
      intro a ha
      exact (G.degree_eq_zero a).mpr (fun j h => hnoA a j h ha)
    have hdB : ∀ a ∈ Aᶜ, G.degree a = 3 := by
      intro a ha
      rw [← G.ncard_neighborSet]
      exact hdeg a (Finset.mem_compl.mp ha)
    have hhand := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, Finset.sum_congr rfl hdA, Finset.sum_congr rfl hdB] at hhand
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at hhand
    by_cases hLR : L.card ≤ R.card
    · have hlt := htight L hcovL
      omega
    · have hlt := htight R hcovR
      omega
  -- Part 5: Split the tight non-bipartite residual into Monotone2 vs at least one NOT gate.
  by_cases hhasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact hnot n G A C hnot_bip htight hhasNot hdeg hgirth hnoA hedge hfan heval hmin hread hallOr htwo
  · have hM2 : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      have hf := hfan g hg
      refine ⟨?_, hf.2⟩
      have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.1
      rcases hop with h1 | h2 | h3
      · simp [h1]
      · simp [h2]
      · exact False.elim (hhasNot ⟨g, hg, h3⟩)
    exact hmono n G A C hnot_bip htight hM2 hdeg hgirth hnoA hedge hfan heval hmin hread hallOr htwo
