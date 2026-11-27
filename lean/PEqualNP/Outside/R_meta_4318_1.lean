import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_4318_1
  (norm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    G.edgeFinset.Nonempty → IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    (∀ k < C.size, (gateAt C k).op = GateOp.and →
      ∀ v : Fin n, gateVal n C k (pairInput v v) = false) →
    ∃ C' : Circuit, IsLeastAO G C' ∧ TopForm G C' ∧ C'.size = C.size ∧
      ∀ k < C'.size, (gateAt C' k).op = GateOp.and →
        ∀ v : Fin n, gateVal n C' k (pairInput v v) = false)
  (budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
    G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
      (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
      K.card ≤ (tops G C \ centreless G C).card)
  (oneJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
    NoFourCycle G → G.edgeFinset.Nonempty →
    ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    (∀ k < C.size, (gateAt C k).op = GateOp.and →
      ∀ v : Fin n, gateVal n C k (pairInput v v) = false) →
    (junk G C).card = 1 →
    2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
    ∃ K' : Finset (Fin n), (∀ e ∈ Ustar G C, ∃ v ∈ K', v ∈ e) ∧
      (Ustar G C).card + K'.card ≤
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
  (manyJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
    NoFourCycle G → G.edgeFinset.Nonempty →
    ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    IsLeastAO G C → TopForm G C →
    (∀ k < C.size, (gateAt C k).op = GateOp.and →
      ∀ v : Fin n, gateVal n C k (pairInput v v) = false) →
    2 ≤ (junk G C).card →
    2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ G.edgeFinset.card + S.card ≤ C.size + 1) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → x2.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x13 x13) = Bool.false) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x2.edgeFinset.card + x11.card ≤ x7.size + (1 : ℕ) := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  intro n G _ htri h4c hne C hmin hfun hclean
  have hno4 : NoFourCycle G := by
    intro a b hab
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hgt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
    rcases h4c a c b d hc.1 hc.2.symm hd.2 hd.1.symm with rfl | rfl
    · exact hab rfl
    · exact hcd rfl
  obtain ⟨C', hL', hTF', hsz, hclean'⟩ := norm n G C hne hmin hfun hclean
  have hfun' : circuitFun n C' = graphFun G ∅ := hL'.2.1
  have hmin' : IsMinimalMonoCircuit n C' := by
    refine ⟨fun g hg => ?_, fun D hD hDf => ?_⟩
    · refine ⟨?_, ?_⟩
      · rcases hL'.1.1 g hg with h | h <;> simp [h]
      · exact (hL'.1.2.2 g hg).le
    · rw [hsz]
      exact hmin.2 D hD (hDf.trans (hfun'.trans hfun.symm))
  obtain ⟨hs, hk⟩ := budget n G C' hno4 hne hL' hTF'
  let U := Ustar G C'
  let B := 2 * (centreless G C').card + (junk G C').card + (orN G C' \ lam G C').card
  have hmincov : ∃ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑U) K := by
    let H := G.deleteEdges (↑U)
    let P (m : ℕ) := ∃ K : Finset (Fin n), H.IsVertexCover (↑K) ∧ K.card = m
    have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
    refine ⟨K, hK, fun T hT => ?_⟩
    exact hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)
  by_cases loose : 2 * U.card ≤ B
  · obtain ⟨K, hK⟩ := hmincov
    have kt := hk K hK
    let X := U.image (fun e => e.out.1)
    have hx : X.card ≤ U.card := Finset.card_image_le
    refine ⟨K ∪ X, ?_, ?_⟩
    · intro u v huv
      by_cases eh : s(u, v) ∈ U
      · have hvx : s(u, v).out.1 ∈ X := Finset.mem_image_of_mem _ eh
        have hh := Sym2.out_fst_mem s(u, v)
        rw [Sym2.mem_iff] at hh
        rcases hh with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
      · have hh : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, eh⟩
        rcases hK.1 hh with h | h
        · exact Or.inl (Finset.mem_union_left X h)
        · exact Or.inr (Finset.mem_union_left X h)
    · have card := Finset.card_union_le K X
      dsimp only [U, B] at *
      omega
  · have hlt : B < 2 * U.card := Nat.lt_of_not_ge loose
    have hjne : junk G C' ≠ ∅ := by
      intro hjempty
      have huempty : U = ∅ := by
        by_contra hneU
        obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hneU
        revert he
        refine Sym2.ind (fun u v huv => ?_) e
        have huv' := huv
        dsimp only [U, Ustar] at huv
        rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
        obtain ⟨hadj, hns⟩ := huv
        let stepWire (w : List Bool) (g : Gate) : List Bool :=
          w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        have foldl_length : ∀ (gs : List Gate) (w : List Bool),
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
          | nil => intro _ _ _; rfl
          | cons g gs ih =>
            intro w i hi
            rw [List.foldl_cons, ih (stepWire w g) i (by simp [stepWire]; omega)]
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
          intro w i hi
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
        have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
            (gs.foldl stepWire w).getD (w.length + j) false =
              gs[j].op.eval (gs[j].inputs.map fun i =>
                if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
          intro gs
          induction gs with
          | nil => intro _ _ hj; simp at hj
          | cons g gs ih =>
            intro w j hj
            rw [List.foldl_cons]
            cases j with
            | zero =>
              have h1 : w.length < (stepWire w g).length := by simp [stepWire]
              rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
              have h2 : (stepWire w g).getD w.length false =
                  g.op.eval (g.inputs.map fun i => w.getD i false) := by
                simp [stepWire, List.getD_eq_getElem?_getD]
              rw [h2]
              congr 1
              apply List.map_congr_left
              intro i _
              by_cases hi : i < w.length
              · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
                simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
              · rw [if_neg hi]; exact getD_ge w i (by omega)
            | succ j =>
              have hj' : j < gs.length := by simpa using hj
              have key := ih (stepWire w g) j hj'
              have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
              rw [hl] at key
              have e1 : w.length + (j + 1) = w.length + 1 + j := by omega
              simp only [List.getElem_cons_succ]
              rw [e1]
              exact key
        let val (x : List Bool) (w : ℕ) : Bool := (C'.wires x).getD w false
        have val_input : ∀ (x : Fin n → Bool) (t : Fin n),
            val (List.ofFn x) t.val = x t := by
          intro x t
          show (C'.gates.foldl stepWire (List.ofFn x)).getD t.val false = x t
          rw [foldl_getD_lt _ _ _ (by simp)]
          simp [List.getD_eq_getElem?_getD]
        have val_ge : ∀ (x : Fin n → Bool) (w : ℕ), n + C'.gates.length ≤ w →
            val (List.ofFn x) w = false := by
          intro x w hw
          apply getD_ge
          show (C'.gates.foldl stepWire (List.ofFn x)).length ≤ w
          rw [foldl_length, List.length_ofFn]
          exact hw
        have gateAt_eq : ∀ {j : ℕ} (hj : j < C'.gates.length), gateAt C' j = C'.gates[j] := by
          intro j hj
          dsimp only [gateAt]
          simp [List.getD_eq_getElem?_getD, hj]
        have gateAt_mem : ∀ {j : ℕ}, j < C'.gates.length → gateAt C' j ∈ C'.gates := by
          intro j hj
          rw [gateAt_eq hj]
          exact List.getElem_mem hj
        have val_gate : ∀ (x : Fin n → Bool) {j : ℕ}, j < C'.gates.length →
            val (List.ofFn x) (n + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
              if i < n + j then val (List.ofFn x) i else false) := by
          intro x j hj
          rw [gateAt_eq hj]
          have h := foldl_getD_gate C'.gates (List.ofFn x) j hj
          rw [List.length_ofFn] at h
          exact h
        have val_or : ∀ (x : Fin n → Bool) {r : ℕ}, r < C'.gates.length →
            (gateAt C' r).op = GateOp.or →
            (val (List.ofFn x) (n + r) = true ↔
              ∃ i ∈ (gateAt C' r).inputs, i < n + r ∧ val (List.ofFn x) i = true) := by
          intro x r hr hop
          rw [val_gate x hr, hop]
          dsimp only [GateOp.eval]
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          constructor
          · rintro ⟨i, hi, h⟩
            by_cases hlt' : i < n + r
            · rw [if_pos hlt'] at h; exact ⟨i, hi, hlt', h⟩
            · rw [if_neg hlt'] at h; cases h
          · rintro ⟨i, hi, hlt', h⟩
            exact ⟨i, hi, by rw [if_pos hlt']; exact h⟩
        have val_and : ∀ (x : Fin n → Bool) {r : ℕ}, r < C'.gates.length →
            (gateAt C' r).op = GateOp.and →
            (val (List.ofFn x) (n + r) = true ↔
              ∀ i ∈ (gateAt C' r).inputs, i < n + r ∧ val (List.ofFn x) i = true) := by
          intro x r hr hop
          rw [val_gate x hr, hop]
          dsimp only [GateOp.eval]
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          constructor
          · intro h i hi
            have h' := h i hi
            by_cases hlt' : i < n + r
            · rw [if_pos hlt'] at h'; exact ⟨hlt', h'⟩
            · rw [if_neg hlt'] at h'; cases h'
          · intro h i hi
            rw [if_pos (h i hi).1]; exact (h i hi).2
        have graphFun_pair : ∀ a b : Fin n,
            graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
          intro a b
          dsimp only [graphFun, pairInput]
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
            Bool.false_or, decide_eq_true_eq]
          constructor
          · rintro ⟨c, d, hcd, hc, hd⟩
            rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
            · exact (G.irrefl hcd).elim
            · exact hcd
            · exact hcd.symm
            · exact (G.irrefl hcd).elim
          · intro h
            exact ⟨a, b, h, by simp, by simp⟩
        have hout : ∀ x : Fin n → Bool, val (List.ofFn x) C'.output = graphFun G ∅ x := by
          intro x
          exact congrFun hfun' x
        have below_trace : ∀ w : ℕ, val (List.ofFn (pairInput u v)) w = true →
            (∀ y : Fin n → Bool, val (List.ofFn y) w = true → graphFun G ∅ y = true) →
            ∃ a < C'.gates.length, (gateAt C' a).op = GateOp.and ∧ BelowF G C' a ∧
              val (List.ofFn (pairInput u v)) (n + a) = true := by
          intro w
          induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hvw hbelw
            by_cases hw : w < n
            · exfalso
              have h1 := hbelw (pairInput ⟨w, hw⟩ ⟨w, hw⟩) (by
                have vi := val_input (pairInput ⟨w, hw⟩ ⟨w, hw⟩) ⟨w, hw⟩
                dsimp only [pairInput] at vi
                simpa using vi)
              exact G.irrefl ((graphFun_pair _ _).mp h1)
            · by_cases hlen : n + C'.gates.length ≤ w
              · rw [val_ge _ _ hlen] at hvw; cases hvw
              · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
                have hk : k < C'.gates.length := by omega
                rcases hL'.1.1 _ (gateAt_mem hk) with hop | hop
                · exact ⟨k, hk, hop, hbelw, hvw⟩
                · obtain ⟨i, hin, hlti, hvi⟩ := (val_or (pairInput u v) hk hop).mp hvw
                  apply ih i hlti hvi
                  intro y hy
                  exact hbelw y ((val_or y hk hop).mpr ⟨i, hin, hlti, hy⟩)
        obtain ⟨a, ha, hopa, hbela, hvala⟩ :=
          below_trace C'.output (by rw [hout]; exact (graphFun_pair u v).mpr hadj)
            (fun y hy => by rw [← hout]; exact hy)
        have hatop : a ∈ tops G C' :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hopa, hbela⟩
        let OrStep (w1 w2 : ℕ) : Prop :=
          ∃ k < C'.gates.length, w1 = n + k ∧ (gateAt C' k).op = GateOp.or ∧
            w2 ∈ (gateAt C' k).inputs ∧ w2 < n + k
        have orStep_up : ∀ (x : Fin n → Bool) {w1 w2 : ℕ},
            Relation.ReflTransGen OrStep w1 w2 → val (List.ofFn x) w2 = true →
            val (List.ofFn x) w1 = true := by
          intro x w1 w2 hr hv
          induction hr using Relation.ReflTransGen.head_induction_on with
          | refl => exact hv
          | head hstep _ ih =>
            obtain ⟨k, hk, rfl, hop, hin, hlt'⟩ := hstep
            exact (val_or x hk hop).mpr ⟨_, hin, hlt', ih⟩
        have orStep_le : ∀ {w1 w2 : ℕ}, Relation.ReflTransGen OrStep w1 w2 → w2 ≤ w1 := by
          intro w1 w2 hr
          induction hr using Relation.ReflTransGen.head_induction_on with
          | refl => exact le_rfl
          | head hstep _ ih =>
            obtain ⟨k, _, rfl, _, _, hlt'⟩ := hstep
            omega
        have coneStep_eq : ∀ cs g, coneStep n cs g =
            cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
        have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
            (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro cs; simp
          | cons g gs ih =>
            intro cs
            rw [List.foldl_cons, ih, coneStep_eq]
            simp
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
            have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
              rw [cones_len]; simp
            have key : ∀ k, k < gs.length →
                (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
                  (gs.foldl (coneStep n) []).getD k [] := by
              intro k hk
              rw [coneStep_eq]
              simp only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by omega)]
            rcases Nat.lt_trichotomy j gs.length with h | h | h
            · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
                simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_left h]
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
                rw [coneStep_eq]
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
                rw [coneStep_eq]
                simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]
                rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩
                simp at h0
                omega
        have inCone_iff : ∀ i j : ℕ,
            InCone n C' i j ↔ j < C'.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C' j).inputs ∧
              (i = k ∨ InCone n C' i k) := by
          intro i j
          have h := cones_char C'.gates i j
          dsimp only [InCone, cones, gateAt]
          rw [h]
          constructor
          · rintro ⟨h0, w, hw, h1, h2, h3⟩
            refine ⟨h0, w - n, by omega, ?_, h3⟩
            have : n + (w - n) = w := by omega
            rw [this]
            exact hw
          · rintro ⟨h0, k, hk, hw, h3⟩
            refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
            have : n + k - n = k := by omega
            rw [this]
            exact h3
        have orStep_cone : ∀ {w1 w2 : ℕ}, Relation.ReflTransGen OrStep w1 w2 →
            ∀ k h', w1 = n + k → w2 = n + h' → h' = k ∨ InCone n C' h' k := by
          intro w1 w2 hr
          induction hr using Relation.ReflTransGen.head_induction_on with
          | refl => intro k h' h1 h2; left; omega
          | @head a1 c1 hstep hrest ih =>
            intro k h' h1 h2
            obtain ⟨k0, hk0, e, _, hin, hlt'⟩ := hstep
            have hk : k0 = k := by omega
            subst hk
            have hle := orStep_le hrest
            obtain ⟨k1, hk1⟩ : ∃ k1, c1 = n + k1 := ⟨c1 - n, by omega⟩
            subst hk1
            right
            rw [inCone_iff]
            exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
        have operand_cone : ∀ {p h : ℕ},
            p ∈ (gateAt C' a).inputs → p < n + a →
            Relation.ReflTransGen OrStep p (n + h) → InCone n C' h a := by
          intro p h hin hp hr
          have hle := orStep_le hr
          obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
          rw [inCone_iff]
          exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
        have orStep_eq : ∀ cs g, orStep n cs g =
            cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
              ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
                (fun w => cs.getD (w - n) [])) [])] := fun _ _ => rfl
        have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
            (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro cs; simp
          | cons g gs ih =>
            intro cs
            rw [List.foldl_cons, ih, orStep_eq]
            simp
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
            have hlen : (gs.foldl (orStep n) []).length = gs.length := by
              rw [orSets_len]; simp
            have key : ∀ k, k < gs.length →
                (orStep n (gs.foldl (orStep n) []) g).getD k [] =
                  (gs.foldl (orStep n) []).getD k [] := by
              intro k hk
              rw [orStep_eq]
              simp only [List.getD_eq_getElem?_getD]
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
                  rw [orStep_eq]
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
                  rw [orStep_eq]
                  simp only [List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega)]
                  simp [hlen, hop]
                rw [e2]
                simp only [List.mem_singleton]
                constructor
                · intro h3
                  exact ⟨by simp, Or.inl h3⟩
                · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
                  · exact h3
                  · exact (hop hop2).elim
            · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
                rw [orStep_eq]
                simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]
                rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩
                simp at h0
                omega
        have orReaches_iff : ∀ k g : ℕ,
            OrReaches n C' (n + k) g ↔ k < C'.gates.length ∧ (g = k ∨ ((gateAt C' k).op = GateOp.or ∧
              ∃ i ∈ (gateAt C' k).inputs, i < n + k ∧ OrReaches n C' i g)) := by
          intro k g
          have h := orSets_char C'.gates g k
          dsimp only [OrReaches, orSets, gateAt]
          have e : n + k - n = k := by omega
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
        have reach_orReaches : ∀ {w1 w2 : ℕ},
            Relation.ReflTransGen OrStep w1 w2 →
            ∀ g, w2 = n + g → g < C'.gates.length → OrReaches n C' w1 g := by
          intro w1 w2 hr
          induction hr using Relation.ReflTransGen.head_induction_on with
          | refl =>
            intro g h1 hg
            subst h1
            exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
          | @head a1 c1 hstep hrest ih =>
            intro g h1 hg
            obtain ⟨k, hk, rfl, hop, hin, hlt'⟩ := hstep
            exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c1, hin, hlt', ih g h1 hg⟩⟩
        have reach_mem_orIn : ∀ {p : ℕ} (t : Fin n),
            Relation.ReflTransGen OrStep p t.val → t ∈ orIn n C' p := by
          intro p t hr
          dsimp only [orIn]
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
          · exact Or.inl h
          · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
            exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
        have or_trace : ∀ w : ℕ, val (List.ofFn (pairInput u v)) w = true →
            ∃ w', Relation.ReflTransGen OrStep w w' ∧ val (List.ofFn (pairInput u v)) w' = true ∧
              (w' < n ∨ ∃ h, h < C'.gates.length ∧ w' = n + h ∧ (gateAt C' h).op ≠ GateOp.or) := by
          intro w
          induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hv
            by_cases hw : w < n
            · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
            · by_cases hlen : n + C'.gates.length ≤ w
              · rw [val_ge _ _ hlen] at hv; cases hv
              · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
                have hk : k < C'.gates.length := by omega
                by_cases hop : (gateAt C' k).op = GateOp.or
                · obtain ⟨i, hin, hlt', hi⟩ := (val_or (pairInput u v) hk hop).mp hv
                  obtain ⟨w', hr, hv', hw'⟩ := ih i hlt' hi
                  exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt'⟩ hr, hv', hw'⟩
                · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
        have operand_trace : ∀ p : ℕ, p ∈ (gateAt C' a).inputs → p < n + a →
            val (List.ofFn (pairInput u v)) p = true →
            ∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val := by
          intro p hpin hplt hvp
          obtain ⟨w', hr, hv', hw'⟩ := or_trace p hvp
          rcases hw' with hlt' | ⟨h, hh, rfl, hhor⟩
          · refine ⟨⟨w', hlt'⟩, ?_, hr⟩
            have h1 := val_input (pairInput u v) ⟨w', hlt'⟩
            rw [show (⟨w', hlt'⟩ : Fin n).val = w' from rfl, hv'] at h1
            dsimp only [pairInput] at h1
            simpa using h1.symm
          · exfalso
            have hhand : (gateAt C' h).op = GateOp.and := by
              rcases hL'.1.1 _ (gateAt_mem hh) with h3 | h3
              · exact h3
              · exact (hhor h3).elim
            have hcone : InCone n C' h a := operand_cone hpin hplt hr
            have hnb : ¬ BelowF G C' h := fun hb2 => hTF' h hh a ha hhand hb2 hopa hcone
            have hjunk : h ∈ junk G C' := by
              dsimp only [junk, gatesWhere]
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨hh, hhand, hh, ?_⟩
              by_contra hne2
              apply hnb
              intro y hy
              by_contra hfy
              exact hne2 ⟨y, hy, Bool.eq_false_iff.mpr hfy⟩
            rw [hjempty] at hjunk
            exact Finset.notMem_empty h hjunk
        obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hL'.1.2.2 _ (gateAt_mem ha))
        have e0 : opnd C' a 0 = p := by dsimp only [opnd]; rw [hin]; rfl
        have e1 : opnd C' a 1 = q := by dsimp only [opnd]; rw [hin]; rfl
        have hpq := (val_and (pairInput u v) ha hopa).mp hvala
        have hp := hpq p (by rw [hin]; simp)
        have hq := hpq q (by rw [hin]; simp)
        obtain ⟨t1, ht1, hr1⟩ := operand_trace p (by rw [hin]; simp) hp.1 hp.2
        obtain ⟨t2, ht2, hr2⟩ := operand_trace q (by rw [hin]; simp) hq.1 hq.2
        have hadj12 : G.Adj t1 t2 := by
          apply (graphFun_pair t1 t2).mp
          apply hbela (pairInput t1 t2)
          show val (List.ofFn (pairInput t1 t2)) (n + a) = true
          rw [val_and (pairInput t1 t2) ha hopa, hin]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨hp.1, orStep_up (pairInput t1 t2) hr1 (by rw [val_input]; dsimp only [pairInput]; simp)⟩
          · exact ⟨hq.1, orStep_up (pairInput t1 t2) hr2 (by rw [val_input]; dsimp only [pairInput]; simp)⟩
        have hne12 : t1 ≠ t2 := G.ne_of_adj hadj12
        have hs' : s(u, v) = s(t1, t2) := by
          rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
          · exact (hne12 (h1.trans h2.symm)).elim
          · rw [h1, h2]
          · rw [h1, h2]; exact Sym2.eq_swap
          · exact (hne12 (h1.trans h2.symm)).elim
        apply hns
        rw [hs']
        dsimp only [starEdges]
        rw [Finset.mem_biUnion]
        refine ⟨a, hatop, Finset.mem_image.mpr ⟨(t1, t2), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩⟩
        · dsimp only [side]; rw [e0]; exact reach_mem_orIn t1 hr1
        · dsimp only [side]; rw [e1]; exact reach_mem_orIn t2 hr2
      rw [huempty, Finset.card_empty] at hlt
      omega
    have hjpos : 1 ≤ (junk G C').card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hjne)
    by_cases hj1 : (junk G C').card = 1
    · obtain ⟨K', hcov', hbud'⟩ := oneJunk n G htri hno4 hne C' hL' hTF' hclean' hj1 hlt
      obtain ⟨K, hK⟩ := hmincov
      have kt := hk K hK
      refine ⟨K ∪ K', ?_, ?_⟩
      · intro u v huv
        by_cases eh : s(u, v) ∈ U
        · obtain ⟨w, hwK', hwe⟩ := hcov' s(u, v) eh
          rw [Sym2.mem_iff] at hwe
          rcases hwe with rfl | rfl
          · exact Or.inl (Finset.mem_union_right _ hwK')
          · exact Or.inr (Finset.mem_union_right _ hwK')
        · have hh : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, eh⟩
          rcases hK.1 hh with h | h
          · exact Or.inl (Finset.mem_union_left K' h)
          · exact Or.inr (Finset.mem_union_left K' h)
      · have card := Finset.card_union_le K K'
        dsimp only [U, B] at *
        omega
    · have hj2 : 2 ≤ (junk G C').card := by omega
      obtain ⟨S, hS, hcard⟩ := manyJunk n G htri hno4 hne C' hmin' hfun' hL' hTF' hclean' hj2 hlt
      exact ⟨S, hS, by omega⟩
