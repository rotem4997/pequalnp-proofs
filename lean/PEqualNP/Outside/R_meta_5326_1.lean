import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5326_1
    (leftJunk : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, u ∉ side (n := n) C a 0 ∧
          ∃ g ∈ junk G C, OrReaches n C (opnd C a 0) g ∧
            gateVal n C g (pairInput u u) = true ∧
            wireVal n C (opnd C a 1) (pairInput v v) = true)).card ≤ k * (C.size + 1))
    (rightJunk : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, u ∈ side (n := n) C a 0 ∧ v ∉ side (n := n) C a 1 ∧
          ∃ h ∈ junk G C, OrReaches n C (opnd C a 1) h ∧
            gateVal n C h (pairInput v v) = true)).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := leftJunk
  obtain ⟨k2, hk2⟩ := rightJunk
  refine ⟨k1 + k2, ?_⟩
  intro n G _ C hg hL hT
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have h1 := hk1 n G C hg hL hT
  have h2 := hk2 n G C hg hL hT
  obtain ⟨⟨hAO, _, _⟩, _, _⟩ := hL
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1
    rw [List.length_append, List.length_singleton]
  have step_getD_lt : ∀ (w : List Bool) (g : Gate) (i : ℕ), i < w.length →
      (step w g).getD i false = w.getD i false := by
    intro w g i hi
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false = w.getD i false
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have step_getD_self : ∀ (w : List Bool) (g : Gate),
      (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD w.length false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    rfl
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro w
      rw [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by rw [step_len]; omega)]
      exact step_getD_lt w g i hi
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl step w).getD i false else false) := by
    intro gs
    induction gs with
    | nil =>
      intro w j hj
      rw [List.length_nil] at hj
      exact (Nat.not_lt_zero j hj).elim
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (step w g) w.length (by rw [step_len]; omega),
          step_getD_self]
        rw [List.getElem_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hi),
            foldl_getD_lt gs (step w g) i (by rw [step_len]; omega), step_getD_lt w g i hi]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), getD_ge w i (Nat.le_of_not_lt hi)]
      | succ j =>
        have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
        have key := ih (step w g) j hj'
        rw [step_len] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        rw [List.getElem_cons_succ]
        change (gs.foldl step (step w g)).getD (w.length + (j + 1)) false = _
        rw [e]
        exact key
  -- OR closures
  have orStep_len : ∀ (cs : List (List ℕ)) (gt : Gate),
      (orStep n cs gt).length = cs.length + 1 := by
    intro cs gt
    change (cs ++ [cs.length :: (if gt.op = GateOp.or then
      (gt.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]).length = cs.length + 1
    rw [List.length_append, List.length_singleton]
  have orStep_getD_lt : ∀ (cs : List (List ℕ)) (gt : Gate) (i : ℕ), i < cs.length →
      (orStep n cs gt).getD i [] = cs.getD i [] := by
    intro cs gt i hi
    change (cs ++ [_]).getD i [] = cs.getD i []
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  have orStep_self : ∀ (cs : List (List ℕ)) (gt : Gate),
      (orStep n cs gt).getD cs.length [] =
        cs.length :: (if gt.op = GateOp.or then
          (gt.inputs.filter (fun i => decide (n ≤ i ∧ i < n + cs.length))).flatMap
            (fun i => cs.getD (i - n) [])
          else []) := by
    intro cs gt
    change (cs ++ [_]).getD cs.length [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  have ofold_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons, ih (orStep n cs g) i (by rw [orStep_len]; omega)]
      exact orStep_getD_lt cs g i hi
  have flatMap_congr' : ∀ (L : List ℕ) (f1 f2 : ℕ → List ℕ), (∀ w ∈ L, f1 w = f2 w) →
      L.flatMap f1 = L.flatMap f2 := by
    intro L
    induction L with
    | nil => intro f1 f2 _; rfl
    | cons a L ih =>
      intro f1 f2 hf
      rw [List.flatMap_cons, List.flatMap_cons, hf a List.mem_cons_self,
        ih f1 f2 (fun w hw => hf w (List.mem_cons_of_mem a hw))]
  have ofold_gate : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (orStep n) cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if (gs[j]).op = GateOp.or then
          ((gs[j]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) cs).getD (w - n) [])
          else []) := by
    intro gs
    induction gs with
    | nil =>
      intro cs j hj
      rw [List.length_nil] at hj
      exact (Nat.not_lt_zero j hj).elim
    | cons g gs ih =>
      intro cs j hj
      cases j with
      | zero =>
        rw [List.foldl_cons, Nat.add_zero,
          ofold_getD_lt gs (orStep n cs g) cs.length (by rw [orStep_len]; omega),
          orStep_self, List.getElem_cons_zero]
        congr 1
        split_ifs with hop
        · apply flatMap_congr'
          intro w hw
          rw [List.mem_filter, decide_eq_true_eq] at hw
          rw [ofold_getD_lt gs (orStep n cs g) (w - n) (by rw [orStep_len]; omega),
            orStep_getD_lt cs g (w - n) (by omega)]
        · rfl
      | succ j =>
        have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
        have key := ih (orStep n cs g) j hj'
        rw [orStep_len] at key
        have e : cs.length + (j + 1) = cs.length + 1 + j := by omega
        rw [List.foldl_cons, List.getElem_cons_succ, e]
        exact key
  have orSets_gate : ∀ k (hk : k < C.gates.length),
      (orSets n C).getD k [] =
        k :: (if (C.gates[k]).op = GateOp.or then
          ((C.gates[k]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (orSets n C).getD (w - n) [])
          else []) := by
    intro k hk
    have h := ofold_gate C.gates [] k hk
    rw [List.length_nil, Nat.zero_add] at h
    exact h
  have hge : ∀ k (hk : k < C.gates.length), gateAt C k = C.gates[k] := by
    intro k hk
    change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have orR_self : ∀ k, k < C.gates.length → OrReaches n C (n + k) k := by
    intro k hk
    refine ⟨Nat.le_add_right n k, ?_⟩
    rw [show n + k - n = k by omega, orSets_gate k hk]
    exact List.mem_cons_self
  have or_trans : ∀ k k' g, k < C.gates.length → (gateAt C k).op = GateOp.or →
      n + k' ∈ (gateAt C k).inputs → k' < k →
      OrReaches n C (n + k') g → OrReaches n C (n + k) g := by
    intro k k' g hk hop hin hk' hor
    obtain ⟨_, hmem⟩ := hor
    rw [show n + k' - n = k' by omega] at hmem
    refine ⟨Nat.le_add_right n k, ?_⟩
    rw [show n + k - n = k by omega, orSets_gate k hk]
    rw [hge k hk] at hop hin
    rw [ite_eq_left_of_eq_true _ _ (eq_true hop)]
    apply List.mem_cons_of_mem
    rw [List.mem_flatMap]
    refine ⟨n + k', ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hin, Nat.le_add_right n k', by omega⟩
    · rw [show n + k' - n = k' by omega]
      exact hmem
  have no_self_graphFun : ∀ u : Fin n, graphFun G ∅ (pairInput u u) = false := by
    intro u
    rw [Bool.eq_false_iff]
    intro h
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u u a = true) ||
      decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u u a = true ∧ pairInput u u b = true)) = true at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
    · exact (Finset.notMem_empty a ha).elim
    · change decide (a = u ∨ a = u) = true at ha
      change decide (b = u ∨ b = u) = true at hb
      rw [decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact G.irrefl hab
  have input_case : ∀ (u : Fin n) (i : ℕ), i < n →
      wireVal n C i (pairInput u u) = true → (u : ℕ) = i := by
    intro u i hi hw
    change (C.gates.foldl step (List.ofFn (pairInput u u))).getD i false = true at hw
    rw [foldl_getD_lt C.gates _ i (by rw [List.length_ofFn]; exact hi),
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn] at hw
    change decide (_ = u ∨ _ = u) = true at hw
    rw [decide_eq_true_eq, or_self] at hw
    rw [← hw]
  have key : ∀ (u : Fin n) (w : ℕ), wireVal n C w (pairInput u u) = true →
      u ∈ orIn n C w ∨ ∃ g ∈ junk G C, OrReaches n C w g ∧ gateVal n C g (pairInput u u) = true := by
    intro u w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwn : w < n
      · left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inl (input_case u w hwn hw)⟩
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        by_cases hk : k < C.gates.length
        · have hlenx : (List.ofFn (pairInput u u)).length = n := List.length_ofFn
          have hgate := foldl_getD_gate C.gates (List.ofFn (pairInput u u)) k hk
          rw [hlenx] at hgate
          have hw' : (C.gates.foldl step (List.ofFn (pairInput u u))).getD (n + k) false = true := hw
          rw [hgate] at hw'
          rcases hAO (C.gates[k]) (List.getElem_mem hk) with hop | hop
          · right
            refine ⟨k, ?_, orR_self k hk, hw⟩
            have hopk : (gateAt C k).op = GateOp.and := by rw [hge k hk]; exact hop
            show k ∈ (Finset.range C.gates.length).filter (fun j => IsDirtyAnd n G C j)
            refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩
            show (gateAt C k).op = GateOp.and ∧ IsDirty n G C k
            exact ⟨hopk, hk, pairInput u u, hw, no_self_graphFun u⟩
          · rw [hop] at hw'
            change ((C.gates[k]).inputs.map fun i =>
              if i < n + k then (C.gates.foldl step (List.ofFn (pairInput u u))).getD i false
              else false).any id = true at hw'
            rw [List.any_map, List.any_eq_true] at hw'
            obtain ⟨i, hi_in, hiv⟩ := hw'
            have hilt : i < n + k := by
              by_contra hc
              rw [Function.comp_apply, ite_eq_right_of_eq_false _ _ (eq_false hc)] at hiv
              cases hiv
            rw [Function.comp_apply, ite_eq_left_of_eq_true _ _ (eq_true hilt)] at hiv
            have hiw : wireVal n C i (pairInput u u) = true := hiv
            have hopk : (gateAt C k).op = GateOp.or := by rw [hge k hk]; exact hop
            have hin : i ∈ (gateAt C k).inputs := by rw [hge k hk]; exact hi_in
            by_cases hin_n : i < n
            · left
              have hui := input_case u i hin_n hiw
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inr ⟨k, hk, orR_self k hk, hopk, ?_⟩⟩
              rw [hui]
              exact hin
            · obtain ⟨k', rfl⟩ : ∃ k', i = n + k' := ⟨i - n, by omega⟩
              have hk' : k' < k := by omega
              rcases ih (n + k') hilt hiw with hmem | ⟨g, hg, hor, hgv⟩
              · left
                obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hmem
                rcases hmem with heq | ⟨k'', hk'', hor'', hop'', hin''⟩
                · exfalso
                  have := u.isLt
                  omega
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Or.inr ⟨k'', hk'',
                    or_trans k k' k'' hk hopk hin hk' hor'', hop'', hin''⟩⟩
              · right
                exact ⟨g, hg, or_trans k k' g hk hopk hin hk' hor, hgv⟩
        · exfalso
          have hlen := foldl_len C.gates (List.ofFn (pairInput u u))
          rw [List.length_ofFn] at hlen
          have hw' : (C.gates.foldl step (List.ofFn (pairInput u u))).getD (n + k) false = true := hw
          rw [getD_ge _ _ (by omega)] at hw'
          cases hw'
  classical
  let S := {x9 ∈ Ustar G C | ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
    ∃ x12 ∈ tops G C, wireVal n C (opnd C x12 0) (pairInput x10 x10) = true ∧
      wireVal n C (opnd C x12 1) (pairInput x11 x11) = true}
  let S1 := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, u ∉ side (n := n) C a 0 ∧
          ∃ g ∈ junk G C, OrReaches n C (opnd C a 0) g ∧
            gateVal n C g (pairInput u u) = true ∧
            wireVal n C (opnd C a 1) (pairInput v v) = true)
  let S2 := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, u ∈ side (n := n) C a 0 ∧ v ∉ side (n := n) C a 1 ∧
          ∃ h ∈ junk G C, OrReaches n C (opnd C a 1) h ∧
            gateVal n C h (pairInput v v) = true)
  have hsub : S ⊆ S1 ∪ S2 := by
    intro e he
    obtain ⟨heU, u, v, rfl, a, ha, h0, h1v⟩ := Finset.mem_filter.mp he
    have heU' : s(u, v) ∈ G.edgeFinset \ starEdges G C := heU
    have hns : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.mp heU').2
    by_cases hu : u ∈ side (n := n) C a 0
    · have hv : v ∉ side (n := n) C a 1 := by
        intro hv
        apply hns
        exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
      rcases key v (opnd C a 1) h1v with hm | ⟨h, hh, hor, hhv⟩
      · exact (hv hm).elim
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨heU, u, v, rfl, a, ha, hu, hv, h, hh, hor, hhv⟩)
    · rcases key u (opnd C a 0) h0 with hm | ⟨g, hg, hor, hgu⟩
      · exact (hu hm).elim
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨heU, u, v, rfl, a, ha, hu, g, hg, hor, hgu, h1v⟩)
  have hcard : S.card ≤ S1.card + S2.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  change S.card ≤ (k1 + k2) * (C.size + 1)
  have hs1 : S1.card ≤ k1 * (C.size + 1) := h1
  have hs2 : S2.card ≤ k2 * (C.size + 1) := h2
  rw [Nat.add_mul]
  exact hcard.trans (Nat.add_le_add hs1 hs2)
