import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2579_1
    (centrelessBound : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin 2),
          2 ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ centreless G C, e ∈ gammaE G C a}).card ≤ k * (C.size + 1))
    (oneSidedBound : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin 2),
          2 ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ tops G C \ centreless G C, e ∈ gammaE G C a ∧
          ∃ w ∈ side C a 0 ∪ side C a 1, w ∈ e}).card ≤ k * (C.size + 1))
    (twoSidedBound : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin 2),
          2 ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ tops G C \ centreless G C, e ∈ gammaE G C a ∧
          ∀ w ∈ side C a 0 ∪ side C a 1, w ∉ e}).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k1, hk1⟩ := centrelessBound
  obtain ⟨k2, hk2⟩ := oneSidedBound
  obtain ⟨k3, hk3⟩ := twoSidedBound
  refine ⟨k1 + k2 + k3, ?_⟩
  intro n G _ hgirth hne C hleast htop
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have step_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gate_eval (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl step w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl step w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, step_lt gs (step w g) w.length (by simp [step])]
        have hlast : (step w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [step, List.getD_eq_getElem?_getD]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, step_lt gs (step w g) i (by simp [step]; omega)]
          simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
      | succ j =>
        have key := ih (step w g) j (by simpa using hj)
        have hl : (step w g).length = w.length + 1 := by simp [step]
        rw [hl] at key
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using key
  have wire_input (x : Fin n → Bool) (i : Fin n) :
      (C.wires (List.ofFn x)).getD i.val false = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
    rw [step_lt C.gates (List.ofFn x) i.val (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have wire_beyond (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
      (C.wires (List.ofFn x)).getD w false = false := by
    change (C.gates.foldl step (List.ofFn x)).getD w false = false
    have hlen : (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length := by
      rw [step_len]; simp
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl step (List.ofFn x)).length ≤ w)]
  have graphFun_single (i : Fin n) : graphFun G ∅ (pairInput i i) = false := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a = i ∨ a = i) = true) ||
      decide (∃ u v, G.Adj u v ∧ decide (u = i ∨ u = i) = true ∧ decide (v = i ∨ v = i) = true)) = false
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = i := (of_decide_eq_true hu).elim id id
    have hv' : v = i := (of_decide_eq_true hv).elim id id
    rw [hu', hv'] at huv
    exact G.loopless.irrefl i huv
  have top_cover (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
      ∃ a ∈ tops G C, e ∈ gammaE G C a := by
    induction e using Sym2.ind with | _ u v =>
    have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have hfun : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD C.output false = graphFun G ∅ x := by
      intro x
      exact congrFun hleast.2.1 x
    have hout_ge : n ≤ C.output := by
      by_contra hlt
      push Not at hlt
      let i : Fin n := ⟨C.output, hlt⟩
      have h1 := hfun (pairInput i i)
      rw [wire_input (pairInput i i) i, graphFun_single i] at h1
      change decide (i = i ∨ i = i) = false at h1
      simp at h1
    have hout_lt : C.output < n + C.gates.length := by
      by_contra hge
      push Not at hge
      have h1 := hfun (pairInput u v)
      rw [wire_beyond (pairInput u v) C.output hge] at h1
      have hgf : graphFun G ∅ (pairInput u v) = true := by
        change (decide _ || decide (∃ a b, G.Adj a b ∧ decide (a = u ∨ a = v) = true ∧
          decide (b = u ∨ b = v) = true)) = true
        rw [Bool.or_eq_true]
        refine Or.inr (decide_eq_true ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩)
      rw [hgf] at h1
      contradiction
    have hex : ∃ j : ℕ, j < C.gates.length ∧ BelowF G C j ∧
        gateVal n C j (pairInput u v) = true := by
      refine ⟨C.output - n, by omega, ?_, ?_⟩
      · intro x hx
        have heq : n + (C.output - n) = C.output := by omega
        change (C.wires (List.ofFn x)).getD (n + (C.output - n)) false = true at hx
        rw [heq, hfun x] at hx
        exact hx
      · change (C.wires (List.ofFn (pairInput u v))).getD (n + (C.output - n)) false = true
        have heq : n + (C.output - n) = C.output := by omega
        rw [heq, hfun (pairInput u v)]
        change (decide _ || decide (∃ a b, G.Adj a b ∧ decide (a = u ∨ a = v) = true ∧
          decide (b = u ∨ b = v) = true)) = true
        rw [Bool.or_eq_true]
        refine Or.inr (decide_eq_true ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩)
    let j := Nat.find hex
    have hj_spec := Nat.find_spec hex
    have hj_min : ∀ j' < j, ¬ (j' < C.gates.length ∧ BelowF G C j' ∧
        gateVal n C j' (pairInput u v) = true) := fun j' hlt => Nat.find_min hex hlt
    have hj_lt : j < C.gates.length := hj_spec.1
    have hj_below : BelowF G C j := hj_spec.2.1
    have hj_true : gateVal n C j (pairInput u v) = true := hj_spec.2.2
    have hgate : gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
      simp [List.getD_eq_getElem?_getD, hj_lt]
    have hj_and : (gateAt C j).op = GateOp.and := by
      rcases hleast.1.1 (gateAt C j) (by rw [hgate]; exact List.getElem_mem hj_lt) with hand | hor
      · exact hand
      · exfalso
        have hrb : ∀ w ∈ (gateAt C j).inputs, w < n + j := hleast.1.2.1 j hj_lt
        have hev (x : Fin n → Bool) : gateVal n C j x =
            ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false).any id := by
          have hl : (List.ofFn x).length = n := by simp
          have hge := gate_eval C.gates (List.ofFn x) j hj_lt
          rw [hl] at hge
          change (C.gates.foldl step (List.ofFn x)).getD (n + j) false = _
          rw [hge, ← hgate, hor]
          change (((gateAt C j).inputs.map fun i =>
            if i < n + j then (C.wires (List.ofFn x)).getD i false else false).any id) = _
          congr 1
          refine List.map_congr_left fun i hi => ?_
          rw [ite_eq_left (hrb i hi)]
        have ht := hev (pairInput u v)
        rw [hj_true] at ht
        obtain ⟨w, hw_in, hw_true⟩ := by
          simpa only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq] using ht.symm
        have hw_lt : w < n + j := hrb w hw_in
        have hw_below : ∀ x : Fin n → Bool,
            (C.wires (List.ofFn x)).getD w false = true → graphFun G ∅ x = true := by
          intro x hwx
          apply hj_below x
          rw [hev x, List.any_map, List.any_eq_true]
          exact ⟨w, hw_in, hwx⟩
        by_cases hwn : w < n
        · let wi : Fin n := ⟨w, hwn⟩
          have hbad := hw_below (pairInput wi wi) (by
            rw [wire_input (pairInput wi wi) wi]
            exact decide_eq_true (Or.inl rfl))
          rw [graphFun_single wi] at hbad
          contradiction
        · have hwj : w - n < j := by omega
          apply hj_min (w - n) hwj
          refine ⟨by omega, ?_, ?_⟩
          · intro x hx
            change (C.wires (List.ofFn x)).getD (n + (w - n)) false = true at hx
            rw [show n + (w - n) = w by omega] at hx
            exact hw_below x hx
          · change (C.wires (List.ofFn (pairInput u v))).getD (n + (w - n)) false = true
            rw [show n + (w - n) = w by omega]
            exact hw_true
    letI : DecidableEq GateOp := gateOpDecEq
    refine ⟨j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hj_and, hj_below⟩
    · exact Finset.mem_filter.mpr ⟨he, u, v, rfl, hj_true⟩
  let P : Sym2 (Fin n) → Prop := fun e =>
    ¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin 2),
      2 ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
      orIn n C (opnd C h b) = {v}
  let S := (Ustar G C).filter P
  let S1 := (Ustar G C).filter fun e => P e ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a
  let S2 := (Ustar G C).filter fun e => P e ∧ ∃ a ∈ tops G C \ centreless G C,
    e ∈ gammaE G C a ∧ ∃ w ∈ side C a 0 ∪ side C a 1, w ∈ e
  let S3 := (Ustar G C).filter fun e => P e ∧ ∃ a ∈ tops G C \ centreless G C,
    e ∈ gammaE G C a ∧ ∀ w ∈ side C a 0 ∪ side C a 1, w ∉ e
  have hsub : S ⊆ S1 ∪ (S2 ∪ S3) := by
    intro e he
    obtain ⟨heU, hPe⟩ := Finset.mem_filter.mp he
    have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heU).1
    obtain ⟨a, ha_top, ha_gam⟩ := top_cover e heE
    by_cases hac : a ∈ centreless G C
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heU, hPe, a, hac, ha_gam⟩)
    · have ha_ct : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha_top, hac⟩
      by_cases hw : ∃ w ∈ side C a 0 ∪ side C a 1, w ∈ e
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨heU, hPe, a, ha_ct, ha_gam, hw⟩))
      · push Not at hw
        exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨heU, hPe, a, ha_ct, ha_gam, hw⟩))
  have hcard : S.card ≤ S1.card + S2.card + S3.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le S1 (S2 ∪ S3)
    have h3 := Finset.card_union_le S2 S3
    omega
  have h1 : S1.card ≤ k1 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk1 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have h2 : S2.card ≤ k2 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk2 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have h3 : S3.card ≤ k3 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk3 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have hgoal : ((Ustar G C).filter P).card ≤ S.card := by
    refine Finset.card_le_card ?_
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  calc
    _ ≤ S.card := hgoal
    _ ≤ S1.card + S2.card + S3.card := hcard
    _ ≤ k1 * (C.size + 1) + k2 * (C.size + 1) + k3 * (C.size + 1) := by omega
    _ = (k1 + k2 + k3) * (C.size + 1) := by ring
