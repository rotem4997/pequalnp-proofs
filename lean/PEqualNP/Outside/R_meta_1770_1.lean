import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1770_1
    (bothSing : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C,
          wireVal n C (opnd C a 0) (pairInput u u) = true ∧
          wireVal n C (opnd C a 1) (pairInput v v) = true)).card ≤ k * (C.size + 1))
    (oneSing : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ g ∈ junk G C, u ∈ wmax G C g ∧
          gateVal n C g (pairInput u v) = true ∧
          gateVal n C g (pairInput u u) = false ∧
          gateVal n C g (pairInput v v) = false)).card ≤ k * (C.size + 1))
    (bothQuad : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
          OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
          gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧
          gateVal n C h (pairInput u u) = false ∧ gateVal n C h (pairInput v v) = false)).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := bothSing
  obtain ⟨k2, hk2⟩ := oneSing
  obtain ⟨k3, hk3⟩ := bothQuad
  refine ⟨k1 + k2 + k3, ?_⟩
  intro n G _ C hg hL hT
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have h1 := hk1 n G C hg hL hT
  have h2 := hk2 n G C hg hL hT
  have h3 := hk3 n G C hg hL hT
  obtain ⟨⟨hAO, hRB, hlen2⟩, hfun, _⟩ := hL
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
  have foldl_mono : ∀ (gs : List Gate) (w1 w2 : List Bool),
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl step w1).getD i false = true → (gs.foldl step w2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro w1 w2 _ _ h i hi; exact h i hi
    | cons g gs ih =>
      intro w1 w2 hgs hlen hw i hi
      rw [List.foldl_cons] at hi ⊢
      refine ih (step w1 g) (step w2 g) (fun x hx => hgs x (List.mem_cons_of_mem g hx))
        (by rw [step_len, step_len, hlen]) ?_ i hi
      intro k hk
      rcases Nat.lt_trichotomy k w1.length with hklt | rfl | hkgt
      · rw [step_getD_lt w1 g k hklt] at hk
        rw [step_getD_lt w2 g k (hlen ▸ hklt)]
        exact hw k hk
      · rw [step_getD_self] at hk
        rw [hlen, step_getD_self]
        rcases hgs g List.mem_cons_self with hop | hop
        · rw [hop] at hk ⊢
          change (g.inputs.map fun t => w1.getD t false).all id = true at hk
          change (g.inputs.map fun t => w2.getD t false).all id = true
          rw [List.all_map, List.all_eq_true] at hk ⊢
          intro t ht
          exact hw t (hk t ht)
        · rw [hop] at hk ⊢
          change (g.inputs.map fun t => w1.getD t false).any id = true at hk
          change (g.inputs.map fun t => w2.getD t false).any id = true
          rw [List.any_map, List.any_eq_true] at hk ⊢
          obtain ⟨t, ht, htv⟩ := hk
          exact ⟨t, ht, hw t htv⟩
      · rw [getD_ge (step w1 g) k (by rw [step_len]; omega)] at hk
        cases hk
  have gateVal_mono : ∀ (j : ℕ) (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) →
      gateVal n C j x = true → gateVal n C j y = true := by
    intro j x y hxy hj
    refine foldl_mono C.gates (List.ofFn x) (List.ofFn y) hAO
      (by rw [List.length_ofFn, List.length_ofFn]) ?_ (n + j) hj
    intro i hi
    by_cases hin : i < n
    · have hi1 : (List.ofFn x).getD i false = x ⟨i, hin⟩ := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn]
        rfl
      have hi2 : (List.ofFn y).getD i false = y ⟨i, hin⟩ := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn]
        rfl
      rw [hi1] at hi
      rw [hi2]
      exact hxy ⟨i, hin⟩ hi
    · rw [getD_ge (List.ofFn x) i (by rw [List.length_ofFn]; omega)] at hi
      cases hi
  have orStep_len : ∀ (cs : List (List ℕ)) (gt : Gate),
      (orStep n cs gt).length = cs.length + 1 := by
    intro cs gt
    change (cs ++ [cs.length :: (if gt.op = GateOp.or then
      (gt.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]).length = cs.length + 1
    rw [List.length_append, List.length_singleton]
  have orReaches_inv : ∀ (gs : List Gate) (w : List Bool) (cs : List (List ℕ)),
      w.length = n + cs.length →
      (∀ k < cs.length, ∀ g ∈ cs.getD k [], g < cs.length ∧
        (w.getD (n + g) false = true → w.getD (n + k) false = true)) →
      (gs.foldl step w).length = n + (gs.foldl (orStep n) cs).length ∧
      ∀ k < (gs.foldl (orStep n) cs).length,
        ∀ g ∈ (gs.foldl (orStep n) cs).getD k [],
          g < (gs.foldl (orStep n) cs).length ∧
            ((gs.foldl step w).getD (n + g) false = true →
              (gs.foldl step w).getD (n + k) false = true) := by
    intro gs
    induction gs with
    | nil => intro w cs hlen hinv; exact ⟨hlen, hinv⟩
    | cons gt gs ih =>
      intro w cs hlen hinv
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (step w gt) (orStep n cs gt)
        (by rw [step_len, orStep_len, hlen]; omega) ?_
      intro k hk g hg
      rw [orStep_len] at hk
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hklt | hkeq
      · have hcs_eq : (orStep n cs gt).getD k [] = cs.getD k [] := by
          change (cs ++ [_]).getD k [] = cs.getD k []
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hklt,
            ← List.getD_eq_getElem?_getD]
        rw [hcs_eq] at hg
        obtain ⟨hg_lt, hval⟩ := hinv k hklt g hg
        refine ⟨by rw [orStep_len]; omega, fun hgv => ?_⟩
        rw [step_getD_lt w gt (n + g) (by omega)] at hgv
        rw [step_getD_lt w gt (n + k) (by omega)]
        exact hval hgv
      · subst hkeq
        have hcs_self : (orStep n cs gt).getD cs.length [] =
            cs.length :: (if gt.op = GateOp.or then
              (gt.inputs.filter (fun i => decide (n ≤ i ∧ i < n + cs.length))).flatMap
                (fun i => cs.getD (i - n) [])
              else []) := by
          change (cs ++ [_]).getD cs.length [] = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
          rfl
        rw [hcs_self, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨by rw [orStep_len]; omega, fun h => h⟩
        · split_ifs at hg with hop
          · rw [List.mem_flatMap] at hg
            obtain ⟨i, hi_filt, hg_mem⟩ := hg
            rw [List.mem_filter, decide_eq_true_eq] at hi_filt
            obtain ⟨hi_in, hni, hilt⟩ := hi_filt
            obtain ⟨hg_lt, hval⟩ := hinv (i - n) (by omega) g hg_mem
            refine ⟨by rw [orStep_len]; omega, fun hgv => ?_⟩
            rw [step_getD_lt w gt (n + g) (by omega)] at hgv
            have hwi : w.getD i false = true := by
              have heq : n + (i - n) = i := by omega
              rw [← heq]
              exact hval hgv
            rw [← hlen, step_getD_self, hop]
            change (gt.inputs.map fun k => w.getD k false).any id = true
            rw [List.any_map, List.any_eq_true]
            exact ⟨i, hi_in, hwi⟩
          · exact (List.not_mem_nil hg).elim
  have orReaches_up : ∀ (w g : ℕ) (x : Fin n → Bool),
      OrReaches n C w g → gateVal n C g x = true → wireVal n C w x = true := by
    intro w g x hor hgx
    obtain ⟨hnw, hmem⟩ := hor
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [show n + k - n = k by omega] at hmem
    have empty_inv : ∀ k < ([] : List (List ℕ)).length,
        ∀ g ∈ ([] : List (List ℕ)).getD k [],
          g < ([] : List (List ℕ)).length ∧
            ((List.ofFn x).getD (n + g) false = true →
              (List.ofFn x).getD (n + k) false = true) := by
      intro k hk
      rw [List.length_nil] at hk
      exact (Nat.not_lt_zero k hk).elim
    have hinv_all := orReaches_inv C.gates (List.ofFn x) []
      (by rw [List.length_ofFn, List.length_nil, Nat.add_zero]) empty_inv
    have hlen_or : (orSets n C).length = C.gates.length := by
      have h1 := hinv_all.1
      have h2 := foldl_len C.gates (List.ofFn x)
      rw [List.length_ofFn] at h2
      change (C.gates.foldl step (List.ofFn x)).length = n + (orSets n C).length at h1
      change (C.gates.foldl (orStep n) []).length = C.gates.length
      omega
    by_cases hk : k < C.gates.length
    · have hk' : k < (orSets n C).length := by omega
      exact (hinv_all.2 k hk' g hmem).2 hgx
    · have hnone : (orSets n C).getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hnone] at hmem
      exact (List.not_mem_nil hmem).elim
  have top_and_true : ∀ (a : ℕ) (x : Fin n → Bool),
      a ∈ tops G C →
      wireVal n C (opnd C a 0) x = true →
      wireVal n C (opnd C a 1) x = true →
      graphFun G ∅ x = true := by
    intro a x ha h0 h1
    obtain ⟨halen_m, haop, habel⟩ := Finset.mem_filter.mp
      (ha : a ∈ (Finset.range C.gates.length).filter
        (fun j => (gateAt C j).op = GateOp.and ∧ BelowF G C j))
    have halen : a < C.gates.length := Finset.mem_range.mp halen_m
    apply habel
    show (C.wires (List.ofFn x)).getD (n + a) false = true
    have hcw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
    rw [hcw]
    have hlenx : (List.ofFn x).length = n := List.length_ofFn
    have hgate := foldl_getD_gate C.gates (List.ofFn x) a halen
    rw [hlenx] at hgate
    rw [hgate]
    have hge : gateAt C a = C.gates[a] := by
      change C.gates.getD a ⟨GateOp.or, []⟩ = C.gates[a]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem halen]
      rfl
    have hga : C.gates[a] ∈ C.gates := List.getElem_mem halen
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 _ hga)
    have ep : opnd C a 0 = p := by
      change (gateAt C a).inputs.getD 0 0 = p
      rw [hge, hpq]
      rfl
    have eq : opnd C a 1 = q := by
      change (gateAt C a).inputs.getD 1 0 = q
      rw [hge, hpq]
      rfl
    have hp_lt : p < n + a := hRB a halen p (by rw [hge, hpq]; exact List.mem_cons_self)
    have hq_lt : q < n + a := hRB a halen q
      (by rw [hge, hpq]; exact List.mem_cons_of_mem p List.mem_cons_self)
    rw [← hge, haop, hge, hpq]
    change (if p < n + a then (C.gates.foldl step (List.ofFn x)).getD p false else false) &&
      ((if q < n + a then (C.gates.foldl step (List.ofFn x)).getD q false else false) && true) = true
    rw [Bool.and_true, ite_eq_left_of_eq_true _ _ (eq_true hp_lt),
      ite_eq_left_of_eq_true _ _ (eq_true hq_lt), ← ep, ← eq]
    exact Bool.and_eq_true_iff.mpr ⟨h0, h1⟩
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
  have wmax_from_left : ∀ (a g h : ℕ) (u : Fin n),
      a ∈ tops G C → OrReaches n C (opnd C a 0) g → OrReaches n C (opnd C a 1) h →
      gateVal n C g (pairInput u u) = true → u ∈ wmax G C h := by
    intro a g h u ha horg horh hgu
    refine (Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩ :
      u ∈ Finset.univ.filter (fun w => ∀ x : Fin n → Bool,
        gateVal n C h x = true → x w = true → graphFun G ∅ x = true))
    intro x hhx hxu
    have hmono : ∀ i : Fin n, pairInput u u i = true → x i = true := by
      intro i hi
      change decide (i = u ∨ i = u) = true at hi
      rw [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl <;> exact hxu
    have hgx := gateVal_mono g (pairInput u u) x hmono hgu
    exact top_and_true a x ha (orReaches_up (opnd C a 0) g x horg hgx)
      (orReaches_up (opnd C a 1) h x horh hhx)
  have wmax_from_right : ∀ (a g h : ℕ) (u : Fin n),
      a ∈ tops G C → OrReaches n C (opnd C a 0) g → OrReaches n C (opnd C a 1) h →
      gateVal n C h (pairInput u u) = true → u ∈ wmax G C g := by
    intro a g h u ha horg horh hhu
    refine (Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩ :
      u ∈ Finset.univ.filter (fun w => ∀ x : Fin n → Bool,
        gateVal n C g x = true → x w = true → graphFun G ∅ x = true))
    intro x hgx hxu
    have hmono : ∀ i : Fin n, pairInput u u i = true → x i = true := by
      intro i hi
      change decide (i = u ∨ i = u) = true at hi
      rw [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl <;> exact hxu
    have hhx := gateVal_mono h (pairInput u u) x hmono hhu
    exact top_and_true a x ha (orReaches_up (opnd C a 0) g x horg hgx)
      (orReaches_up (opnd C a 1) h x horh hhx)
  have pair_comm : ∀ u v : Fin n, pairInput u v = pairInput v u := by
    intro u v
    funext w
    change decide (w = u ∨ w = v) = decide (w = v ∨ w = u)
    exact decide_eq_decide.mpr or_comm
  classical
  let S := {x9 ∈ Ustar G C |
    (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C, ∃ (x13 : Fin 2),
      ∃ x14 ∈ junk G C, x10 ∈ side C x12 x13 ∧
        OrReaches n C (opnd C x12 ((1 : Fin 2) - x13)) x14 ∧
        gateVal n C x14 (pairInput x10 x11) = true) ∧
    ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ tops G C,
      ∃ x13 ∈ junk G C, ∃ x14 ∈ junk G C, x13 ≠ x14 ∧
        OrReaches n C (opnd C x12 0) x13 ∧ OrReaches n C (opnd C x12 1) x14 ∧
        gateVal n C x13 (pairInput x10 x11) = true ∧
        gateVal n C x14 (pairInput x10 x11) = true}
  let S1 := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C,
      wireVal n C (opnd C a 0) (pairInput u u) = true ∧
      wireVal n C (opnd C a 1) (pairInput v v) = true)
  let S2 := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
    ∃ g ∈ junk G C, u ∈ wmax G C g ∧
      gateVal n C g (pairInput u v) = true ∧
      gateVal n C g (pairInput u u) = false ∧
      gateVal n C g (pairInput v v) = false)
  let S3 := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C, g ≠ h ∧
      OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
      gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
      gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false ∧
      gateVal n C h (pairInput u u) = false ∧ gateVal n C h (pairInput v v) = false)
  have hsub : S ⊆ S1 ∪ S2 ∪ S3 := by
    intro e he
    obtain ⟨heU, -, u, v, rfl, a, ha, g, hg, h, hh, hne, horg, horh, hguv, hhuv⟩ :=
      Finset.mem_filter.mp he
    have n_uu : ¬ (gateVal n C g (pairInput u u) = true ∧ gateVal n C h (pairInput u u) = true) := by
      rintro ⟨hgu, hhu⟩
      have hgf := top_and_true a (pairInput u u) ha
        (orReaches_up (opnd C a 0) g (pairInput u u) horg hgu)
        (orReaches_up (opnd C a 1) h (pairInput u u) horh hhu)
      rw [no_self_graphFun u] at hgf
      cases hgf
    have n_vv : ¬ (gateVal n C g (pairInput v v) = true ∧ gateVal n C h (pairInput v v) = true) := by
      rintro ⟨hgv, hhv⟩
      have hgf := top_and_true a (pairInput v v) ha
        (orReaches_up (opnd C a 0) g (pairInput v v) horg hgv)
        (orReaches_up (opnd C a 1) h (pairInput v v) horh hhv)
      rw [no_self_graphFun v] at hgf
      cases hgf
    by_cases hgu : gateVal n C g (pairInput u u) = true
    · by_cases hhv : gateVal n C h (pairInput v v) = true
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨heU, u, v, rfl, a, ha,
            orReaches_up (opnd C a 0) g (pairInput u u) horg hgu,
            orReaches_up (opnd C a 1) h (pairInput v v) horh hhv⟩))
      · have hhu_f : gateVal n C h (pairInput u u) = false :=
          Bool.eq_false_iff.mpr fun hhu => n_uu ⟨hgu, hhu⟩
        have hhv_f : gateVal n C h (pairInput v v) = false := Bool.eq_false_iff.mpr hhv
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨heU, u, v, rfl, h, hh, wmax_from_left a g h u ha horg horh hgu, hhuv, hhu_f, hhv_f⟩))
    · by_cases hgv : gateVal n C g (pairInput v v) = true
      · by_cases hhu : gateVal n C h (pairInput u u) = true
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨heU, v, u, Sym2.eq_swap, a, ha,
              orReaches_up (opnd C a 0) g (pairInput v v) horg hgv,
              orReaches_up (opnd C a 1) h (pairInput u u) horh hhu⟩))
        · have hhu_f : gateVal n C h (pairInput u u) = false := Bool.eq_false_iff.mpr hhu
          have hhv_f : gateVal n C h (pairInput v v) = false :=
            Bool.eq_false_iff.mpr fun hhv => n_vv ⟨hgv, hhv⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨heU, v, u, Sym2.eq_swap, h, hh, wmax_from_left a g h v ha horg horh hgv,
              by rw [pair_comm]; exact hhuv, hhv_f, hhu_f⟩))
      · have hgu_f : gateVal n C g (pairInput u u) = false := Bool.eq_false_iff.mpr hgu
        have hgv_f : gateVal n C g (pairInput v v) = false := Bool.eq_false_iff.mpr hgv
        by_cases hhu : gateVal n C h (pairInput u u) = true
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨heU, u, v, rfl, g, hg, wmax_from_right a g h u ha horg horh hhu, hguv, hgu_f, hgv_f⟩))
        · by_cases hhv : gateVal n C h (pairInput v v) = true
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨heU, v, u, Sym2.eq_swap, g, hg, wmax_from_right a g h v ha horg horh hhv,
                by rw [pair_comm]; exact hguv, hgv_f, hgu_f⟩))
          · have hhu_f : gateVal n C h (pairInput u u) = false := Bool.eq_false_iff.mpr hhu
            have hhv_f : gateVal n C h (pairInput v v) = false := Bool.eq_false_iff.mpr hhv
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨heU, u, v, rfl, a, ha, g, hg, h, hh, hne, horg, horh,
                hguv, hhuv, hgu_f, hgv_f, hhu_f, hhv_f⟩)
  have hcard : S.card ≤ S1.card + S2.card + S3.card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le (S1 ∪ S2) S3).trans
      (Nat.add_le_add_right (Finset.card_union_le S1 S2) S3.card))
  change S.card ≤ (k1 + k2 + k3) * (C.size + 1)
  have hs1 : S1.card ≤ k1 * (C.size + 1) := h1
  have hs2 : S2.card ≤ k2 * (C.size + 1) := h2
  have hs3 : S3.card ≤ k3 * (C.size + 1) := h3
  have hsum : S1.card + S2.card + S3.card ≤
      k1 * (C.size + 1) + k2 * (C.size + 1) + k3 * (C.size + 1) :=
    Nat.add_le_add (Nat.add_le_add hs1 hs2) hs3
  rw [Nat.add_mul, Nat.add_mul]
  exact hcard.trans hsum
