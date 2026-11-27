import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1894_573
    (hOneHot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true) →
      ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 42) (0 : Fin 42)))).getD (42 + j) false = false)
    (hTwoPts : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true) →
      ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 42) (1 : Fin 42)))).getD (42 + j) false = false)
    (hNonInc : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true) →
      ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 42) (22 : Fin 42)))).getD (42 + j) false = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  classical
  intro C hMono hSize hActive
  by_contra hAll
  have hComputes : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x p = true ∧ x l = true := by
    intro x
    by_contra hbad
    exact hAll ⟨x, hbad⟩
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hMono g hg).1
  let run : List Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]
    rfl
  have hrun_len : ∀ (gs : List Gate) (x : List Bool), (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have hgetD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b
    simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List Gate) (x : List Bool) (i : ℕ), i < x.length + gs.length →
      (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), i < x.length →
      (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1
    exact h1
  have hrun_gate : ∀ (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs.getD j ⟨GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
            if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := hrun_len gs x
      have hsame : ∀ k ≤ gs.length, ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hrun_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · have hgd : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd, hsame j (Nat.le_of_lt hlt), hrun_prefix gs [g] x _ (by omega)]
        exact ih j hlt
      · have hjeq : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
        subst hjeq
        have hgd : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hgd, hsame gs.length le_rfl, hrun_snoc, ← hlen, hgetD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hrun_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ w, (run gs x).getD w false = true → (run gs y).getD w false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => intro w hw; exact hle w hw
    | append_singleton gs g ih =>
      intro w hw
      have ih' := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
      have l1 := hrun_len gs x
      have l2 := hrun_len gs y
      rw [hrun_snoc] at hw ⊢
      rcases Nat.lt_trichotomy w (x.length + gs.length) with hlt | heq | hgt
      · rw [hgetD_lt _ _ _ (by omega)] at hw
        rw [hgetD_lt _ _ _ (by omega)]
        exact ih' w hw
      · have e1 : w = (run gs x).length := by omega
        have e2 : w = (run gs y).length := by omega
        rw [e1, hgetD_at] at hw
        rw [e2, hgetD_at]
        rcases hgs g (List.mem_append_right _ (List.mem_singleton_self g)) with hop | hop
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).all id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).all id = true
          rw [List.all_map, List.all_eq_true] at hw ⊢
          intro q hq
          exact ih' q (hw q hq)
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).any id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).any id = true
          rw [List.any_map, List.any_eq_true] at hw ⊢
          rcases hw with ⟨q, hq1, hq2⟩
          exact ⟨q, hq1, ih' q hq2⟩
      · exfalso
        have hdef : (run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)]).getD w false = false :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        rw [hdef] at hw
        exact Bool.false_ne_true hw
  let xX : Fin 42 → Bool := fun i => decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))
  let actSet : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧ (run C.gates (List.ofFn xX)).getD (42 + j) false = true
  have hact_ne : actSet.Nonempty := by
    rcases hActive with ⟨j, g, hjg, hop, hval⟩
    have hjlt : j < C.gates.length := by
      rcases List.getElem?_eq_some_iff.mp hjg with ⟨hlt, _⟩; exact hlt
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, g, hjg, hop, hval⟩⟩
  let j0 : ℕ := actSet.min' hact_ne
  have hj0_mem : j0 ∈ actSet := Finset.min'_mem actSet hact_ne
  have hj0_min : ∀ i ∈ actSet, j0 ≤ i := fun i hi => Finset.min'_le actSet i hi
  have hj0_f := Finset.mem_filter.mp hj0_mem
  have hj0_lt : j0 < C.gates.length := Finset.mem_range.mp hj0_f.1
  rcases hj0_f.2 with ⟨g0, hj0_g, hj0_and, hj0_val⟩
  have hearlier_and : ∀ i < j0, ∀ g : Gate, C.gates[i]? = some g → g.op = GateOp.and →
      (run C.gates (List.ofFn xX)).getD (42 + i) false = false := by
    intro i hilt g hig hop
    by_contra hne
    have htrue : (run C.gates (List.ofFn xX)).getD (42 + i) false = true :=
      Bool.eq_true_of_not_eq_false hne
    have hi_lt : i < C.gates.length := Nat.lt_trans hilt hj0_lt
    have himem : i ∈ actSet := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_lt, g, hig, hop, htrue⟩
    have := hj0_min i himem
    omega
  have hsingle : ∀ w < 42 + j0, (run C.gates (List.ofFn xX)).getD w false = true →
      ∃ u : Fin 42, xX u = true ∧ (run C.gates (List.ofFn (fun t : Fin 42 => decide (t = u)))).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt hwtrue
      by_cases hw42 : w < 42
      · refine ⟨⟨w, hw42⟩, ?_, ?_⟩
        · rw [hrun_input C.gates (List.ofFn xX) w (by rw [List.length_ofFn]; exact hw42)] at hwtrue
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw42] at hwtrue
          exact hwtrue
        · rw [hrun_input C.gates _ w (by rw [List.length_ofFn]; exact hw42)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw42]
          exact decide_eq_true rfl
      · let i : ℕ := w - 42
        have hiw : w = 42 + i := by omega
        have hilt : i < j0 := by omega
        have hiC : i < C.gates.length := Nat.lt_trans hilt hj0_lt
        let gi : Gate := C.gates.getD i ⟨GateOp.or, []⟩
        have hgi_some : C.gates[i]? = some gi := by
          dsimp only [gi]
          rw [List.getD_eq_getElem _ _ hiC, List.getElem?_eq_getElem hiC]
        have hgi_mem : gi ∈ C.gates := by
          dsimp only [gi]; rw [List.getD_eq_getElem _ _ hiC]; exact List.getElem_mem hiC
        rcases hAO gi hgi_mem with hiand | hior
        · exfalso
          have hf := hearlier_and i hilt gi hgi_some hiand
          rw [hiw] at hwtrue
          rw [hf] at hwtrue
          exact Bool.false_ne_true hwtrue
        · rw [hiw] at hwtrue
          have hrg := hrun_gate C.gates (List.ofFn xX) i hiC
          rw [List.length_ofFn] at hrg
          rw [hrg] at hwtrue
          change gi.op.eval (gi.inputs.map fun k => if k < 42 + i then (run C.gates (List.ofFn xX)).getD k false else false) = true at hwtrue
          rw [hior] at hwtrue
          change (gi.inputs.map fun k => if k < 42 + i then (run C.gates (List.ofFn xX)).getD k false else false).any id = true at hwtrue
          rw [List.any_map, List.any_eq_true] at hwtrue
          rcases hwtrue with ⟨k, hk_in, hk_true⟩
          dsimp only [Function.comp, id] at hk_true
          have hk_lt : k < 42 + i := by
            by_contra hge
            rw [if_neg hge] at hk_true
            exact Bool.false_ne_true hk_true
          rw [if_pos hk_lt] at hk_true
          rcases ih k (by omega) (by omega) hk_true with ⟨u, hxu, hku⟩
          refine ⟨u, hxu, ?_⟩
          rw [hiw]
          have hrg2 := hrun_gate C.gates (List.ofFn (fun t : Fin 42 => decide (t = u))) i hiC
          rw [List.length_ofFn] at hrg2
          rw [hrg2]
          change gi.op.eval (gi.inputs.map fun m => if m < 42 + i then (run C.gates (List.ofFn (fun t : Fin 42 => decide (t = u)))).getD m false else false) = true
          rw [hior]
          change (gi.inputs.map fun m => if m < 42 + i then (run C.gates (List.ofFn (fun t : Fin 42 => decide (t = u)))).getD m false else false).any id = true
          rw [List.any_map, List.any_eq_true]
          exact ⟨k, hk_in, by dsimp only [Function.comp, id]; rw [if_pos hk_lt]; exact hku⟩
  have hg0_eq : C.gates.getD j0 ⟨GateOp.or, []⟩ = g0 := by
    rw [List.getD_eq_getElem?_getD, hj0_g]; rfl
  have hg0_mem : g0 ∈ C.gates := by
    rcases List.getElem?_eq_some_iff.mp hj0_g with ⟨hlt, heq⟩
    rw [← heq]; exact List.getElem_mem hlt
  have hg0_len : g0.inputs.length ≤ 2 := (hMono g0 hg0_mem).2
  have hpair_ex : ∃ u v : Fin 42, xX u = true ∧ xX v = true ∧
      (run C.gates (List.ofFn (pairInput u v))).getD (42 + j0) false = true := by
    have hrg0 := hrun_gate C.gates (List.ofFn xX) j0 hj0_lt
    rw [List.length_ofFn, hg0_eq, hj0_and] at hrg0
    rcases hinputs : g0.inputs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩
    · refine ⟨0, 0, by dsimp only [xX]; decide +kernel, by dsimp only [xX]; decide +kernel, ?_⟩
      have hrgp := hrun_gate C.gates (List.ofFn (pairInput (0 : Fin 42) (0 : Fin 42))) j0 hj0_lt
      rw [List.length_ofFn, hg0_eq, hj0_and, hinputs] at hrgp
      rw [hrgp]; rfl
    · rw [hrg0, hinputs] at hj0_val
      change ((if w1 < 42 + j0 then (run C.gates (List.ofFn xX)).getD w1 false else false) && true) = true at hj0_val
      rw [Bool.and_true] at hj0_val
      have hw1_lt : w1 < 42 + j0 := by
        by_contra hge; rw [if_neg hge] at hj0_val; exact Bool.false_ne_true hj0_val
      rw [if_pos hw1_lt] at hj0_val
      rcases hsingle w1 hw1_lt hj0_val with ⟨u, hxu, hwu⟩
      refine ⟨u, u, hxu, hxu, ?_⟩
      have hrgp := hrun_gate C.gates (List.ofFn (pairInput u u)) j0 hj0_lt
      rw [List.length_ofFn, hg0_eq, hj0_and, hinputs] at hrgp
      rw [hrgp]
      change ((if w1 < 42 + j0 then (run C.gates (List.ofFn (pairInput u u))).getD w1 false else false) && true) = true
      rw [if_pos hw1_lt, Bool.and_true]
      have hpeq : pairInput u u = (fun t : Fin 42 => decide (t = u)) := by
        funext t
        change decide (t = u ∨ t = u) = decide (t = u)
        exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq, decide_eq_true_eq, or_self])
      rw [hpeq]; exact hwu
    · rw [hrg0, hinputs] at hj0_val
      change ((if w1 < 42 + j0 then (run C.gates (List.ofFn xX)).getD w1 false else false) &&
        ((if w2 < 42 + j0 then (run C.gates (List.ofFn xX)).getD w2 false else false) && true)) = true at hj0_val
      rw [Bool.and_true, Bool.and_eq_true] at hj0_val
      have hw1_lt : w1 < 42 + j0 := by
        by_contra hge; have h1 := hj0_val.1; rw [if_neg hge] at h1; exact Bool.false_ne_true h1
      have hw2_lt : w2 < 42 + j0 := by
        by_contra hge; have h2 := hj0_val.2; rw [if_neg hge] at h2; exact Bool.false_ne_true h2
      have hw1_t : (run C.gates (List.ofFn xX)).getD w1 false = true := by
        have h1 := hj0_val.1; rw [if_pos hw1_lt] at h1; exact h1
      have hw2_t : (run C.gates (List.ofFn xX)).getD w2 false = true := by
        have h2 := hj0_val.2; rw [if_pos hw2_lt] at h2; exact h2
      rcases hsingle w1 hw1_lt hw1_t with ⟨u, hxu, hwu⟩
      rcases hsingle w2 hw2_lt hw2_t with ⟨v, hxv, hwv⟩
      refine ⟨u, v, hxu, hxv, ?_⟩
      have hrgp := hrun_gate C.gates (List.ofFn (pairInput u v)) j0 hj0_lt
      rw [List.length_ofFn, hg0_eq, hj0_and, hinputs] at hrgp
      rw [hrgp]
      change ((if w1 < 42 + j0 then (run C.gates (List.ofFn (pairInput u v))).getD w1 false else false) &&
        ((if w2 < 42 + j0 then (run C.gates (List.ofFn (pairInput u v))).getD w2 false else false) && true)) = true
      rw [if_pos hw1_lt, if_pos hw2_lt, Bool.and_true, Bool.and_eq_true]
      constructor
      · refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 42 => decide (t = u)))
          (List.ofFn (pairInput u v)) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w1 hwu
        intro k hk
        by_cases hk42 : k < 42
        · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk42] at hk ⊢
          change decide (⟨k, hk42⟩ = u) = true at hk
          change decide (⟨k, hk42⟩ = u ∨ ⟨k, hk42⟩ = v) = true
          rw [decide_eq_true_eq] at hk ⊢
          exact Or.inl hk
        · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
      · refine hrun_mono C.gates hAO (List.ofFn (fun t : Fin 42 => decide (t = v)))
          (List.ofFn (pairInput u v)) (by rw [List.length_ofFn, List.length_ofFn]) ?_ w2 hwv
        intro k hk
        by_cases hk42 : k < 42
        · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk42] at hk ⊢
          change decide (⟨k, hk42⟩ = v) = true at hk
          change decide (⟨k, hk42⟩ = u ∨ ⟨k, hk42⟩ = v) = true
          rw [decide_eq_true_eq] at hk ⊢
          exact Or.inr hk
        · exfalso; rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hk; exact Bool.false_ne_true hk
    · rw [hinputs] at hg0_len; exfalso; exact Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hg0_len))
  rcases hpair_ex with ⟨u, v, hxu, hxv, hj0_uv⟩
  let E : Fin 42 → Fin 42 → Prop := fun p l =>
    p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  let adj : Fin 42 → Fin 42 → Prop := fun a b => E a b ∨ E b a
  have hX_ind : ∀ a b : Fin 42, xX a = true → xX b = true → ¬ adj a b := by
    dsimp only [xX, adj, E]
    decide +kernel
  have hnot_adj : ¬ adj u v := hX_ind u v hxu hxv
  have hrelabel : ∀ (e eInv : Fin 42 → Fin 42),
      (∀ a : Fin 42, eInv (e a) = a) →
      (∀ a : Fin 42, e (eInv a) = a) →
      (∀ a b : Fin 42, adj (e a) (e b) ↔ adj a b) →
      (e u = 0 ∧ (e v = 0 ∨ e v = 1 ∨ e v = 22)) → False := by
    intro e eInv hli hri haut heuv
    let mw : ℕ → ℕ := fun w => if h : w < 42 then (e ⟨w, h⟩).val else w
    let mg : Gate → Gate := fun g => ⟨g.op, g.inputs.map mw⟩
    let D : Circuit := ⟨C.gates.map mg, mw C.output⟩
    have hmw_lt : ∀ w k : ℕ, w < 42 + k → mw w < 42 + k := by
      intro w k hw
      dsimp only [mw]
      split_ifs with h42
      · have := (e ⟨w, h42⟩).isLt; omega
      · exact hw
    have hD_run : ∀ (gs : List Gate) (y : Fin 42 → Bool) (w : ℕ),
        (run (gs.map mg) (List.ofFn y)).getD (mw w) false =
          (run gs (List.ofFn (fun a : Fin 42 => y (e a)))).getD w false := by
      intro gs y
      induction gs using List.reverseRecOn with
      | nil =>
        intro w
        change (List.ofFn y).getD (mw w) false = (List.ofFn (fun a : Fin 42 => y (e a))).getD w false
        dsimp only [mw]
        split_ifs with h42
        · have hlt := (e ⟨w, h42⟩).isLt
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h42]
        · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
          rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
      | append_singleton gs g ih =>
        intro w
        rw [List.map_append, List.map_singleton, hrun_snoc, hrun_snoc]
        have hlen1 : (run (gs.map mg) (List.ofFn y)).length = 42 + gs.length := by
          rw [hrun_len, List.length_ofFn, List.length_map]
        have hlen2 : (run gs (List.ofFn (fun a : Fin 42 => y (e a)))).length = 42 + gs.length := by
          rw [hrun_len, List.length_ofFn]
        rcases Nat.lt_trichotomy w (42 + gs.length) with hlt | heq | hgt
        · have hmlt : mw w < 42 + gs.length := hmw_lt w gs.length hlt
          rw [hgetD_lt _ _ _ (by omega), hgetD_lt _ _ _ (by omega)]
          exact ih w
        · subst heq
          have hmw_eq : mw (42 + gs.length) = 42 + gs.length := by
            dsimp only [mw]; rw [dif_neg (by omega)]
          rw [hmw_eq]
          have h1 : (run (gs.map mg) (List.ofFn y) ++
              [(mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false)]).getD
              (42 + gs.length) false =
              (mg g).op.eval ((mg g).inputs.map fun i => (run (gs.map mg) (List.ofFn y)).getD i false) := by
            rw [← hlen1]; exact hgetD_at _ _
          have h2 : (run gs (List.ofFn (fun a : Fin 42 => y (e a))) ++
              [g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun a : Fin 42 => y (e a)))).getD i false)]).getD
              (42 + gs.length) false =
              g.op.eval (g.inputs.map fun i => (run gs (List.ofFn (fun a : Fin 42 => y (e a)))).getD i false) := by
            rw [← hlen2]; exact hgetD_at _ _
          rw [h1, h2]
          dsimp only [mg]
          rw [List.map_map]
          congr 1
          refine List.map_congr_left fun i _ => ?_
          exact ih i
        · have hmw_eq : mw w = w := by dsimp only [mw]; rw [dif_neg (by omega)]
          rw [hmw_eq]
          rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
          rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]
    have hD_mono : Monotone2 D := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨g1, hg1, rfl⟩
      exact ⟨(hMono g1 hg1).1, by dsimp only [mg]; rw [List.length_map]; exact (hMono g1 hg1).2⟩
    have hD_size : D.size ≤ 124 := by
      change (C.gates.map mg).length ≤ 124
      rw [List.length_map]
      exact hSize
    have hD_comp : ∀ y : Fin 42 → Bool, D.eval (List.ofFn y) = true ↔
        ∃ p l : Fin 42, E p l ∧ y p = true ∧ y l = true := by
      intro y
      have h1 : D.eval (List.ofFn y) = C.eval (List.ofFn (fun a => y (e a))) := hD_run C.gates y C.output
      rw [h1, hComputes (fun a => y (e a))]
      constructor
      · rintro ⟨p, l, hpl, hp, hl⟩
        have hadj_ep_el : adj (e p) (e l) := (haut p l).mpr (Or.inl hpl)
        rcases hadj_ep_el with h1' | h2'
        · exact ⟨e p, e l, h1', hp, hl⟩
        · exact ⟨e l, e p, h2', hl, hp⟩
      · rintro ⟨p, l, hpl, hp, hl⟩
        have hadj_inv : adj (eInv p) (eInv l) :=
          (haut (eInv p) (eInv l)).mp (by rw [hri p, hri l]; exact Or.inl hpl)
        rcases hadj_inv with h1' | h2'
        · exact ⟨eInv p, eInv l, h1', by rw [hri p]; exact hp, by rw [hri l]; exact hl⟩
        · exact ⟨eInv l, eInv p, h2', by rw [hri l]; exact hl, by rw [hri p]; exact hp⟩
    have hD_g0 : D.gates[j0]? = some (mg g0) := by
      change (C.gates.map mg)[j0]? = some (mg g0)
      rw [List.getElem?_map, hj0_g]; rfl
    have hD_and : (mg g0).op = GateOp.and := hj0_and
    have hD_val : (D.wires (List.ofFn (pairInput (e u) (e v)))).getD (42 + j0) false = true := by
      have hmw_j0 : mw (42 + j0) = 42 + j0 := by dsimp only [mw]; rw [dif_neg (by omega)]
      have hstep := hD_run C.gates (pairInput (e u) (e v)) (42 + j0)
      rw [hmw_j0] at hstep
      change (run (C.gates.map mg) (List.ofFn (pairInput (e u) (e v)))).getD (42 + j0) false = true
      rw [hstep]
      have hpeq : (fun a : Fin 42 => pairInput (e u) (e v) (e a)) = pairInput u v := by
        funext a
        change decide (e a = e u ∨ e a = e v) = decide (a = u ∨ a = v)
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, decide_eq_true_eq]
        constructor
        · rintro (h | h)
          · exact Or.inl (by have := congrArg eInv h; rw [hli, hli] at this; exact this)
          · exact Or.inr (by have := congrArg eInv h; rw [hli, hli] at this; exact this)
        · rintro (rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr rfl
      rw [hpeq]
      exact hj0_uv
    rcases heuv with ⟨heu0, hev0 | hev1 | hev22⟩
    · rw [heu0, hev0] at hD_val
      have hf := hOneHot D hD_mono hD_size hD_comp j0 (mg g0) hD_g0 hD_and
      rw [hf] at hD_val; exact Bool.false_ne_true hD_val
    · rw [heu0, hev1] at hD_val
      have hf := hTwoPts D hD_mono hD_size hD_comp j0 (mg g0) hD_g0 hD_and
      rw [hf] at hD_val; exact Bool.false_ne_true hD_val
    · rw [heu0, hev22] at hD_val
      have hf := hNonInc D hD_mono hD_size hD_comp j0 (mg g0) hD_g0 hD_and
      rw [hf] at hD_val; exact Bool.false_ne_true hD_val
  let dual : Fin 42 → Fin 42 := fun a =>
    if a.val < 21 then Fin.natAdd 21 (-Fin.ofNat 21 a.val)
    else Fin.castAdd 21 (-Fin.ofNat 21 (a.val - 21))
  let shift : Fin 21 → Fin 42 → Fin 42 := fun c a =>
    if a.val < 21 then Fin.castAdd 21 (Fin.ofNat 21 a.val - c)
    else Fin.natAdd 21 (Fin.ofNat 21 (a.val - 21) - c)
  let frob : Fin 42 → Fin 42 := fun a =>
    if a.val < 21 then Fin.castAdd 21 (4 * Fin.ofNat 21 a.val)
    else Fin.natAdd 21 (4 * Fin.ofNat 21 (a.val - 21))
  let frob2 : Fin 42 → Fin 42 := fun a =>
    if a.val < 21 then Fin.castAdd 21 (16 * Fin.ofNat 21 a.val)
    else Fin.natAdd 21 (16 * Fin.ofNat 21 (a.val - 21))
  let colMap (pm lm : List ℕ) (a : Fin 42) : Fin 42 :=
    if a.val < 21 then Fin.ofNat 42 (pm.getD a.val 0)
    else Fin.ofNat 42 (21 + lm.getD (a.val - 21) 0)
  let c1 := colMap [0, 19, 16, 20, 6, 8, 11, 1, 14, 2, 18, 4, 12, 3, 5, 15, 9, 10, 17, 7, 13] [5, 15, 16, 6, 13, 7, 18, 0, 19, 2, 4, 11, 8, 10, 1, 14, 9, 17, 3, 12, 20]
  let c1i := colMap [0, 7, 9, 13, 11, 14, 4, 19, 5, 16, 17, 6, 12, 20, 8, 15, 2, 18, 10, 1, 3] [7, 14, 9, 18, 10, 0, 3, 5, 12, 16, 13, 11, 19, 4, 15, 1, 2, 17, 6, 8, 20]
  let c2 := colMap [0, 15, 17, 8, 20, 1, 14, 18, 10, 16, 9, 12, 19, 11, 3, 2, 13, 5, 6, 4, 7] [20, 1, 13, 4, 6, 0, 14, 17, 15, 16, 8, 19, 18, 10, 2, 9, 12, 5, 11, 3, 7]
  let c2i := colMap [0, 5, 15, 14, 19, 17, 18, 20, 3, 10, 8, 13, 11, 16, 6, 1, 9, 2, 7, 12, 4] [5, 1, 14, 19, 3, 17, 4, 20, 10, 15, 13, 18, 16, 2, 6, 8, 9, 7, 12, 11, 0]
  let c3 := colMap [0, 2, 15, 16, 11, 5, 19, 20, 3, 6, 12, 13, 18, 4, 7, 1, 8, 17, 10, 9, 14] [7, 1, 15, 16, 10, 5, 19, 20, 2, 11, 12, 18, 4, 3, 6, 8, 13, 17, 9, 14, 0]
  let c3i := colMap [0, 15, 1, 8, 13, 5, 9, 14, 16, 19, 18, 4, 10, 11, 20, 2, 3, 17, 12, 6, 7] [20, 1, 8, 13, 12, 5, 14, 0, 15, 18, 4, 9, 10, 16, 19, 2, 3, 17, 11, 6, 7]
  let c4 := colMap [0, 2, 15, 19, 11, 17, 10, 13, 20, 12, 4, 3, 14, 6, 7, 5, 8, 1, 16, 18, 9] [7, 1, 15, 18, 16, 17, 9, 20, 19, 11, 3, 10, 13, 6, 12, 4, 8, 0, 2, 14, 5]
  let c4i := colMap [0, 17, 1, 11, 10, 15, 13, 14, 16, 20, 6, 4, 9, 7, 12, 2, 18, 5, 19, 3, 8] [17, 1, 18, 10, 15, 20, 13, 0, 16, 6, 11, 9, 14, 12, 19, 2, 4, 5, 3, 8, 7]
  let c5 := colMap [0, 1, 2, 12, 16, 15, 20, 7, 8, 3, 6, 11, 9, 18, 4, 17, 14, 5, 19, 13, 10] [0, 1, 19, 12, 15, 20, 6, 7, 8, 2, 11, 16, 14, 4, 3, 13, 10, 5, 18, 9, 17]
  let c5i := colMap [0, 1, 2, 9, 14, 17, 10, 7, 8, 12, 20, 11, 3, 19, 16, 5, 4, 15, 13, 18, 6] [0, 1, 9, 14, 13, 17, 6, 7, 8, 19, 16, 10, 3, 15, 12, 4, 11, 20, 18, 2, 5]
  let isAut : (Fin 42 → Fin 42) → (Fin 42 → Fin 42) → Prop := fun f g =>
    (∀ a : Fin 42, g (f a) = a) ∧ (∀ a : Fin 42, f (g a) = a) ∧ (∀ a b : Fin 42, adj (f a) (f b) ↔ adj a b)
  let checkCol (pm lm pmi lmi : List ℕ) : Bool :=
    (List.range 21).all (fun p =>
      let fp := pm.getD p 0
      fp < 21 && pmi.getD fp 0 == p && pm.getD (pmi.getD p 0) 0 == p && pmi.getD p 0 < 21) &&
    (List.range 21).all (fun l =>
      let fl := lm.getD l 0
      fl < 21 && lmi.getD fl 0 == l && lm.getD (lmi.getD l 0) 0 == l && lmi.getD l 0 < 21) &&
    (List.range 21).all (fun p =>
      let fp := pm.getD p 0
      (List.range 21).all (fun l =>
        let fl := lm.getD l 0
        (((fl + 21 - fp) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) == ((l + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))))
  have hcheckCol_ok : ∀ (pm lm pmi lmi : List ℕ), checkCol pm lm pmi lmi = true →
      isAut (colMap pm lm) (colMap pmi lmi) := by
    intro pm lm pmi lmi hck
    dsimp only [checkCol] at hck
    rw [Bool.and_eq_true, Bool.and_eq_true] at hck
    have hp_all := List.all_eq_true.mp hck.1.1
    have hl_all := List.all_eq_true.mp hck.1.2
    have he_all := List.all_eq_true.mp hck.2
    have hpm_lt : ∀ p < 21, pm.getD p 0 < 21 := by
      intro p hp
      have h := hp_all p (List.mem_range.mpr hp)
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact of_decide_eq_true h.1.1.1
    have hpmi_lt : ∀ p < 21, pmi.getD p 0 < 21 := by
      intro p hp
      have h := hp_all p (List.mem_range.mpr hp)
      rw [Bool.and_eq_true] at h
      exact of_decide_eq_true h.2
    have hpm_li : ∀ p < 21, pmi.getD (pm.getD p 0) 0 = p := by
      intro p hp
      have h := hp_all p (List.mem_range.mpr hp)
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact eq_of_beq h.1.1.2
    have hpm_ri : ∀ p < 21, pm.getD (pmi.getD p 0) 0 = p := by
      intro p hp
      have h := hp_all p (List.mem_range.mpr hp)
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact eq_of_beq h.1.2
    have hlm_lt : ∀ l < 21, lm.getD l 0 < 21 := by
      intro l hl
      have h := hl_all l (List.mem_range.mpr hl)
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact of_decide_eq_true h.1.1.1
    have hlmi_lt : ∀ l < 21, lmi.getD l 0 < 21 := by
      intro l hl
      have h := hl_all l (List.mem_range.mpr hl)
      rw [Bool.and_eq_true] at h
      exact of_decide_eq_true h.2
    have hlm_li : ∀ l < 21, lmi.getD (lm.getD l 0) 0 = l := by
      intro l hl
      have h := hl_all l (List.mem_range.mpr hl)
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact eq_of_beq h.1.1.2
    have hlm_ri : ∀ l < 21, lm.getD (lmi.getD l 0) 0 = l := by
      intro l hl
      have h := hl_all l (List.mem_range.mpr hl)
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact eq_of_beq h.1.2
    have hE_pres : ∀ a b : Fin 42, E (colMap pm lm a) (colMap pm lm b) ↔ E a b := by
      intro a b
      dsimp only [E, colMap]
      by_cases ha : a.val < 21 <;> by_cases hb : b.val < 21
      · rw [if_pos ha, if_pos hb]
        have h1 : (Fin.ofNat 42 (pm.getD a.val 0)).val = pm.getD a.val 0 := Nat.mod_eq_of_lt (by have := hpm_lt a.val ha; omega)
        have h2 : (Fin.ofNat 42 (pm.getD b.val 0)).val = pm.getD b.val 0 := Nat.mod_eq_of_lt (by have := hpm_lt b.val hb; omega)
        have h3 := hpm_lt b.val hb
        constructor <;> intro h <;> omega
      · rw [if_pos ha, if_neg hb]
        have hb21 : b.val - 21 < 21 := by have := b.isLt; omega
        have h1 : (Fin.ofNat 42 (pm.getD a.val 0)).val = pm.getD a.val 0 := Nat.mod_eq_of_lt (by have := hpm_lt a.val ha; omega)
        have h2 : (Fin.ofNat 42 (21 + lm.getD (b.val - 21) 0)).val = 21 + lm.getD (b.val - 21) 0 := Nat.mod_eq_of_lt (by have := hlm_lt (b.val - 21) hb21; omega)
        have hfp := hpm_lt a.val ha
        have hfl := hlm_lt (b.val - 21) hb21
        have hstep := List.all_eq_true.mp (he_all a.val (List.mem_range.mpr ha)) (b.val - 21) (List.mem_range.mpr hb21)
        have hiff : (lm.getD (b.val - 21) 0 + 21 - pm.getD a.val 0) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ↔
            (b.val - 21 + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
          have heq := eq_of_beq hstep
          constructor
          · intro h; exact of_decide_eq_true (heq.symm.trans (decide_eq_true h))
          · intro h; exact of_decide_eq_true (heq.trans (decide_eq_true h))
        have hm1 : (21 + lm.getD (b.val - 21) 0 + 21 - pm.getD a.val 0) % 21 =
            (lm.getD (b.val - 21) 0 + 21 - pm.getD a.val 0) % 21 := by
          have : 21 + lm.getD (b.val - 21) 0 + 21 - pm.getD a.val 0 =
              (lm.getD (b.val - 21) 0 + 21 - pm.getD a.val 0) + 21 := by omega
          rw [this, Nat.add_mod_right]
        have hm2 : (b.val + 21 - a.val) % 21 = (b.val - 21 + 21 - a.val) % 21 := by
          have : b.val + 21 - a.val = (b.val - 21 + 21 - a.val) + 21 := by omega
          rw [this, Nat.add_mod_right]
        rw [h1, h2, hm1, hm2]
        constructor
        · intro h; exact ⟨ha, by omega, hiff.mp h.2.2⟩
        · intro h; exact ⟨hfp, by omega, hiff.mpr h.2.2⟩
      · rw [if_neg ha, if_pos hb]
        have ha21 : a.val - 21 < 21 := by have := a.isLt; omega
        have h1 : (Fin.ofNat 42 (21 + lm.getD (a.val - 21) 0)).val = 21 + lm.getD (a.val - 21) 0 := Nat.mod_eq_of_lt (by have := hlm_lt (a.val - 21) ha21; omega)
        constructor <;> intro h <;> omega
      · rw [if_neg ha, if_neg hb]
        have ha21 : a.val - 21 < 21 := by have := a.isLt; omega
        have h1 : (Fin.ofNat 42 (21 + lm.getD (a.val - 21) 0)).val = 21 + lm.getD (a.val - 21) 0 := Nat.mod_eq_of_lt (by have := hlm_lt (a.val - 21) ha21; omega)
        constructor <;> intro h <;> omega
    refine ⟨?_, ?_, fun a b => or_congr (hE_pres a b) (hE_pres b a)⟩
    · intro a
      dsimp only [colMap]
      by_cases ha : a.val < 21
      · rw [if_pos ha]
        have hfp := hpm_lt a.val ha
        have h1 : (Fin.ofNat 42 (pm.getD a.val 0)).val = pm.getD a.val 0 := Nat.mod_eq_of_lt (by omega)
        rw [if_pos (by rw [h1]; exact hfp), h1, hpm_li a.val ha]
        exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
      · rw [if_neg ha]
        have ha21 : a.val - 21 < 21 := by have := a.isLt; omega
        have hfl := hlm_lt (a.val - 21) ha21
        have h1 : (Fin.ofNat 42 (21 + lm.getD (a.val - 21) 0)).val = 21 + lm.getD (a.val - 21) 0 := Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by rw [h1]; omega), h1, Nat.add_sub_cancel_left, hlm_li (a.val - 21) ha21]
        have hback : 21 + (a.val - 21) = a.val := by omega
        rw [hback]
        exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
    · intro a
      dsimp only [colMap]
      by_cases ha : a.val < 21
      · rw [if_pos ha]
        have hfp := hpmi_lt a.val ha
        have h1 : (Fin.ofNat 42 (pmi.getD a.val 0)).val = pmi.getD a.val 0 := Nat.mod_eq_of_lt (by omega)
        rw [if_pos (by rw [h1]; exact hfp), h1, hpm_ri a.val ha]
        exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
      · rw [if_neg ha]
        have ha21 : a.val - 21 < 21 := by have := a.isLt; omega
        have hfl := hlmi_lt (a.val - 21) ha21
        have h1 : (Fin.ofNat 42 (21 + lmi.getD (a.val - 21) 0)).val = 21 + lmi.getD (a.val - 21) 0 := Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by rw [h1]; omega), h1, Nat.add_sub_cancel_left, hlm_ri (a.val - 21) ha21]
        have hback : 21 + (a.val - 21) = a.val := by omega
        rw [hback]
        exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
  have hcomp : ∀ {f1 g1 f2 g2}, isAut f1 g1 → isAut f2 g2 → isAut (fun a => f2 (f1 a)) (fun a => g1 (g2 a)) := by
    intro f1 g1 f2 g2 h1 h2
    exact ⟨fun a => by dsimp only; rw [h2.1, h1.1], fun a => by dsimp only; rw [h1.2.1, h2.2.1],
      fun a b => (h2.2.2 _ _).trans (h1.2.2 a b)⟩
  have hcomp3 : ∀ {f1 g1 f2 g2 f3 g3}, isAut f1 g1 → isAut f2 g2 → isAut f3 g3 →
      isAut (fun a => f3 (f2 (f1 a))) (fun a => g1 (g2 (g3 a))) := by
    intro f1 g1 f2 g2 f3 g3 h1 h2 h3
    exact ⟨fun a => by dsimp only; rw [h3.1, h2.1, h1.1], fun a => by dsimp only; rw [h1.2.1, h2.2.1, h3.2.1],
      fun a b => (h3.2.2 _ _).trans ((h2.2.2 _ _).trans (h1.2.2 a b))⟩
  have hid_aut : isAut id id := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩
  have hdual_aut : isAut dual dual := by
    have hinv : ∀ a : Fin 42, dual (dual a) = a := by dsimp only [dual]; decide +kernel
    have hE_d : ∀ a b : Fin 42, E (dual a) (dual b) ↔ E b a := by
      intro a b
      dsimp only [E, dual]
      by_cases ha : a.val < 21 <;> by_cases hb : b.val < 21
      · rw [if_pos ha, if_pos hb, Fin.val_natAdd, Fin.val_natAdd]; constructor <;> intro h <;> omega
      · rw [if_pos ha, if_neg hb, Fin.val_natAdd, Fin.val_castAdd]; constructor <;> intro h <;> omega
      · rw [if_neg ha, if_pos hb, Fin.val_castAdd, Fin.val_natAdd]
        have ha21 : a.val - 21 < 21 := by have := a.isLt; omega
        have hmod : ∀ p l : Fin 21, ((21 + (-p).val + 21 - (-l).val) % 21) = ((l.val + 21 - p.val) % 21) := by decide +kernel
        have hm := hmod ⟨b.val, hb⟩ ⟨a.val - 21, ha21⟩
        have hpa : Fin.ofNat 21 (a.val - 21) = ⟨a.val - 21, ha21⟩ := Fin.ext (Nat.mod_eq_of_lt ha21)
        have hpb : Fin.ofNat 21 b.val = ⟨b.val, hb⟩ := Fin.ext (Nat.mod_eq_of_lt hb)
        rw [hpa, hpb]
        have hm2 : (a.val + 21 - b.val) % 21 = (a.val - 21 + 21 - b.val) % 21 := by
          have : a.val + 21 - b.val = (a.val - 21 + 21 - b.val) + 21 := by omega
          rw [this, Nat.add_mod_right]
        have hlt1 : (-⟨a.val - 21, ha21⟩ : Fin 21).val < 21 := Fin.isLt _
        have hge2 : 21 ≤ 21 + (-⟨b.val, hb⟩ : Fin 21).val := by omega
        rw [hm, ← hm2]
        constructor
        · intro h; exact ⟨hb, by omega, h.2.2⟩
        · intro h; exact ⟨hlt1, hge2, h.2.2⟩
      · rw [if_neg ha, if_neg hb, Fin.val_castAdd, Fin.val_castAdd]
        have hlt2 : (-Fin.ofNat 21 (b.val - 21)).val < 21 := Fin.isLt _
        constructor <;> intro h <;> omega
    exact ⟨hinv, hinv, fun a b => ⟨fun h => h.elim (fun h1 => Or.inr ((hE_d a b).mp h1)) (fun h2 => Or.inl ((hE_d b a).mp h2)),
      fun h => h.elim (fun h1 => Or.inr ((hE_d b a).mpr h1)) (fun h2 => Or.inl ((hE_d a b).mpr h2))⟩⟩
  have hshift_aut : ∀ c : Fin 21, isAut (shift c) (shift (-c)) := by
    intro c
    have hE_s : ∀ a b : Fin 42, E (shift c a) (shift c b) ↔ E a b := by
      intro a b
      dsimp only [E, shift]
      by_cases ha : a.val < 21 <;> by_cases hb : b.val < 21
      · rw [if_pos ha, if_pos hb, Fin.val_castAdd, Fin.val_castAdd]
        have hlt := (Fin.ofNat 21 b.val - c).isLt
        constructor <;> intro h <;> omega
      · rw [if_pos ha, if_neg hb, Fin.val_castAdd, Fin.val_natAdd]
        have hb21 : b.val - 21 < 21 := by have := b.isLt; omega
        have hpa : Fin.ofNat 21 a.val = ⟨a.val, ha⟩ := Fin.ext (Nat.mod_eq_of_lt ha)
        have hpb : Fin.ofNat 21 (b.val - 21) = ⟨b.val - 21, hb21⟩ := Fin.ext (Nat.mod_eq_of_lt hb21)
        rw [hpa, hpb]
        have hsub21 : ∀ x y : Fin 21, (21 + x.val + 21 - y.val) % 21 = (x - y).val := by decide +kernel
        have hsub21b : ∀ x y : Fin 21, (x.val + 21 - y.val) % 21 = (x - y).val := by decide +kernel
        have hmod : ∀ p l c0 : Fin 21, ((21 + (l - c0).val + 21 - (p - c0).val) % 21) = ((l.val + 21 - p.val) % 21) := by
          intro p l c0
          rw [hsub21, hsub21b, sub_sub_sub_cancel_right]
        have hm := hmod ⟨a.val, ha⟩ ⟨b.val - 21, hb21⟩ c
        have hm2 : (b.val + 21 - a.val) % 21 = (b.val - 21 + 21 - a.val) % 21 := by
          have : b.val + 21 - a.val = (b.val - 21 + 21 - a.val) + 21 := by omega
          rw [this, Nat.add_mod_right]
        rw [hm, ← hm2]
        constructor
        · intro h; exact ⟨ha, by omega, h.2.2⟩
        · intro h; exact ⟨Fin.isLt _, by omega, h.2.2⟩
      · rw [if_neg ha, if_pos hb, Fin.val_natAdd, Fin.val_castAdd]; constructor <;> intro h <;> omega
      · rw [if_neg ha, if_neg hb, Fin.val_natAdd, Fin.val_natAdd]; constructor <;> intro h <;> omega
    have hinv1 : ∀ c0 : Fin 21, ∀ a : Fin 42, shift (-c0) (shift c0 a) = a := by dsimp only [shift]; decide +kernel
    exact ⟨hinv1 c, fun a => by have := hinv1 (-c) a; rw [neg_neg] at this; exact this,
      fun a b => or_congr (hE_s a b) (hE_s b a)⟩
  have hfrob_aut : isAut frob frob2 := by
    have hinv1 : ∀ a : Fin 42, frob2 (frob a) = a := by dsimp only [frob, frob2]; decide +kernel
    have hinv2 : ∀ a : Fin 42, frob (frob2 a) = a := by dsimp only [frob, frob2]; decide +kernel
    have hE_f : ∀ a b : Fin 42, E (frob a) (frob b) ↔ E a b := by
      intro a b
      dsimp only [E, frob]
      by_cases ha : a.val < 21 <;> by_cases hb : b.val < 21
      · rw [if_pos ha, if_pos hb, Fin.val_castAdd, Fin.val_castAdd]
        have hlt := (4 * Fin.ofNat 21 b.val).isLt; constructor <;> intro h <;> omega
      · rw [if_pos ha, if_neg hb, Fin.val_castAdd, Fin.val_natAdd]
        have hb21 : b.val - 21 < 21 := by have := b.isLt; omega
        have hpa : Fin.ofNat 21 a.val = ⟨a.val, ha⟩ := Fin.ext (Nat.mod_eq_of_lt ha)
        have hpb : Fin.ofNat 21 (b.val - 21) = ⟨b.val - 21, hb21⟩ := Fin.ext (Nat.mod_eq_of_lt hb21)
        rw [hpa, hpb]
        have hmod : ∀ p l : Fin 21,
            ((21 + (4 * l).val + 21 - (4 * p).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ↔
            ((l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := by decide +kernel
        have hm := hmod ⟨a.val, ha⟩ ⟨b.val - 21, hb21⟩
        have hm2 : (b.val + 21 - a.val) % 21 = (b.val - 21 + 21 - a.val) % 21 := by
          have : b.val + 21 - a.val = (b.val - 21 + 21 - a.val) + 21 := by omega
          rw [this, Nat.add_mod_right]
        rw [hm2]
        constructor
        · intro h; exact ⟨ha, by omega, hm.mp h.2.2⟩
        · intro h; exact ⟨Fin.isLt _, by omega, hm.mpr h.2.2⟩
      · rw [if_neg ha, if_pos hb, Fin.val_natAdd, Fin.val_castAdd]; constructor <;> intro h <;> omega
      · rw [if_neg ha, if_neg hb, Fin.val_natAdd, Fin.val_natAdd]; constructor <;> intro h <;> omega
    exact ⟨hinv1, hinv2, fun a b => or_congr (hE_f a b) (hE_f b a)⟩
  have hfrob2_aut : isAut frob2 frob :=
    ⟨hfrob_aut.2.1, hfrob_aut.1, fun a b => by
      have h := hfrob_aut.2.2 (frob2 a) (frob2 b)
      rw [hfrob_aut.2.1, hfrob_aut.2.1] at h
      exact h.symm⟩
  have hc1_aut : isAut c1 c1i := hcheckCol_ok _ _ _ _ (by dsimp only [checkCol]; decide +kernel)
  have hc2_aut : isAut c2 c2i := hcheckCol_ok _ _ _ _ (by dsimp only [checkCol]; decide +kernel)
  have hc3_aut : isAut c3 c3i := hcheckCol_ok _ _ _ _ (by dsimp only [checkCol]; decide +kernel)
  have hc4_aut : isAut c4 c4i := hcheckCol_ok _ _ _ _ (by dsimp only [checkCol]; decide +kernel)
  have hc5_aut : isAut c5 c5i := hcheckCol_ok _ _ _ _ (by dsimp only [checkCol]; decide +kernel)
  have hstep1 : ∃ f1 g1, isAut f1 g1 ∧ f1 u = 0 := by
    by_cases hu21 : u.val < 21
    · refine ⟨shift (Fin.ofNat 21 u.val), shift (-Fin.ofNat 21 u.val), hshift_aut _, ?_⟩
      dsimp only [shift]
      rw [if_pos hu21, sub_self]
      rfl
    · let c : Fin 21 := -Fin.ofNat 21 (u.val - 21)
      refine ⟨fun a => shift c (dual a), fun a => dual (shift (-c) a), hcomp hdual_aut (hshift_aut c), ?_⟩
      dsimp only [dual, shift]
      rw [if_neg hu21]
      have hc21 : (Fin.castAdd 21 c).val < 21 := by rw [Fin.val_castAdd]; exact c.isLt
      rw [if_pos hc21]
      have hceq : Fin.ofNat 21 (Fin.castAdd 21 c).val = c := by
        rw [Fin.val_castAdd]
        exact Fin.ext (Nat.mod_eq_of_lt c.isLt)
      rw [hceq, sub_self]
      rfl
  rcases hstep1 with ⟨f1, g1, hf1, hfu0⟩
  have hnot_adj0w : ¬ adj 0 (f1 v) := by
    intro h0w
    apply hnot_adj
    rw [← hfu0] at h0w
    exact (hf1.2.2 u v).mp h0w
  have hcases_all : ∀ w : Fin 42, ¬ adj 0 w → (w = 0) ∨ (w = 1) ∨ (w = 2) ∨ (w = 3) ∨ (w = 4) ∨ (w = 5) ∨ (w = 6) ∨ (w = 7) ∨ (w = 8) ∨ (w = 9) ∨ (w = 10) ∨ (w = 11) ∨ (w = 12) ∨ (w = 13) ∨ (w = 14) ∨ (w = 15) ∨ (w = 16) ∨ (w = 17) ∨ (w = 18) ∨ (w = 19) ∨ (w = 20) ∨ (w = 22) ∨ (w = 23) ∨ (w = 24) ∨ (w = 25) ∨ (w = 27) ∨ (w = 29) ∨ (w = 30) ∨ (w = 31) ∨ (w = 32) ∨ (w = 33) ∨ (w = 34) ∨ (w = 35) ∨ (w = 36) ∨ (w = 37) ∨ (w = 39) ∨ (w = 40) := by
    dsimp only [adj, E]
    decide +kernel
  have horb : ∀ w : Fin 42, ¬ adj 0 w →
      ∃ f2 g2, isAut f2 g2 ∧ f2 0 = 0 ∧ (f2 w = 0 ∨ f2 w = 1 ∨ f2 w = 22) := by
    intro w hnw
    rcases hcases_all w hnw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨id, id, hid_aut, rfl, Or.inl rfl⟩
    · exact ⟨id, id, hid_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob (c1 a)), (fun a => c1i (frob2 a)), (hcomp hc1_aut hfrob_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob (c3 a)), (fun a => c3i (frob2 a)), (hcomp hc3_aut hfrob_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨c2, c2i, hc2_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob (c3 (frob a))), (fun a => frob2 (c3i (frob2 a))), (hcomp3 hfrob_aut hc3_aut hfrob_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨c1, c1i, hc1_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob (c1 (frob2 a))), (fun a => frob (c1i (frob2 a))), (hcomp3 hfrob2_aut hc1_aut hfrob_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => c3 (frob a)), (fun a => frob2 (c3i a)), (hcomp hfrob_aut hc3_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob2 (c4 a)), (fun a => c4i (frob a)), (hcomp hc4_aut hfrob2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob2 (c1 a)), (fun a => c1i (frob a)), (hcomp hc1_aut hfrob2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob (c3 (frob2 a))), (fun a => frob (c3i (frob2 a))), (hcomp3 hfrob2_aut hc3_aut hfrob_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob2 (c3 a)), (fun a => c3i (frob a)), (hcomp hc3_aut hfrob2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob2 (c5 a)), (fun a => c5i (frob a)), (hcomp hc5_aut hfrob2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨c3, c3i, hc3_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨c4, c4i, hc4_aut, by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => c3 (frob2 a)), (fun a => frob (c3i a)), (hcomp hfrob2_aut hc3_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => frob2 (c2 a)), (fun a => c2i (frob a)), (hcomp hc2_aut hfrob2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨(fun a => c2 (frob2 a)), (fun a => frob (c2i a)), (hcomp hfrob2_aut hc2_aut), by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨id, id, hid_aut, by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c1 a)), (fun a => c1i (frob2 a)), (hcomp hc1_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c3 a)), (fun a => c3i (frob2 a)), (hcomp hc3_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨frob2, frob, hfrob2_aut, by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c3 (frob a))), (fun a => frob2 (c3i (frob2 a))), (hcomp3 hfrob_aut hc3_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c1 (frob2 a))), (fun a => frob (c1i (frob2 a))), (hcomp3 hfrob2_aut hc1_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c2 a)), (fun a => c2i (frob2 a)), (hcomp hc2_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob2 (c1 a)), (fun a => c1i (frob a)), (hcomp hc1_aut hfrob2_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c5 a)), (fun a => c5i (frob2 a)), (hcomp hc5_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob2 (c3 a)), (fun a => c3i (frob a)), (hcomp hc3_aut hfrob2_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob2 (c5 a)), (fun a => c5i (frob a)), (hcomp hc5_aut hfrob2_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨c1, c1i, hc1_aut, by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob2 (c4 a)), (fun a => c4i (frob a)), (hcomp hc4_aut hfrob2_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨frob, frob2, hfrob_aut, by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob (c2 (frob a))), (fun a => frob2 (c2i (frob2 a))), (hcomp3 hfrob_aut hc2_aut hfrob_aut), by decide, Or.inr (Or.inr (by decide))⟩
    · exact ⟨(fun a => frob2 (c1 (frob2 a))), (fun a => frob (c1i (frob a))), (hcomp3 hfrob2_aut hc1_aut hfrob2_aut), by decide, Or.inr (Or.inr (by decide))⟩
  rcases horb (f1 v) hnot_adj0w with ⟨f2, g2, hf2, hf20, hf2w⟩
  have hfin := hcomp hf1 hf2
  exact hrelabel (fun a => f2 (f1 a)) (fun a => g1 (g2 a)) hfin.1 hfin.2.1 hfin.2.2 ⟨by rw [hfu0, hf20], hf2w⟩
