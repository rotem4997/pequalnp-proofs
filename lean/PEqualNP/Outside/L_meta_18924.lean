import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18924_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wstep_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private lemma foldl_wstep_getD_lt (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl wstep acc).getD j false = acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep acc g) (by simp [wstep]; omega)]
    rw [wstep, List.getD_append _ _ _ _ hj]

private lemma getD_ofFn_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma or_eval_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

-- Build left cumulative ORs
private lemma build_left (n : ℕ) (hn : 2 ≤ n) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs, 0⟩ ∧ gs.length = m ∧
        ∃ pw : ℕ → ℕ,
          (∀ k ≤ m, pw k < n + m) ∧
          (∀ (x : Fin n → Bool) (k : ℕ), k ≤ m →
            ((Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD (pw k) false =
              decide (∃ j : Fin n, j.val ≤ k ∧ x j = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun _ h => by simp at h, rfl, fun _ => 0, fun _ _ => by dsimp only; omega, ?_⟩
    intro x k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Circuit.wires, List.foldl_nil]
    rw [getD_ofFn_lt x 0 (by omega)]
    cases hx : x ⟨0, by omega⟩ with
    | false =>
      symm
      rw [decide_eq_false_iff_not]
      rintro ⟨j, hj, hxj⟩
      have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hj0] at hxj
      rw [hx] at hxj
      exact Bool.noConfusion hxj
    | true =>
      symm
      rw [decide_eq_true_eq]
      exact ⟨⟨0, by omega⟩, le_rfl, hx⟩
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, pw, hpbd, hpev⟩ := ih (by omega)
    let newG : Gate := ⟨.or, [pw m, m + 1]⟩
    let gs' : List Gate := gs ++ [newG]
    let pw' : ℕ → ℕ := fun k => if k = m + 1 then n + m else pw k
    refine ⟨gs', ?_, by simp [gs', hlen], pw', ?_, ?_⟩
    · intro g hg
      simp only [gs', List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro k hk
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · simp only [hkeq, ite_true]; omega
      · simp only [hkeq, ite_false]
        have := hpbd k (by omega)
        omega
    · intro x k hk
      set w := Circuit.wires ⟨gs, 0⟩ (List.ofFn x)
      have hwlen : w.length = n + m := by
        simp only [w, Circuit.wires]
        change (gs.foldl wstep (List.ofFn x)).length = n + m
        rw [foldl_wstep_len, List.length_ofFn, hlen]
      have hw' : Circuit.wires ⟨gs', 0⟩ (List.ofFn x) =
          w ++ [w.getD (pw m) false || w.getD (m + 1) false] := by
        unfold Circuit.wires
        change ((gs ++ [newG]).foldl wstep (List.ofFn x)) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · subst hkeq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hpev x m le_rfl
        have h2 : w.getD (m + 1) false = x ⟨m + 1, by omega⟩ := by
          simp only [w, Circuit.wires]
          change (gs.foldl wstep (List.ofFn x)).getD (m + 1) false = x ⟨m + 1, by omega⟩
          rw [foldl_wstep_getD_lt _ _ _ (by rw [List.length_ofFn]; omega)]
          exact getD_ofFn_lt x (m + 1) (by omega)
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | hxm)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨⟨m + 1, by omega⟩, le_rfl, hxm⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : j.val ≤ m
          · exact Or.inl ⟨j, hjm, hxj⟩
          · have hjeq : j = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hjeq] at hxj
            exact Or.inr hxj
      · simp only [hkeq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hpbd k (by omega))]
        exact hpev x k (by omega)

-- Build right cumulative ORs appended to gs0
private lemma build_right (n : ℕ) (hn : 2 ≤ n) (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ sw : ℕ → ℕ,
          (∀ r ≤ m, sw r < n + gs0.length + m) ∧
          (∀ (x : Fin n → Bool) (r : ℕ), r ≤ m →
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ (List.ofFn x)).getD (sw r) false =
              decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ x j = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, rfl, fun _ => n - 1, fun _ _ => by dsimp only; omega, ?_⟩
    intro x r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep (List.ofFn x)).getD (n - 1) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by rw [List.length_ofFn]; omega)]
    rw [getD_ofFn_lt x (n - 1) (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨n - 1, by omega⟩, by dsimp only; omega, h⟩
    · rintro ⟨j, hj, hxj⟩
      have hjeq : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rwa [← hjeq]
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, sw, hsbd, hsev⟩ := ih (by omega)
    let idx : ℕ := n - 1 - (m + 1)
    let newG : Gate := ⟨.or, [idx, sw m]⟩
    let gs' : List Gate := gs ++ [newG]
    let sw' : ℕ → ℕ := fun r => if r = m + 1 then n + gs0.length + m else sw r
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], sw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro r hr
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · simp only [hreq, ite_true]; omega
      · simp only [hreq, ite_false]
        have := hsbd r (by omega)
        omega
    · intro x r hr
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ (List.ofFn x)
      have hwlen : w.length = n + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep (List.ofFn x)).length = n + gs0.length + m
        rw [foldl_wstep_len, List.length_ofFn, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ (List.ofFn x) =
          w ++ [w.getD idx false || w.getD (sw m) false] := by
        unfold Circuit.wires
        dsimp only
        rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep (List.ofFn x)) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · subst hreq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hsev x m le_rfl
        have h2 : w.getD idx false = x ⟨idx, by omega⟩ := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep (List.ofFn x)).getD idx false = x ⟨idx, by omega⟩
          rw [foldl_wstep_getD_lt _ _ _ (by rw [List.length_ofFn]; omega)]
          exact getD_ofFn_lt x idx (by omega)
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (hxidx | ⟨j, hj, hxj⟩)
          · exact ⟨⟨idx, by omega⟩, by dsimp only [idx]; omega, hxidx⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : n - 1 - m ≤ j.val
          · exact Or.inr ⟨j, hjm, hxj⟩
          · have hjeq : j = ⟨idx, by omega⟩ := Fin.ext (by dsimp only [idx]; omega)
            rw [hjeq] at hxj
            exact Or.inl hxj
      · simp only [hreq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hsbd r (by omega))]
        exact hsev x r (by omega)

-- Build middle ORs combining pw (i - 1) and sw (n - 2 - i) for i = 1 .. m
private lemma build_middle (n : ℕ) (hn : 3 ≤ n) (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩)
    (pw sw : ℕ → ℕ)
    (hpbd : ∀ k ≤ n - 2, pw k < n + gs0.length)
    (hsbd : ∀ r ≤ n - 2, sw r < n + gs0.length)
    (hpev : ∀ (x : Fin n → Bool) (k : ℕ), k ≤ n - 2 →
      (Circuit.wires ⟨gs0, 0⟩ (List.ofFn x)).getD (pw k) false =
        decide (∃ j : Fin n, j.val ≤ k ∧ x j = true))
    (hsev : ∀ (x : Fin n → Bool) (r : ℕ), r ≤ n - 2 →
      (Circuit.wires ⟨gs0, 0⟩ (List.ofFn x)).getD (sw r) false =
        decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ x j = true)) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ mw : ℕ → ℕ,
          (∀ i, 1 ≤ i → i ≤ m → mw i < n + gs0.length + m) ∧
          (∀ (x : Fin n → Bool) (i : ℕ), 1 ≤ i → i ≤ m →
            (Circuit.wires ⟨gs0 ++ gs, 0⟩ (List.ofFn x)).getD (mw i) false =
              decide (∃ j : Fin n, j.val ≠ i ∧ x j = true)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], by simpa using hM0, rfl, fun _ => 0, fun _ h1 h2 => by omega, fun _ _ h1 h2 => by omega⟩
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, mw, hmbd, hmev⟩ := ih (by omega)
    let i0 : ℕ := m + 1
    let newG : Gate := ⟨.or, [pw (i0 - 1), sw (n - 2 - i0)]⟩
    let gs' : List Gate := gs ++ [newG]
    let mw' : ℕ → ℕ := fun i => if i = i0 then n + gs0.length + m else mw i
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], mw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro i hi1 hi2
      dsimp only [mw']
      by_cases hieq : i = i0
      · simp only [hieq, ite_true]; omega
      · simp only [hieq, ite_false]
        have := hmbd i hi1 (by omega)
        omega
    · intro x i hi1 hi2
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ (List.ofFn x)
      have hwlen : w.length = n + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep (List.ofFn x)).length = n + gs0.length + m
        rw [foldl_wstep_len, List.length_ofFn, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ (List.ofFn x) =
          w ++ [w.getD (pw (i0 - 1)) false || w.getD (sw (n - 2 - i0)) false] := by
        unfold Circuit.wires
        dsimp only
        rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep (List.ofFn x)) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [mw']
      by_cases hieq : i = i0
      · subst hieq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have hkeep : ∀ u < n + gs0.length, w.getD u false = (Circuit.wires ⟨gs0, 0⟩ (List.ofFn x)).getD u false := by
          intro u hu
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep (List.ofFn x)).getD u false = _
          rw [List.foldl_append]
          rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, List.length_ofFn]; exact hu)]
          rfl
        rw [hkeep _ (hpbd (i0 - 1) (by omega)), hkeep _ (hsbd (n - 2 - i0) (by omega))]
        rw [hpev x (i0 - 1) (by omega), hsev x (n - 2 - i0) (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hlt : j.val < i0
          · exact Or.inl ⟨j, by omega, hxj⟩
          · exact Or.inr ⟨j, by omega, hxj⟩
      · simp only [hieq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hmbd i hi1 (by omega))]
        exact hmev x i hi1 (by omega)

theorem leaveOneOut_main :
    ∀ (n : ℕ), ∃ C : Circuit,
      Monotone2 C ∧ C.size ≤ 3 * n - 6 ∧
      ∃ w : Fin n → ℕ, ∀ (x : Fin n → Bool) (i : Fin n),
        (C.wires (List.ofFn x)).getD (w i) false = decide (∃ j : Fin n, j ≠ i ∧ x j = true) := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], Fin.elim0, fun _ i => Fin.elim0 i⟩
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun _ => 1, ?_⟩
    intro x i
    simp only [Circuit.wires, List.foldl_nil]
    have h1 : (List.ofFn x).getD 1 false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
      rfl
    rw [h1]
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨j, hne, _⟩
    exact hne (Subsingleton.elim j i)
  by_cases hn2 : n = 2
  · subst hn2
    refine ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun i => 1 - i.val, ?_⟩
    intro x i
    simp only [Circuit.wires, List.foldl_nil]
    rw [getD_ofFn_lt x (1 - i.val) (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨⟨1 - i.val, by omega⟩, ?_, h⟩
      intro heq
      have := congrArg Fin.val heq
      dsimp only at this
      omega
    · rintro ⟨j, hne, hxj⟩
      have hjeq : j = ⟨1 - i.val, by omega⟩ := by
        apply Fin.ext
        have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
        dsimp only
        omega
      rwa [← hjeq]
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨gs1, hM1, hlen1, pw, hpbd1, hpev1⟩ := build_left n (by omega) (n - 2) le_rfl
    obtain ⟨gs2, hM2, hlen2, sw, hsbd2, hsev2⟩ := build_right n (by omega) gs1 hM1 (n - 2) le_rfl
    have hlen12 : (gs1 ++ gs2).length = 2 * (n - 2) := by
      rw [List.length_append, hlen1, hlen2]; omega
    have hpbd12 : ∀ k ≤ n - 2, pw k < n + (gs1 ++ gs2).length := by
      intro k hk; have := hpbd1 k hk; omega
    have hsbd12 : ∀ r ≤ n - 2, sw r < n + (gs1 ++ gs2).length := by
      intro r hr; have := hsbd2 r hr; omega
    have hpev12 : ∀ (x : Fin n → Bool) (k : ℕ), k ≤ n - 2 →
        (Circuit.wires ⟨gs1 ++ gs2, 0⟩ (List.ofFn x)).getD (pw k) false =
          decide (∃ j : Fin n, j.val ≤ k ∧ x j = true) := by
      intro x k hk
      unfold Circuit.wires
      change ((gs1 ++ gs2).foldl wstep (List.ofFn x)).getD (pw k) false = _
      rw [List.foldl_append]
      rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, List.length_ofFn, hlen1]; exact hpbd1 k hk)]
      exact hpev1 x k hk
    obtain ⟨gs3, hM3, hlen3, mw, hmbd3, hmev3⟩ :=
      build_middle n hn3 (gs1 ++ gs2) hM2 pw sw hpbd12 hsbd12 hpev12 hsev2 (n - 2) le_rfl
    let C : Circuit := ⟨(gs1 ++ gs2) ++ gs3, 0⟩
    have hCsize : C.size ≤ 3 * n - 6 := by
      simp only [C, Circuit.size, List.length_append, hlen1, hlen2, hlen3]
      omega
    let wout : Fin n → ℕ := fun i =>
      if i.val = 0 then sw (n - 2)
      else if i.val = n - 1 then pw (n - 2)
      else mw i.val
    refine ⟨C, hM3, hCsize, wout, ?_⟩
    intro x i
    have hkeep : ∀ u < n + (gs1 ++ gs2).length,
        (C.wires (List.ofFn x)).getD u false = (Circuit.wires ⟨gs1 ++ gs2, 0⟩ (List.ofFn x)).getD u false := by
      intro u hu
      simp only [C, Circuit.wires]
      change (((gs1 ++ gs2) ++ gs3).foldl wstep (List.ofFn x)).getD u false = _
      rw [List.foldl_append]
      rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, List.length_ofFn]; exact hu)]
      rfl
    dsimp only [wout]
    by_cases hi0 : i.val = 0
    · simp only [hi0, ite_true]
      rw [hkeep _ (hsbd12 (n - 2) le_rfl), hsev2 x (n - 2) le_rfl]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, hxj⟩
        exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
      · rintro ⟨j, hne, hxj⟩
        have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
        exact ⟨j, by omega, hxj⟩
    · simp only [hi0, ite_false]
      by_cases hin : i.val = n - 1
      · simp only [hin, ite_true]
        rw [hkeep _ (hpbd12 (n - 2) le_rfl), hpev12 x (n - 2) le_rfl]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj, hxj⟩
          exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
        · rintro ⟨j, hne, hxj⟩
          have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
          exact ⟨j, by omega, hxj⟩
      · simp only [hin, ite_false]
        rw [hmev3 x i.val (by omega) (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hne, hxj⟩
          exact ⟨j, fun h => hne (congrArg Fin.val h), hxj⟩
        · rintro ⟨j, hne, hxj⟩
          exact ⟨j, fun h => hne (Fin.ext h), hxj⟩

end PEqualNP.Outside.L_meta_18924_aux

theorem PEqualNP.Outside.L_meta_18924 : ∀ (n : ℕ), ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 * n - 6 ∧
  ∃ w : Fin n → ℕ, ∀ (x : Fin n → Bool) (i : Fin n),
    (C.wires (List.ofFn x)).getD (w i) false = decide (∃ j : Fin n, j ≠ i ∧ x j = true) := by
  exact PEqualNP.Outside.L_meta_18924_aux.leaveOneOut_main
