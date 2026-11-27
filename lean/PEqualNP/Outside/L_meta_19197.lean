import PEqualNP.Defs
-- The leave-one-out construction is adapted from the checked L_meta_18925.
-- The induction keeps only positive gate values, saving the second gate per step.

namespace PEqualNP.Outside.L_meta_19197

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

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

private lemma or_eval_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

private lemma and_eval_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

-- Build leave-one-out OR wires directly appended to `gs0` for an input slice at `[off, off + n)`
private lemma build_slice_left (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ pw : ℕ → ℕ,
          (∀ k ≤ m, pw k < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ k ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (pw k) false =
              decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, rfl, fun _ => off, fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD off false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨0, by omega⟩, le_rfl, by simpa using h⟩
    · rintro ⟨j, hj, hxj⟩
      have hj0 : j.val = 0 := by omega
      rw [hj0, Nat.add_zero] at hxj
      exact hxj
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, pw, hpbd, hpev⟩ := ih (by omega)
    let newG : Gate := ⟨.or, [pw m, off + (m + 1)]⟩
    let gs' : List Gate := gs ++ [newG]
    let pw' : ℕ → ℕ := fun k => if k = m + 1 then N + gs0.length + m else pw k
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], pw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
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
    · intro inp hlen_inp k hk
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw m) false || w.getD (off + (m + 1)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · subst hkeq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hpev inp hlen_inp m le_rfl
        have h2 : w.getD (off + (m + 1)) false = inp.getD (off + (m + 1)) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + (m + 1)) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
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
          · have hjeq : j.val = m + 1 := by omega
            rw [hjeq] at hxj
            exact Or.inr hxj
      · simp only [hkeq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hpbd k (by omega))]
        exact hpev inp hlen_inp k (by omega)

private lemma build_slice_right (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ sw : ℕ → ℕ,
          (∀ r ≤ m, sw r < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ r ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (sw r) false =
              decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, rfl, fun _ => off + (n - 1), fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (n - 1)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨n - 1, by omega⟩, by dsimp only; omega, h⟩
    · rintro ⟨j, hj, hxj⟩
      have hjeq : j.val = n - 1 := by omega
      rwa [← hjeq]
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, sw, hsbd, hsev⟩ := ih (by omega)
    let idx : ℕ := n - 1 - (m + 1)
    let newG : Gate := ⟨.or, [off + idx, sw m]⟩
    let gs' : List Gate := gs ++ [newG]
    let sw' : ℕ → ℕ := fun r => if r = m + 1 then N + gs0.length + m else sw r
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
    · intro inp hlen_inp r hr
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (off + idx) false || w.getD (sw m) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · subst hreq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hsev inp hlen_inp m le_rfl
        have h2 : w.getD (off + idx) false = inp.getD (off + idx) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + idx) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
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
          · have hjeq : j.val = idx := by dsimp only [idx]; omega
            rw [hjeq] at hxj
            exact Or.inl hxj
      · simp only [hreq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hsbd r (by omega))]
        exact hsev inp hlen_inp r (by omega)

private lemma build_slice_mid (N off n : ℕ) (hn : 3 ≤ n) (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩)
    (pw sw : ℕ → ℕ)
    (hpbd : ∀ k ≤ n - 2, pw k < N + gs0.length)
    (hsbd : ∀ r ≤ n - 2, sw r < N + gs0.length)
    (hpev : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (pw k) false =
        decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))
    (hsev : ∀ (inp : List Bool), inp.length = N → ∀ r ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (sw r) false =
        decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true)) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ mw : ℕ → ℕ,
          (∀ i, 1 ≤ i → i ≤ m → mw i < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ i, 1 ≤ i → i ≤ m →
            (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (mw i) false =
              decide (∃ j : Fin n, j.val ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], by simpa using hM0, rfl, fun _ => 0, fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega⟩
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, mw, hmbd, hmev⟩ := ih (by omega)
    let i0 : ℕ := m + 1
    let newG : Gate := ⟨.or, [pw (i0 - 1), sw (n - 2 - i0)]⟩
    let gs' : List Gate := gs ++ [newG]
    let mw' : ℕ → ℕ := fun i => if i = i0 then N + gs0.length + m else mw i
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
    · intro inp hlen_inp i hi1 hi2
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw (i0 - 1)) false || w.getD (sw (n - 2 - i0)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [mw']
      by_cases hieq : i = i0
      · subst hieq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have hkeep : ∀ u < N + gs0.length, w.getD u false = (Circuit.wires ⟨gs0, 0⟩ inp).getD u false := by
          intro u hu
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD u false = _
          rw [List.foldl_append]
          rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
          rfl
        rw [hkeep _ (hpbd (i0 - 1) (by omega)), hkeep _ (hsbd (n - 2 - i0) (by omega))]
        rw [hpev inp hlen_inp (i0 - 1) (by omega), hsev inp hlen_inp (n - 2 - i0) (by omega)]
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
        exact hmev inp hlen_inp i hi1 (by omega)

private inductive Rail where
  | ff : Rail
  | tt : Rail
  | wire : ℕ → Rail

private def evalRail (dw : List Bool) : Rail → Bool
  | .ff => false
  | .tt => true
  | .wire i => dw.getD i false

private def railBound (L : ℕ) : Rail → Prop
  | .ff => True
  | .tt => True
  | .wire i => i < L

private lemma railBound_mono {L1 L2 : ℕ} (h : L1 ≤ L2) : ∀ {r : Rail}, railBound L1 r → railBound L2 r
  | .ff, _ => trivial
  | .tt, _ => trivial
  | .wire _, hi => Nat.lt_of_lt_of_le hi h

private lemma build_slice_loo (N off n : ℕ) (hn : 1 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length ≤ 3 * n - 6 ∧
      ∃ r : Fin n → Rail,
        (∀ i, railBound (N + gs0.length + gs.length) (r i)) ∧
        (∀ i, r i ≠ .tt) ∧
        (∀ (inp : List Bool), inp.length = N → ∀ i : Fin n,
          evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) (r i) =
            decide (∃ j : Fin n, j ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨[], by simpa using hM0, by simp, fun _ => .ff, fun _ => trivial, fun _ h => Rail.noConfusion h, ?_⟩
    intro inp _ i
    symm
    dsimp only [evalRail]
    rw [decide_eq_false_iff_not]
    rintro ⟨j, hne, _⟩
    exact hne (Subsingleton.elim j i)
  by_cases hn2 : n = 2
  · subst hn2
    refine ⟨[], by simpa using hM0, by simp, fun i => .wire (off + (1 - i.val)),
      fun i => by dsimp only [railBound]; omega, fun _ h => Rail.noConfusion h, ?_⟩
    intro inp hlen i
    simp only [evalRail, List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (1 - i.val)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
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
      have hjeq : j.val = 1 - i.val := by
        have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
        omega
      rwa [← hjeq]
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨gs1, hM1, hlen1, pw, hpbd1, hpev1⟩ := build_slice_left N off n (by omega) hbound gs0 hM0 (n - 2) le_rfl
    obtain ⟨gs2, hM2, hlen2, sw, hsbd2, hsev2⟩ := build_slice_right N off n (by omega) hbound (gs0 ++ gs1) hM1 (n - 2) le_rfl
    have hlen012 : ((gs0 ++ gs1) ++ gs2).length = gs0.length + 2 * (n - 2) := by
      simp only [List.length_append, hlen1, hlen2]; omega
    have hpbd12 : ∀ k ≤ n - 2, pw k < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro k hk; have := hpbd1 k hk; omega
    have hsbd12 : ∀ r ≤ n - 2, sw r < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro r hr; have := hsbd2 r hr; simp only [List.length_append, hlen1] at this; omega
    have hpev12 : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
        (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD (pw k) false =
          decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true) := by
      intro inp hlen_inp k hk
      unfold Circuit.wires
      change (((gs0 ++ gs1) ++ gs2).foldl wstep inp).getD (pw k) false = _
      rw [List.foldl_append]
      rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp, List.length_append, hlen1]; have := hpbd1 k hk; omega)]
      exact hpev1 inp hlen_inp k hk
    obtain ⟨gs3, hM3, hlen3, mw, hmbd3, hmev3⟩ :=
      build_slice_mid N off n hn3 ((gs0 ++ gs1) ++ gs2) hM2 pw sw hpbd12 hsbd12 hpev12 hsev2 (n - 2) le_rfl
    let gtot : List Gate := (gs1 ++ gs2) ++ gs3
    have hassoc : gs0 ++ gtot = ((gs0 ++ gs1) ++ gs2) ++ gs3 := by
      simp [gtot, List.append_assoc]
    let r : Fin n → Rail := fun i =>
      if i.val = 0 then .wire (sw (n - 2))
      else if i.val = n - 1 then .wire (pw (n - 2))
      else .wire (mw i.val)
    refine ⟨gtot, ?_, ?_, r, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gtot at hg
      rw [hassoc] at hg
      exact hM3 g hg
    · simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
    · intro i
      dsimp only [r]
      have htot : N + gs0.length + gtot.length = N + ((gs0 ++ gs1) ++ gs2).length + (n - 2) := by
        simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true, railBound]; have := hsbd12 (n - 2) le_rfl; omega
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true, railBound]; have := hpbd12 (n - 2) le_rfl; omega
        · simp only [hin, ite_false, railBound]; have := hmbd3 i.val (by omega) (by omega); omega
    · intro i
      dsimp only [r]
      split_ifs <;> intro h <;> cases h
    · intro inp hlen_inp i
      have hkeep : ∀ u < N + ((gs0 ++ gs1) ++ gs2).length,
          (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp).getD u false =
          (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD u false := by
        intro u hu
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change ((((gs0 ++ gs1) ++ gs2) ++ gs3).foldl wstep inp).getD u false = _
        rw [List.foldl_append]
        rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
        rfl
      dsimp only [r]
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true, evalRail]
        rw [hkeep _ (hsbd12 (n - 2) le_rfl), hsev2 inp hlen_inp (n - 2) le_rfl]
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
        · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true, evalRail]
          rw [hkeep _ (hpbd12 (n - 2) le_rfl), hpev12 inp hlen_inp (n - 2) le_rfl]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
          · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
        · simp only [hin, ite_false, evalRail]
          have heq : (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp) = Circuit.wires ⟨((gs0 ++ gs1) ++ gs2) ++ gs3, 0⟩ inp := by
            unfold Circuit.wires; dsimp only; rw [hassoc]
          rw [heq, hmev3 inp hlen_inp i.val (by omega) (by omega)]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (congrArg Fin.val h), hxj⟩
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (Fin.ext h), hxj⟩

private def railAnd (base : ℕ) (gs : List Gate) (r1 r2 : Rail) : List Gate × Rail :=
  match r1, r2 with
  | .ff, _ => (gs, .ff)
  | _, .ff => (gs, .ff)
  | .tt, r2 => (gs, r2)
  | r1, .tt => (gs, r1)
  | .wire a, .wire b => (gs ++ [⟨.and, [a, b]⟩], .wire (base + gs.length))

private def railOr (base : ℕ) (gs : List Gate) (r1 r2 : Rail) : List Gate × Rail :=
  match r1, r2 with
  | .tt, _ => (gs, .tt)
  | _, .tt => (gs, .tt)
  | .ff, r2 => (gs, r2)
  | r1, .ff => (gs, r1)
  | .wire a, .wire b => (gs ++ [⟨.or, [a, b]⟩], .wire (base + gs.length))

private lemma railAnd_spec (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (r1 r2 : Rail) (hb1 : railBound (N + gs0.length + gs.length) r1) (hb2 : railBound (N + gs0.length + gs.length) r2) :
    let res := railAnd (N + gs0.length) gs r1 r2
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧
    gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + 1 ∧
    (res.2 = .tt → res.1.length = gs.length) ∧
    railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false = (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        (evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r1 && evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r2)) := by
  cases r1 <;> cases r2
  all_goals
    dsimp only [railAnd]
    try (refine ⟨hM, le_rfl, by omega, fun _ => rfl, ?_, fun inp _ => ⟨fun _ _ => rfl, ?_⟩⟩
         · first | trivial | exact hb1 | exact hb2
         · simp [evalRail])
  · rename_i a b
    let newG : Gate := ⟨.and, [a, b]⟩
    have hassoc : gs0 ++ (gs ++ [newG]) = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨?_, by simp, by simp, fun h => Rail.noConfusion h, by simp [railBound], ?_⟩
    · intro g hg
      change g ∈ gs0 ++ (gs ++ [newG]) at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inl rfl, by simp [newG]⟩
    · intro inp hlen_inp
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + gs.length := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = _
        rw [foldl_wstep_len, hlen_inp, List.length_append]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ (gs ++ [newG]), 0⟩ inp = w ++ [w.getD a false && w.getD b false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, and_eval_two, w, Circuit.wires]
        rfl
      constructor
      · intro u hu
        rw [hw', List.getD_append _ _ _ _ (by omega)]
      · simp only [evalRail]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp

private lemma railOr_spec (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (r1 r2 : Rail) (hb1 : railBound (N + gs0.length + gs.length) r1) (hb2 : railBound (N + gs0.length + gs.length) r2) :
    let res := railOr (N + gs0.length) gs r1 r2
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧
    gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + 1 ∧
    (res.2 = .tt → res.1.length = gs.length) ∧
    railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false = (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        (evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r1 || evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r2)) := by
  cases r1 <;> cases r2
  all_goals
    dsimp only [railOr]
    try (refine ⟨hM, le_rfl, by omega, fun _ => rfl, ?_, fun inp _ => ⟨fun _ _ => rfl, ?_⟩⟩
         · first | trivial | exact hb1 | exact hb2
         · simp [evalRail])
  · rename_i a b
    let newG : Gate := ⟨.or, [a, b]⟩
    have hassoc : gs0 ++ (gs ++ [newG]) = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨?_, by simp, by simp, fun h => Rail.noConfusion h, by simp [railBound], ?_⟩
    · intro g hg
      change g ∈ gs0 ++ (gs ++ [newG]) at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro inp hlen_inp
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + gs.length := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = _
        rw [foldl_wstep_len, hlen_inp, List.length_append]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ (gs ++ [newG]), 0⟩ inp = w ++ [w.getD a false || w.getD b false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      constructor
      · intro u hu
        rw [hw', List.getD_append _ _ _ _ (by omega)]
      · simp only [evalRail]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp

private lemma evalRail_congr {dw1 dw2 : List Bool} {L : ℕ} (h : ∀ u < L, dw1.getD u false = dw2.getD u false) :
    ∀ {r : Rail}, railBound L r → evalRail dw1 r = evalRail dw2 r
  | .ff, _ => rfl
  | .tt, _ => rfl
  | .wire i, hi => h i hi

private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]


open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
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
      simp only [coneStep, List.getD_eq_getElem?_getD]
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
        simp only [coneStep, List.getD_eq_getElem?_getD]
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
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
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


lemma cone_lt (N : ℕ) (C : Circuit) (i j : ℕ) (h : InCone N C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨hj,k,hkj,hw,hi⟩ := (inCone_iff N C i j).mp h
    rcases hi with rfl | hi
    · exact hkj
    · exact lt_trans (ih k hkj hi) hkj

lemma cone_trans (N : ℕ) (C : Circuit) (i j k : ℕ)
    (hij : InCone N C i j) (hjk : InCone N C j k) : InCone N C i k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨hk,r,hrk,hw,hjr⟩ := (inCone_iff N C j k).mp hjk
    apply (inCone_iff N C i k).mpr
    refine ⟨hk,r,hrk,hw,Or.inr ?_⟩
    rcases hjr with rfl | hjr
    · exact hij
    · exact ih r hrk hjr

def Under (N : ℕ) (C : Circuit) (i h : ℕ) : Prop := i = h ∨ InCone N C i h

instance (N : ℕ) (C : Circuit) (i h : ℕ) : Decidable (Under N C i h) := by
  unfold Under; infer_instance

lemma under_trans {N : ℕ} {C : Circuit} {i j h : ℕ}
    (hi : Under N C i j) (hj : Under N C j h) : Under N C i h := by
  rcases hi with rfl | hi
  · exact hj
  rcases hj with rfl | hj
  · exact Or.inr hi
  · exact Or.inr (cone_trans N C i j h hi hj)

lemma under_le {N : ℕ} {C : Circuit} {i h : ℕ} (hi : Under N C i h) : i ≤ h := by
  rcases hi with rfl | hi
  · exact le_rfl
  · exact le_of_lt (cone_lt N C i h hi)

def Shared (N : ℕ) (C : Circuit) (p h i : ℕ) : Prop :=
  Under N C i h ∧ ∃ r < C.gates.length, Under N C r h ∧ Under N C i r ∧
    (C.output = N + r ∨ ∃ j < C.gates.length, ¬ Under N C j h ∧ j ≠ p ∧
      N + r ∈ (gateAt C j).inputs)

instance (N : ℕ) (C : Circuit) (p h i : ℕ) : Decidable (Shared N C p h i) := by
  unfold Shared; infer_instance

def PosNeed (N : ℕ) (C : Circuit) (p h i : ℕ) : Prop :=
  ¬ Under N C i h ∨ Shared N C p h i

instance (N : ℕ) (C : Circuit) (p h i : ℕ) : Decidable (PosNeed N C p h i) := by
  unfold PosNeed; infer_instance

lemma shared_down {N : ℕ} {C : Circuit} {p h i j : ℕ}
    (hij : Under N C i j) (hj : Shared N C p h j) : Shared N C p h i := by
  obtain ⟨hjh,r,hr,hrh,hjr,he⟩ := hj
  exact ⟨under_trans hij hjh,r,hr,hrh,under_trans hij hjr,he⟩

lemma operand_under {N : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (hw : N + i ∈ (gateAt C j).inputs) :
    Under N C i j :=
  Or.inr ((inCone_iff N C i j).mpr ⟨hj,i,hi,hw,Or.inl rfl⟩)

lemma negative_closed {N : ℕ} {C : Circuit} {h i j : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (hw : N + i ∈ (gateAt C j).inputs)
    (hn : Under N C j h) : Under N C i h :=
  under_trans (operand_under hj hi hw) hn

lemma positive_closed {N : ℕ} {C : Circuit} {p h i j : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (hw : N + i ∈ (gateAt C j).inputs)
    (hjp : j ≠ p) (hn : PosNeed N C p h j) : PosNeed N C p h i := by
  by_cases hih : Under N C i h
  · right
    rcases hn with hjh | hsh
    · exact ⟨hih,i,by omega,hih,Or.inl rfl,Or.inr ⟨j,hj,hjh,hjp,hw⟩⟩
    · exact shared_down (operand_under hj hi hw) hsh
  · exact Or.inl hih

lemma output_positive {N : ℕ} {C : Circuit} {p h i : ℕ}
    (hi : i < C.gates.length) (ho : C.output = N + i) : PosNeed N C p h i := by
  by_cases hih : Under N C i h
  · exact Or.inr ⟨hih,i,hi,hih,Or.inl rfl,Or.inl ho⟩
  · exact Or.inl hih

private def emit (base : ℕ) (gs : List Gate) (isAnd : Bool) (rs : List Rail) : List Gate × Rail :=
  match rs with
  | [] => (gs, if isAnd then .tt else .ff)
  | [r] => (gs,r)
  | [a,b] => if isAnd then railAnd base gs a b else railOr base gs a b
  | _ => (gs,.ff)

private def railEvalList (dw : List Bool) (isAnd : Bool) (rs : List Rail) : Bool :=
  if isAnd then (rs.map (evalRail dw)).all id else (rs.map (evalRail dw)).any id

private lemma emit_spec (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (isAnd : Bool) (rs : List Rail) (hl : rs.length ≤ 2)
    (hb : ∀ r ∈ rs, railBound (N + gs0.length + gs.length) r) :
    let res := emit (N + gs0.length) gs isAnd rs
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧ gs.length ≤ res.1.length ∧
    res.1.length ≤ gs.length + 1 ∧ railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false =
        (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        railEvalList (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) isAnd rs) := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
  · cases isAnd <;> dsimp only [emit]
    all_goals exact ⟨hM,le_rfl,by omega,trivial,fun _ _ => ⟨fun _ _ => rfl,rfl⟩⟩
  · dsimp only [emit]
    refine ⟨hM,le_rfl,by omega,hb a (by simp),?_⟩
    intro inp hi
    refine ⟨fun _ _ => rfl,?_⟩
    cases isAnd <;> simp [emit,railEvalList]
  · have ha := hb a (by simp)
    have hb' := hb b (by simp)
    cases isAnd
    · obtain ⟨h1,h2,h3,_,h4,h5⟩ := railOr_spec N gs0 gs hM a b ha hb'
      refine ⟨h1,h2,h3,h4,?_⟩
      intro inp hi
      have h := h5 inp hi
      exact ⟨h.1,by simpa [emit,railEvalList] using h.2⟩
    · obtain ⟨h1,h2,h3,_,h4,h5⟩ := railAnd_spec N gs0 gs hM a b ha hb'
      refine ⟨h1,h2,h3,h4,?_⟩
      intro inp hi
      have h := h5 inp hi
      exact ⟨h.1,by simpa [emit,railEvalList] using h.2⟩
  · simp at hl

private def emitOpt (base : ℕ) (gs : List Gate) (want isAnd : Bool) (rs : List Rail) :
    List Gate × Rail := if want then emit base gs isAnd rs else (gs,.ff)

private lemma emitOpt_spec (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (want isAnd : Bool) (rs : List Rail) (hl : rs.length ≤ 2)
    (hb : ∀ r ∈ rs, railBound (N + gs0.length + gs.length) r) :
    let res := emitOpt (N + gs0.length) gs want isAnd rs
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧ gs.length ≤ res.1.length ∧
    res.1.length ≤ gs.length + (if want then 1 else 0) ∧
    railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false =
        (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      (want = true → evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        railEvalList (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) isAnd rs)) := by
  cases want
  · exact ⟨hM,le_rfl,by simp [emitOpt],trivial,fun _ _ => ⟨fun _ _ => rfl,by simp⟩⟩
  · obtain ⟨h1,h2,h3,h4,h5⟩ := emit_spec N gs0 gs hM isAnd rs hl hb
    exact ⟨h1,h2,h3,h4,fun inp hi => ⟨(h5 inp hi).1,fun _ => (h5 inp hi).2⟩⟩

private lemma emitPair_spec (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (wp wn isAnd : Bool) (ps ns : List Rail) (hp : ps.length ≤ 2) (hn : ns.length ≤ 2)
    (hbp : ∀ r ∈ ps, railBound (N + gs0.length + gs.length) r)
    (hbn : ∀ r ∈ ns, railBound (N + gs0.length + gs.length) r) :
    ∃ (gs' : List Gate) (rp rn : Rail),
      Monotone2 ⟨gs0 ++ gs', 0⟩ ∧ gs.length ≤ gs'.length ∧
      gs'.length ≤ gs.length + (if wp then 1 else 0) + (if wn then 1 else 0) ∧
      railBound (N + gs0.length + gs'.length) rp ∧ railBound (N + gs0.length + gs'.length) rn ∧
      ∀ inp : List Bool, inp.length = N →
        (∀ u < N + gs0.length + gs.length,
          (Circuit.wires ⟨gs0 ++ gs', 0⟩ inp).getD u false =
          (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
        (wp = true → evalRail (Circuit.wires ⟨gs0 ++ gs', 0⟩ inp) rp =
          railEvalList (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) isAnd ps) ∧
        (wn = true → evalRail (Circuit.wires ⟨gs0 ++ gs', 0⟩ inp) rn =
          railEvalList (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) (!isAnd) ns) := by
  let r1 := emitOpt (N + gs0.length) gs wp isAnd ps
  obtain ⟨hM1,hge1,hle1,hb1,he1⟩ := emitOpt_spec N gs0 gs hM wp isAnd ps hp hbp
  change Monotone2 ⟨gs0 ++ r1.1,0⟩ at hM1
  change gs.length ≤ r1.1.length at hge1
  change r1.1.length ≤ gs.length + (if wp then 1 else 0) at hle1
  change railBound (N + gs0.length + r1.1.length) r1.2 at hb1
  let r2 := emitOpt (N + gs0.length) r1.1 wn (!isAnd) ns
  obtain ⟨hM2,hge2,hle2,hb2,he2⟩ := emitOpt_spec N gs0 r1.1 hM1 wn (!isAnd) ns hn
    (fun r hr => railBound_mono (by omega) (hbn r hr))
  change r1.1.length ≤ r2.1.length at hge2
  change r2.1.length ≤ r1.1.length + (if wn then 1 else 0) at hle2
  refine ⟨r2.1,r1.2,r2.2,hM2,by omega,by omega,railBound_mono (by omega) hb1,hb2,?_⟩
  intro inp hi
  have e1 := he1 inp hi
  have e2 := he2 inp hi
  refine ⟨fun u hu => (e2.1 u (by omega)).trans (e1.1 u hu),?_,?_⟩
  · intro hw
    exact (evalRail_congr e2.1 hb1).trans (e1.2 hw)
  · intro hw
    rw [e2.2 hw]
    unfold railEvalList
    have he : ns.map (evalRail (Circuit.wires ⟨gs0 ++ r1.1,0⟩ inp)) =
        ns.map (evalRail (Circuit.wires ⟨gs0 ++ gs,0⟩ inp)) := by
      exact List.map_congr_left fun r hr => evalRail_congr e1.1 (hbn r hr)
    rw [he]

private lemma rails_positive (dw : List Bool) (ia : Bool) (ws : List ℕ)
    (get : ℕ → Rail) (value : ℕ → Bool) (he : ∀ w ∈ ws, evalRail dw (get w) = value w) :
    railEvalList dw ia (ws.map get) = (if ia then GateOp.and else GateOp.or).eval (ws.map value) := by
  have hm : (ws.map get).map (evalRail dw) = ws.map value := by
    rw [List.map_map]
    exact List.map_congr_left he
  cases ia <;> simp [railEvalList,hm,GateOp.eval]

private lemma list_demorgan (xs : List Bool) :
    (xs.map Bool.not).any id = !(xs.all id) ∧
    (xs.map Bool.not).all id = !(xs.any id) := by
  induction xs with
  | nil => decide
  | cons a xs ih => cases a <;> simp_all

private lemma rails_negative (dw : List Bool) (ia : Bool) (ws : List ℕ)
    (get : ℕ → Rail) (value : ℕ → Bool) (he : ∀ w ∈ ws, evalRail dw (get w) = !(value w)) :
    railEvalList dw (!ia) (ws.map get) = !((if ia then GateOp.and else GateOp.or).eval (ws.map value)) := by
  have hm : (ws.map get).map (evalRail dw) = (ws.map value).map Bool.not := by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left he
  cases ia <;> simp only [railEvalList, Bool.not_false, Bool.not_true,
    ↓reduceIte,hm,GateOp.eval]
  · exact (list_demorgan _).2
  · exact (list_demorgan _).1

private def cost (P Q T : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred T] (k : ℕ) : ℕ :=
  if T k then 0 else (if P k then 1 else 0) + (if Q k then 1 else 0)

private def budget (P Q T : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred T] (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, cost P Q T i

private lemma budget_succ (P Q T : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred T] (k : ℕ) : budget P Q T (k+1) = budget P Q T k + cost P Q T k := by
  exact Finset.sum_range_succ _ _

set_option maxHeartbeats 0 in
private theorem simulate {X : Type} (N : ℕ) (input : X → List Bool) (hlen : ∀ x, (input x).length = N)
    (C : Circuit) (T : ℕ → Prop) [DecidablePred T] (source : ℕ → ℕ)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (hF : FanInTwo C)
    (hinfo : ∀ j < C.gates.length, T j → source j < j ∧ (gateAt C j).op = .not ∧
      (gateAt C j).inputs.head? = some (N+source j))
    (huniq : ∀ j < C.gates.length, (gateAt C j).op = .not → T j)
    (hNsrc : ∀ j < C.gates.length, T j → P j → Q (source j))
    (hPsrc : ∀ j < C.gates.length, T j → Q j → P (source j))
    (hPC : ∀ j < C.gates.length, ¬ T j → P j → ∀ i < j,
      N+i ∈ (gateAt C j).inputs → P i)
    (hQC : ∀ j < C.gates.length, Q j → ∀ i < j,
      N+i ∈ (gateAt C j).inputs → Q i)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0,0⟩) (pos0 neg0 : ℕ → Rail)
    (hb0 : ∀ w < N, railBound (N+gs0.length) (pos0 w) ∧ railBound (N+gs0.length) (neg0 w))
    (he0 : ∀ x w, w < N → evalRail (Circuit.wires ⟨gs0,0⟩ (input x)) (pos0 w) = (input x).getD w false ∧
      evalRail (Circuit.wires ⟨gs0,0⟩ (input x)) (neg0 w) = !((input x).getD w false)) :
    ∀ k ≤ C.gates.length, ∃ (gs : List Gate) (pm nm : ℕ → Rail),
      Monotone2 ⟨gs0++gs,0⟩ ∧ gs.length ≤ budget P Q T k ∧
      (∀ w < N+k, railBound (N+gs0.length+gs.length) (pm w) ∧
        railBound (N+gs0.length+gs.length) (nm w)) ∧
      ∀ x w, w < N+k →
        ((w < N ∨ P (w-N)) → evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (pm w) =
          ((C.gates.take k).foldl wstep (input x)).getD w false) ∧
        ((w < N ∨ Q (w-N)) → evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (nm w) =
          !(((C.gates.take k).foldl wstep (input x)).getD w false)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[],pos0,neg0,by simpa using hM0,by simp [budget],?_,?_⟩
    · simpa using hb0
    · intro x w hw
      have he := he0 x w (by simpa using hw)
      exact ⟨fun _ => by simpa using he.1,fun _ => by simpa using he.2⟩
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := by omega
    obtain ⟨gs,pm,nm,hM,hsize,hbd,hev⟩ := ih (by omega)
    let g := C.gates[k]
    have hga : gateAt C k = g := by
      simp [gateAt,List.getD_eq_getElem?_getD,hk,g]
    have hgmem : g ∈ C.gates := List.getElem_mem hk
    have hgl : g.inputs.length ≤ 2 := (hF g hgmem).2
    have hgo : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using (hF g hgmem).1
    let getP (i : ℕ) : Rail := if i < N+k then pm i else .ff
    let getN (i : ℕ) : Rail := if i < N+k then nm i else .tt
    have getbd (i : ℕ) : railBound (N+gs0.length+gs.length) (getP i) ∧
        railBound (N+gs0.length+gs.length) (getN i) := by
      by_cases hi : i < N+k
      · simpa [getP,getN,hi] using hbd i hi
      · simp [getP,getN,hi,railBound]
    have cwlen (x : X) : ((C.gates.take k).foldl wstep (input x)).length = N+k := by
      rw [foldl_wstep_len,hlen,List.length_take,Nat.min_eq_left (by omega)]
    have getpev (x : X) (i : ℕ) (hneed : i < N+k → i < N ∨ P (i-N)) :
        evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (getP i) =
          ((C.gates.take k).foldl wstep (input x)).getD i false := by
      by_cases hi : i < N+k
      · simpa [getP,hi] using (hev x i hi).1 (hneed hi)
      · simp only [getP,hi,ite_false,evalRail]
        rw [List.getD_eq_default _ _ (by rw [cwlen]; omega)]
    have getnev (x : X) (i : ℕ) (hneed : i < N+k → i < N ∨ Q (i-N)) :
        evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (getN i) =
          !(((C.gates.take k).foldl wstep (input x)).getD i false) := by
      by_cases hi : i < N+k
      · simpa [getN,hi] using (hev x i hi).2 (hneed hi)
      · simp only [getN,hi,ite_false,evalRail]
        rw [List.getD_eq_default _ _ (by rw [cwlen]; omega)]
        rfl
    have htake : C.gates.take (k+1) = C.gates.take k ++ [g] := List.take_succ_eq_append_getElem hk
    have finish : ∀ (gs' : List Gate) (rp rn : Rail),
        Monotone2 ⟨gs0++gs',0⟩ → gs.length ≤ gs'.length →
        gs'.length ≤ gs.length + cost P Q T k →
        railBound (N+gs0.length+gs'.length) rp → railBound (N+gs0.length+gs'.length) rn →
        (∀ x, (∀ w < N+gs0.length+gs.length,
            (Circuit.wires ⟨gs0++gs',0⟩ (input x)).getD w false =
            (Circuit.wires ⟨gs0++gs,0⟩ (input x)).getD w false) ∧
          (P k → evalRail (Circuit.wires ⟨gs0++gs',0⟩ (input x)) rp =
            g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (input x)).getD i false)) ∧
          (Q k → evalRail (Circuit.wires ⟨gs0++gs',0⟩ (input x)) rn =
            !(g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (input x)).getD i false)))) →
        ∃ (gs : List Gate) (pm nm : ℕ → Rail), Monotone2 ⟨gs0++gs,0⟩ ∧
          gs.length ≤ budget P Q T (k+1) ∧
          (∀ w < N+(k+1), railBound (N+gs0.length+gs.length) (pm w) ∧
            railBound (N+gs0.length+gs.length) (nm w)) ∧
          ∀ x w, w < N+(k+1) →
            ((w < N ∨ P (w-N)) → evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (pm w) =
              ((C.gates.take (k+1)).foldl wstep (input x)).getD w false) ∧
            ((w < N ∨ Q (w-N)) → evalRail (Circuit.wires ⟨gs0++gs,0⟩ (input x)) (nm w) =
              !(((C.gates.take (k+1)).foldl wstep (input x)).getD w false)) := by
      intro gs' rp rn hm' hge hle hbp hbn he
      let pm' := fun w => if w = N+k then rp else pm w
      let nm' := fun w => if w = N+k then rn else nm w
      refine ⟨gs',pm',nm',hm',?_,?_,?_⟩
      · rw [budget_succ]; omega
      · intro w hw
        by_cases heq : w = N+k
        · simpa [pm',nm',heq] using And.intro hbp hbn
        · have hb := hbd w (by omega)
          exact ⟨by simpa [pm',heq] using railBound_mono (by omega) hb.1,
            by simpa [nm',heq] using railBound_mono (by omega) hb.2⟩
      · intro x w hw
        obtain ⟨keep,ep,en⟩ := he x
        have ecw : (C.gates.take (k+1)).foldl wstep (input x) =
            (C.gates.take k).foldl wstep (input x) ++
              [g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (input x)).getD i false)] := by
          rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]; rfl
        by_cases heq : w = N+k
        · subst w
          rw [ecw,← cwlen x,List.getD_append_right _ _ _ _ le_rfl]
          simp only [Nat.sub_self,List.getD_cons_zero]
          rw [cwlen x]
          constructor
          · intro hh
            have hp' : P k := by rcases hh with hh | hh; omega; simpa using hh
            simpa [pm'] using ep hp'
          · intro hh
            have hn' : Q k := by rcases hh with hh | hh; omega; simpa using hh
            simpa [nm'] using en hn'
        · rw [ecw,List.getD_append _ _ _ _ (by rw [cwlen]; omega)]
          have hb := hbd w (by omega)
          have ev := hev x w (by omega)
          constructor
          · intro hn
            simpa [pm',heq] using (evalRail_congr keep hb.1).trans (ev.1 hn)
          · intro hn
            simpa [nm',heq] using (evalRail_congr keep hb.2).trans (ev.2 hn)
    by_cases hkp : T k
    · obtain ⟨hsk,hop0,hhd0⟩ := hinfo k hk hkp
      have hop : g.op = .not := by simpa [hga] using hop0
      have hhd : g.inputs.head? = some (N+source k) := by simpa [hga] using hhd0
      refine finish gs (getN (N+source k)) (getP (N+source k)) hM le_rfl
        (by simp [cost,hkp]) (getbd _).2 (getbd _).1 ?_
      intro x
      have heval : g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (input x)).getD i false) =
          !(((C.gates.take k).foldl wstep (input x)).getD (N+source k) false) := by
        rw [hop]
        cases hi : g.inputs with
        | nil => simp [hi] at hhd
        | cons a t =>
          simp only [hi,List.head?_cons,Option.some.injEq] at hhd
          subst a
          simp [GateOp.eval,hi]
      refine ⟨fun _ _ => rfl,?_,?_⟩
      · intro hpk
        rw [heval]
        exact getnev x (N+source k) (fun _ => Or.inr (by simpa using hNsrc k hk hkp hpk))
      · intro hqk
        rw [heval,Bool.not_not]
        exact getpev x (N+source k) (fun _ => Or.inr (by simpa using hPsrc k hk hkp hqk))
    · have hnon : g.op ≠ .not := by
        intro ho
        exact hkp (huniq k hk (by simpa [hga] using ho))
      obtain ⟨ia,hia⟩ : ∃ ia : Bool, g.op = if ia then GateOp.and else GateOp.or := by
        rcases hgo with ha | ho | hn
        · exact ⟨true,ha⟩
        · exact ⟨false,ho⟩
        · exact (hnon hn).elim
      obtain ⟨gs',rp,rn,hm',hge,hle,hbp,hbn,he⟩ := emitPair_spec N gs0 gs hM
        (decide (P k)) (decide (Q k)) ia (g.inputs.map getP) (g.inputs.map getN)
        (by simpa using hgl) (by simpa using hgl)
        (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr; exact (getbd i).1)
        (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr; exact (getbd i).2)
      refine finish gs' rp rn hm' hge ?_ hbp hbn ?_
      · simpa [cost,hkp,Nat.add_assoc] using hle
      · intro x
        have ex := he (input x) (hlen x)
        refine ⟨ex.1,?_,?_⟩
        · intro hpk
          rw [ex.2.1 (by simpa using hpk),hia]
          apply rails_positive
          intro i hi
          apply getpev x i
          intro hil
          by_cases hiN : i < N
          · exact Or.inl hiN
          · right
            apply hPC k hk hkp hpk (i-N) (by omega)
            have eqi : N+(i-N) = i := by omega
            simpa [hga,eqi] using hi
        · intro hqk
          rw [ex.2.2 (by simpa using hqk),hia]
          apply rails_negative
          intro i hi
          apply getnev x i
          intro hil
          by_cases hiN : i < N
          · exact Or.inl hiN
          · right
            apply hQC k hk hqk (i-N) (by omega)
            have eqi : N+(i-N) = i := by omega
            simpa [hga,eqi] using hi


private theorem makeBank (n m : ℕ) (hn1 : 1 ≤ n) (hm1 : 1 ≤ m) :
    ∃ (gs0 : List Gate) (pos0 neg0 : ℕ → Rail),
      Monotone2 ⟨gs0,0⟩ ∧ gs0.length ≤ (3*n-6)+(3*m-6) ∧
      (∀ w < n+m, railBound (n+m+gs0.length) (pos0 w) ∧ railBound (n+m+gs0.length) (neg0 w)) ∧
      ∀ (u : Fin n) (v : Fin m) w, w < n+m →
        evalRail (Circuit.wires ⟨gs0,0⟩ (oneEach u v)) (pos0 w) = (oneEach u v).getD w false ∧
        evalRail (Circuit.wires ⟨gs0,0⟩ (oneEach u v)) (neg0 w) = !((oneEach u v).getD w false) := by
  let N := n + m
  obtain ⟨gL, hML, hlenL, rL, hbdL, hntL, hevL⟩ :=
    build_slice_loo N 0 n hn1 (by omega) [] (fun _ h => by simp at h)
  obtain ⟨gR, hMR, hlenR, rR, hbdR, hntR, hevR⟩ :=
    build_slice_loo N n m hm1 (by omega) ([] ++ gL) hML
  let gs0 : List Gate := ([] ++ gL) ++ gR
  have hM0 : Monotone2 ⟨gs0, 0⟩ := hMR
  have hlen0 : gs0.length ≤ (3 * n - 6) + (3 * m - 6) := by
    simp only [gs0, List.nil_append, List.length_append]; omega
  -- Initial rail maps on wires 0 .. N-1
  let pos0 : ℕ → Rail := fun w => if w < N then .wire w else .ff
  let neg0 : ℕ → Rail := fun w =>
    if h1 : w < n then rL ⟨w, h1⟩
    else if h2 : w - n < m then rR ⟨w - n, h2⟩
    else .tt
  refine ⟨gs0,pos0,neg0,hM0,hlen0,?_,?_⟩
  · intro w hw
    constructor
    · dsimp only [pos0]
      by_cases hwn : w < N
      · simp only [hwn, ite_true, railBound]; omega
      · simp only [hwn, ite_false, railBound]
    · dsimp only [neg0]
      split_ifs with h1 h2
      · have hb := hbdL ⟨w, h1⟩
        simp only [List.length_nil, Nat.add_zero] at hb
        apply railBound_mono _ hb
        simp only [gs0, List.nil_append, List.length_append]; omega
      · have hb := hbdR ⟨w - n, h2⟩
        apply railBound_mono _ hb
        simp only [gs0, List.length_append]; omega
      · trivial
  · intro u v w hw
    have hkeep0 : ∀ idx < N,
        (Circuit.wires ⟨gs0, 0⟩ (oneEach u v)).getD idx false = (oneEach u v).getD idx false := by
      intro idx hidx
      simp only [List.append_nil, Circuit.wires]
      change (gs0.foldl wstep (oneEach u v)).getD idx false = _
      rw [foldl_wstep_getD_lt _ _ _ (by rw [oneEach_len]; exact hidx)]
    constructor
    · dsimp only [pos0]
      have hwn : w < N := by omega
      simp only [hwn, ite_true, evalRail]
      exact hkeep0 w hwn
    · dsimp only [neg0]
      by_cases h1 : w < n
      · simp only [h1, dite_true]
        have hkeepL : ∀ idx < N + ([] ++ gL).length,
            (Circuit.wires ⟨gs0, 0⟩ (oneEach u v)).getD idx false =
            (Circuit.wires ⟨[] ++ gL, 0⟩ (oneEach u v)).getD idx false := by
          intro idx hidx
          simp only [List.append_nil, gs0, Circuit.wires]
          change ((([] ++ gL) ++ gR).foldl wstep (oneEach u v)).getD idx false = _
          rw [List.foldl_append]
          rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, oneEach_len]; exact hidx)]
          rfl
        have hbL := hbdL ⟨w, h1⟩
        rw [evalRail_congr hkeepL (by simpa using hbL)]
        rw [hevL (oneEach u v) (oneEach_len u v) ⟨w, h1⟩]
        have hleft := oneEach_getD_left u v ⟨w, h1⟩
        rw [hleft]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        constructor
        · rintro ⟨j, hne, hj⟩
          have hj' := oneEach_getD_left u v j
          simp only [Nat.zero_add] at hj
          rw [hj', decide_eq_true_eq] at hj
          subst hj
          exact hne.symm
        · intro hne
          refine ⟨u, fun h => hne h.symm, ?_⟩
          simp only [Nat.zero_add]
          rw [oneEach_getD_left]
          simp
      · have h2 : w - n < m := by omega
        simp only [h1, h2, dite_false, dite_true]
        have hEqR : Circuit.wires ⟨gs0, 0⟩ (oneEach u v) =
            Circuit.wires ⟨([] ++ gL) ++ gR, 0⟩ (oneEach u v) := by simp [gs0]
        rw [hEqR, hevR (oneEach u v) (oneEach_len u v) ⟨w - n, h2⟩]
        have hw_eq : w = n + (w - n) := by omega
        conv_rhs => rw [hw_eq]
        rw [oneEach_getD_right u v ⟨w - n, h2⟩]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        constructor
        · rintro ⟨j, hne, hj⟩
          have hj' := oneEach_getD_right u v j
          rw [hj', decide_eq_true_eq] at hj
          subst hj
          exact hne.symm
        · intro hne
          refine ⟨v, fun h => hne h.symm, ?_⟩
          rw [oneEach_getD_right]
          simp



lemma exact_budget (N : ℕ) (C : Circuit) (p q : ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hp : p < C.gates.length) (hq : q < C.gates.length) (hpq : p ≠ q) :
    budget (fun _ => True) Q (fun i => i=p ∨ i=q) C.gates.length + 2 =
      C.gates.length + ((Finset.range C.gates.length).filter (fun i => i≠p ∧ i≠q ∧ Q i)).card := by
  have he : ∀ i ∈ Finset.range C.gates.length,
      cost (fun _ => True) Q (fun i => i=p ∨ i=q) i + (if i=p then 1 else 0) + (if i=q then 1 else 0) =
        1 + (if i≠p ∧ i≠q ∧ Q i then 1 else 0) := by
    intro i hi
    by_cases hip : i=p <;> by_cases hiq : i=q <;> by_cases hiQ : Q i <;> simp_all [cost]
  have hs := Finset.sum_congr (s₁ := Finset.range C.gates.length) (s₂ := Finset.range C.gates.length) rfl he
  simpa [Finset.sum_add_distrib,budget,hp,hq,Finset.sum_boole,Nat.add_assoc] using hs

set_option maxHeartbeats 0 in
theorem rep_main (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (p q h h' : ℕ)
    (hF : FanInTwo C) (hs : C.size ≤ s) (hR : Represents A C)
    (hp : p < C.gates.length) (hq : q < C.gates.length) (hpq : p ≠ q)
    (hop : (gateAt C p).op = .not) (hoq : (gateAt C q).op = .not)
    (hhead : (gateAt C p).inputs.head? = some (n+m+h))
    (hhead' : (gateAt C q).inputs.head? = some (n+m+h')) (hh : h < p) (hh' : h' < q)
    (huniq : ∀ j < C.gates.length, (gateAt C j).op = .not → j = p ∨ j = q) :
    RepSizeAtMost A (s-2 + ((Finset.range C.gates.length).filter
      (fun i => i≠p ∧ i≠q ∧ (Under (n+m) C i h ∨ Under (n+m) C i h'))).card +
      ((3*n-6)+(3*m-6))) := by
  by_cases hn0 : n = 0
  · subst n
    exact ⟨⟨[],0⟩,fun _ hg => by simp at hg,by simp [Circuit.size],fun u => Fin.elim0 u⟩
  by_cases hm0 : m = 0
  · subst m
    exact ⟨⟨[],0⟩,fun _ hg => by simp at hg,by simp [Circuit.size],fun _ v => Fin.elim0 v⟩
  obtain ⟨gs0,pos0,neg0,hM0,hlen0,hb0,he0⟩ := makeBank n m (by omega) (by omega)
  let N := n+m
  let P := fun _ : ℕ => True
  let Q := fun i => Under N C i h ∨ Under N C i h'
  let T := fun i => i=p ∨ i=q
  let source := fun i => if i=p then h else h'
  have hinfo : ∀ j < C.gates.length, T j → source j < j ∧ (gateAt C j).op = .not ∧
      (gateAt C j).inputs.head? = some (N+source j) := by
    intro j hj ht
    rcases ht with rfl | rfl
    · simpa [source,N] using And.intro hh (And.intro hop hhead)
    · simpa [source,N,Ne.symm hpq] using And.intro hh' (And.intro hoq hhead')
  have hNsrc : ∀ j < C.gates.length, T j → P j → Q (source j) := by
    intro j hj ht _
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inl (by simp [source]))
    · exact Or.inr (Or.inl (by simp [source,Ne.symm hpq]))
  have hPsrc : ∀ j < C.gates.length, T j → Q j → P (source j) := by intros; trivial
  have hPC : ∀ j < C.gates.length, ¬ T j → P j → ∀ i < j,
      N+i ∈ (gateAt C j).inputs → P i := by intros; trivial
  have hQC : ∀ j < C.gates.length, Q j → ∀ i < j,
      N+i ∈ (gateAt C j).inputs → Q i := by
    intro j hj hn i hi hw
    rcases hn with hn | hn
    · exact Or.inl (negative_closed hj hi hw hn)
    · exact Or.inr (negative_closed hj hi hw hn)
  obtain ⟨gs,pm,nm,hM,hsize,hbd,hev⟩ := simulate N
    (fun x : Fin n × Fin m => oneEach x.1 x.2) (fun x => oneEach_len x.1 x.2)
    C T source P Q hF hinfo huniq hNsrc hPsrc hPC hQC gs0 hM0 pos0 neg0 hb0
    (fun x => he0 x.1 x.2) C.gates.length le_rfl
  have hc : C.gates.length ≤ s := hs
  have hbudget := exact_budget N C p q Q hp hq hpq
  have htotal : (gs0++gs).length ≤ s-2 +
      ((Finset.range C.gates.length).filter (fun i => i≠p ∧ i≠q ∧ Q i)).card + ((3*n-6)+(3*m-6)) := by
    change gs.length ≤ budget (fun _ => True) Q (fun i => i=p ∨ i=q) C.gates.length at hsize
    rw [List.length_append]
    omega
  have hone : 1 ≤ s-2 + ((Finset.range C.gates.length).filter (fun i => i≠p ∧ i≠q ∧ Q i)).card +
      ((3*n-6)+(3*m-6)) := by omega
  let r : Rail := if C.output < N+C.gates.length then pm C.output else .ff
  have hr : ∀ (u : Fin n) (v : Fin m),
      evalRail (Circuit.wires ⟨gs0++gs,0⟩ (oneEach u v)) r = A u v := by
    intro u v
    rw [← hR u v]
    by_cases ho : C.output < N+C.gates.length
    · have hn : C.output < N ∨ P (C.output-N) := Or.inr trivial
      have he := (hev (u,v) C.output ho).1 hn
      simp only [List.take_length] at he
      change evalRail (Circuit.wires ⟨gs0++gs,0⟩ (oneEach u v)) (pm C.output) =
        C.eval (oneEach u v) at he
      simpa only [r,if_pos ho] using he
    · simp only [r,ho,ite_false,evalRail,Circuit.eval,Circuit.wires]
      change false = (C.gates.foldl wstep (oneEach u v)).getD C.output false
      rw [List.getD_eq_default _ _ (by rw [foldl_wstep_len,oneEach_len]; omega)]
  cases er : r with
  | ff =>
    refine ⟨⟨[],N⟩,fun _ hg => by simp at hg,by simp [Circuit.size],?_⟩
    intro u v
    have he := hr u v
    rw [er] at he
    change (oneEach u v).getD N false = A u v
    rw [List.getD_eq_default _ _ (by simp [oneEach_len,N])]
    exact he
  | tt =>
    refine ⟨⟨[⟨.and,[]⟩],N⟩,?_,?_,?_⟩
    · simp [Monotone2]
    · simpa [Circuit.size] using hone
    · intro u v
      have he := hr u v
      rw [er] at he
      change (oneEach u v ++ [true]).getD (n+m) false = A u v
      rw [← oneEach_len u v,List.getD_append_right _ _ _ _ le_rfl]
      simpa [evalRail] using he
  | wire w =>
    refine ⟨⟨gs0++gs,w⟩,hM,htotal,?_⟩
    intro u v
    have he := hr u v
    rw [er] at he
    exact he

end PEqualNP.Outside.L_meta_19197

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19197 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p q h h' : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → p < C.gates.length → q < C.gates.length → p ≠ q → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.head? = some (n + m + h') → h < p → h' < q → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) → PEqualNP.Represents.RepSizeAtMost A (s - 2 + ((Finset.range C.gates.length).filter (fun i => i ≠ p ∧ i ≠ q ∧ ((i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∨ (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h')))).card + ((3 * n - 6) + (3 * m - 6))) := by
  intro n m s A C p q h h2 hf hs hr hp hq hpq hop hoq hhead hhead2 hh hh2 hu
  change PEqualNP.Represents.RepSizeAtMost A (s-2 + ((Finset.range C.gates.length).filter (fun i => i≠p ∧ i≠q ∧ (PEqualNP.Outside.L_meta_19197.Under (n+m) C i h ∨ PEqualNP.Outside.L_meta_19197.Under (n+m) C i h2))).card + ((3*n-6)+(3*m-6)))
  exact PEqualNP.Outside.L_meta_19197.rep_main n m s A C p q h h2 hf hs hr hp hq hpq hop hoq hhead hhead2 hh hh2 hu
