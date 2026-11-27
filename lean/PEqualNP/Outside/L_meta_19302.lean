import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19302

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

-- Build leave-one-out OR wires directly appended to gs0 for an input slice at [off, off + n)
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

theorem rep18925 :
    ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit),
      FanInTwo C → C.size ≤ s → Represents A C →
      RepSizeAtMost A (2 * s + ((3 * n - 6) + (3 * m - 6))) := by
  intro n m s A C hF hsz hRep
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun u => Fin.elim0 u⟩
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun _ v => Fin.elim0 v⟩
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
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
  have hSim : ∀ k ≤ C.gates.length,
      ∃ (gs : List Gate) (pM nM : ℕ → Rail),
        Monotone2 ⟨gs0 ++ gs, 0⟩ ∧
        gs.length ≤ 2 * k ∧
        ((∃ w < N + k, pM w = .tt) → gs.length + 1 ≤ 2 * k) ∧
        (∀ w < N + k, railBound (N + gs0.length + gs.length) (pM w) ∧
                      railBound (N + gs0.length + gs.length) (nM w)) ∧
        (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + k →
          let cw := ((C.gates.take k).foldl wstep (oneEach u v)).getD w false
          let dw := Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)
          evalRail dw (pM w) = cw ∧ evalRail dw (nM w) = !cw) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], pos0, neg0, by simpa using hM0, by simp, ?_, ?_, ?_⟩
      · rintro ⟨w, hw, htt⟩
        dsimp only [pos0] at htt
        split_ifs at htt <;> cases htt
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
        dsimp only [List.take_zero, List.foldl_nil]
        have hkeep0 : ∀ idx < N,
            (Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v)).getD idx false = (oneEach u v).getD idx false := by
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
                (Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v)).getD idx false =
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
            have hEqR : Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v) =
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
    | succ k ih =>
      intro hk1
      have hk : k < C.gates.length := by omega
      obtain ⟨gs, pM, nM, hM, hlen, htt_ih, hbd, hev⟩ := ih (Nat.le_of_lt hk)
      set g := C.gates[k]
      have hg_mem : g ∈ C.gates := List.getElem_mem hk
      have hgF := hF g hg_mem
      have hgop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using hgF.1
      have hglen : g.inputs.length ≤ 2 := hgF.2
      -- Helper to look up wire i at step k
      let getP (i : ℕ) : Rail := if i < N + k then pM i else .ff
      let getN (i : ℕ) : Rail := if i < N + k then nM i else .tt
      have hget_bd : ∀ i, railBound (N + gs0.length + gs.length) (getP i) ∧
                          railBound (N + gs0.length + gs.length) (getN i) := by
        intro i
        dsimp only [getP, getN]
        by_cases hi : i < N + k
        · simp only [hi, ite_true]; exact hbd i hi
        · simp only [hi, ite_false]; exact ⟨trivial, trivial⟩
      have hget_ev : ∀ (u : Fin n) (v : Fin m) (i : ℕ),
          let cw := ((C.gates.take k).foldl wstep (oneEach u v)).getD i false
          let dw := Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)
          evalRail dw (getP i) = cw ∧ evalRail dw (getN i) = !cw := by
        intro u v i
        dsimp only [getP, getN]
        by_cases hi : i < N + k
        · simp only [hi, ite_true]; exact hev u v i hi
        · simp only [hi, ite_false, evalRail]
          have hcw_len : ((C.gates.take k).foldl wstep (oneEach u v)).length = N + k := by
            rw [foldl_wstep_len, oneEach_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
          have hcw0 : ((C.gates.take k).foldl wstep (oneEach u v)).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
          rw [hcw0]
          exact ⟨rfl, rfl⟩
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [g] := List.take_succ_eq_append_getElem hk
      -- Helper to package step result once we have gs', pNew, nNew
      have hfinish : ∀ (gs' : List Gate) (pNew nNew : Rail),
          Monotone2 ⟨gs0 ++ gs', 0⟩ →
          gs.length ≤ gs'.length → gs'.length ≤ gs.length + 2 →
          (pNew = .tt → gs'.length ≤ gs.length + 1) →
          railBound (N + gs0.length + gs'.length) pNew →
          railBound (N + gs0.length + gs'.length) nNew →
          (∀ (u : Fin n) (v : Fin m),
            (∀ idx < N + gs0.length + gs.length,
              (Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)).getD idx false =
              (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false) ∧
            let cw_pre := (C.gates.take k).foldl wstep (oneEach u v)
            let val := g.op.eval (g.inputs.map fun i => cw_pre.getD i false)
            let dw' := Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)
            evalRail dw' pNew = val ∧ evalRail dw' nNew = !val) →
          ∃ (gs'' : List Gate) (pM' nM' : ℕ → Rail),
            Monotone2 ⟨gs0 ++ gs'', 0⟩ ∧
            gs''.length ≤ 2 * (k + 1) ∧
            ((∃ w < N + (k + 1), pM' w = .tt) → gs''.length + 1 ≤ 2 * (k + 1)) ∧
            (∀ w < N + (k + 1), railBound (N + gs0.length + gs''.length) (pM' w) ∧
                                railBound (N + gs0.length + gs''.length) (nM' w)) ∧
            (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + (k + 1) →
              let cw := ((C.gates.take (k + 1)).foldl wstep (oneEach u v)).getD w false
              let dw := Circuit.wires ⟨gs0 ++ gs'', 0⟩ (oneEach u v)
              evalRail dw (pM' w) = cw ∧ evalRail dw (nM' w) = !cw) := by
        intro gs' pNew nNew hM' hge hle htt_new hbp hbn hev_new
        let pM' : ℕ → Rail := fun w => if w = N + k then pNew else pM w
        let nM' : ℕ → Rail := fun w => if w = N + k then nNew else nM w
        refine ⟨gs', pM', nM', hM', by omega, ?_, ?_, ?_⟩
        · rintro ⟨w, hw, httw⟩
          dsimp only [pM'] at httw
          by_cases heq : w = N + k
          · simp only [heq, ite_true] at httw
            have := htt_new httw; omega
          · simp only [heq, ite_false] at httw
            have := htt_ih ⟨w, by omega, httw⟩; omega
        · intro w hw
          dsimp only [pM', nM']
          by_cases heq : w = N + k
          · simp only [heq, ite_true]; exact ⟨hbp, hbn⟩
          · simp only [heq, ite_false]
            have hb := hbd w (by omega)
            exact ⟨railBound_mono (by omega) hb.1, railBound_mono (by omega) hb.2⟩
        · intro u v w hw
          obtain ⟨hkeep, hpv, hnv⟩ := hev_new u v
          set cw_pre := (C.gates.take k).foldl wstep (oneEach u v)
          have hpre_len : cw_pre.length = N + k := by
            simp only [cw_pre, foldl_wstep_len, oneEach_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), N]
          have hcw_next : (C.gates.take (k + 1)).foldl wstep (oneEach u v) =
              cw_pre ++ [g.op.eval (g.inputs.map fun i => cw_pre.getD i false)] := by
            rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
          dsimp only [pM', nM']
          by_cases heq : w = N + k
          · subst heq
            simp only [ite_true]
            rw [hcw_next, ← hpre_len, List.getD_append_right _ _ _ _ le_rfl]
            simp only [Nat.sub_self, List.getD_cons_zero]
            exact ⟨hpv, hnv⟩
          · simp only [heq, ite_false]
            rw [hcw_next, List.getD_append _ _ _ _ (by omega)]
            have hb := hbd w (by omega)
            have hevw := hev u v w (by omega)
            rw [evalRail_congr hkeep hb.1, evalRail_congr hkeep hb.2]
            exact hevw
      -- Case split on g.op and g.inputs (length ≤ 2)
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · -- inputs = []
        rcases hgop with hop | hop | hop
        · exact hfinish gs .tt .ff hM le_rfl (by omega) (fun _ => by omega) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
        · exact hfinish gs .ff .tt hM le_rfl (by omega) (fun h => by cases h) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
        · exact hfinish gs .tt .ff hM le_rfl (by omega) (fun _ => by omega) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
      · -- inputs = [a]
        rcases hgop with hop | hop | hop
        · exact hfinish gs (getP a) (getN a) hM le_rfl (by omega) (fun _ => by omega)
            (hget_bd a).1 (hget_bd a).2
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              simp [hop, hgi, GateOp.eval, h.1, h.2]⟩)
        · exact hfinish gs (getP a) (getN a) hM le_rfl (by omega) (fun _ => by omega)
            (hget_bd a).1 (hget_bd a).2
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              simp [hop, hgi, GateOp.eval, h.1, h.2]⟩)
        · exact hfinish gs (getN a) (getP a) hM le_rfl (by omega) (fun _ => by omega)
            (hget_bd a).2 (hget_bd a).1
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              simp [hop, hgi, GateOp.eval, h.1, h.2]⟩)
      · -- inputs = [a, b]
        rcases hgop with hop | hop | hop
        · -- AND [a, b]
          set res1 := railAnd (N + gs0.length) gs (getP a) (getP b)
          obtain ⟨hM1, hge1, hle1, htt1, hbd1, hev1⟩ := railAnd_spec N gs0 gs hM (getP a) (getP b) (hget_bd a).1 (hget_bd b).1
          change Monotone2 ⟨gs0 ++ res1.1, 0⟩ at hM1
          change gs.length ≤ res1.1.length at hge1
          change res1.1.length ≤ gs.length + 1 at hle1
          change res1.2 = .tt → res1.1.length = gs.length at htt1
          change railBound (N + gs0.length + res1.1.length) res1.2 at hbd1
          set res2 := railOr (N + gs0.length) res1.1 (getN a) (getN b)
          obtain ⟨hM2, hge2, hle2, htt2, hbd2, hev2⟩ := railOr_spec N gs0 res1.1 hM1 (getN a) (getN b)
            (railBound_mono (by omega) (hget_bd a).2) (railBound_mono (by omega) (hget_bd b).2)
          change Monotone2 ⟨gs0 ++ res2.1, 0⟩ at hM2
          change res1.1.length ≤ res2.1.length at hge2
          change res2.1.length ≤ res1.1.length + 1 at hle2
          change railBound (N + gs0.length + res2.1.length) res2.2 at hbd2
          refine hfinish res2.1 res1.2 res2.2 hM2 (by omega) (by omega) ?_
            (railBound_mono (by omega) hbd1) hbd2 ?_
          · intro htt; have := htt1 htt; omega
          · intro u v
            have h1 := hev1 (oneEach u v) (oneEach_len u v)
            have h2 := hev2 (oneEach u v) (oneEach_len u v)
            have hkeep : ∀ idx < N + gs0.length + gs.length,
                (Circuit.wires ⟨gs0 ++ res2.1, 0⟩ (oneEach u v)).getD idx false =
                (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false := by
              intro idx hidx
              rw [h2.1 idx (by omega), h1.1 idx hidx]
            refine ⟨hkeep, ?_, ?_⟩
            · rw [evalRail_congr h2.1 hbd1, h1.2]
              have ha := hget_ev u v a; have hb := hget_ev u v b
              simp [hop, hgi, GateOp.eval, ha.1, hb.1]
            · rw [h2.2]
              rw [evalRail_congr h1.1 (hget_bd a).2, evalRail_congr h1.1 (hget_bd b).2]
              have ha := hget_ev u v a; have hb := hget_ev u v b
              simp [hop, hgi, GateOp.eval, ha.2, hb.2, Bool.not_and]
        · -- OR [a, b]
          set res1 := railOr (N + gs0.length) gs (getP a) (getP b)
          obtain ⟨hM1, hge1, hle1, htt1, hbd1, hev1⟩ := railOr_spec N gs0 gs hM (getP a) (getP b) (hget_bd a).1 (hget_bd b).1
          change Monotone2 ⟨gs0 ++ res1.1, 0⟩ at hM1
          change gs.length ≤ res1.1.length at hge1
          change res1.1.length ≤ gs.length + 1 at hle1
          change res1.2 = .tt → res1.1.length = gs.length at htt1
          change railBound (N + gs0.length + res1.1.length) res1.2 at hbd1
          set res2 := railAnd (N + gs0.length) res1.1 (getN a) (getN b)
          obtain ⟨hM2, hge2, hle2, htt2, hbd2, hev2⟩ := railAnd_spec N gs0 res1.1 hM1 (getN a) (getN b)
            (railBound_mono (by omega) (hget_bd a).2) (railBound_mono (by omega) (hget_bd b).2)
          change Monotone2 ⟨gs0 ++ res2.1, 0⟩ at hM2
          change res1.1.length ≤ res2.1.length at hge2
          change res2.1.length ≤ res1.1.length + 1 at hle2
          change railBound (N + gs0.length + res2.1.length) res2.2 at hbd2
          refine hfinish res2.1 res1.2 res2.2 hM2 (by omega) (by omega) ?_
            (railBound_mono (by omega) hbd1) hbd2 ?_
          · intro htt; have := htt1 htt; omega
          · intro u v
            have h1 := hev1 (oneEach u v) (oneEach_len u v)
            have h2 := hev2 (oneEach u v) (oneEach_len u v)
            have hkeep : ∀ idx < N + gs0.length + gs.length,
                (Circuit.wires ⟨gs0 ++ res2.1, 0⟩ (oneEach u v)).getD idx false =
                (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false := by
              intro idx hidx
              rw [h2.1 idx (by omega), h1.1 idx hidx]
            refine ⟨hkeep, ?_, ?_⟩
            · rw [evalRail_congr h2.1 hbd1, h1.2]
              have ha := hget_ev u v a; have hb := hget_ev u v b
              simp [hop, hgi, GateOp.eval, ha.1, hb.1]
            · rw [h2.2]
              rw [evalRail_congr h1.1 (hget_bd a).2, evalRail_congr h1.1 (hget_bd b).2]
              have ha := hget_ev u v a; have hb := hget_ev u v b
              simp [hop, hgi, GateOp.eval, ha.2, hb.2, Bool.not_or]
        · -- NOT [a, b] reads headD = a
          exact hfinish gs (getN a) (getP a) hM le_rfl (by omega) (fun _ => by omega)
            (hget_bd a).2 (hget_bd a).1
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              simp [hop, hgi, GateOp.eval, h.1, h.2]⟩)
      · simp [hgi] at hglen
  obtain ⟨gs, pM, nM, hM, hlen, htt, hbd, hev⟩ := hSim C.gates.length le_rfl
  by_cases hout : C.output < N + C.gates.length
  · cases hpo : pM C.output with
    | ff =>
      refine ⟨⟨gs0 ++ gs, N + (gs0 ++ gs).length⟩, hM, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        have : C.gates.length ≤ s := hsz
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        unfold Circuit.eval
        change (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false =
               (C.gates.foldl wstep (oneEach u v)).getD C.output false
        rw [← h1]
        simp only [evalRail]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · unfold Circuit.wires
          change ((gs0 ++ gs).foldl wstep (oneEach u v)).length ≤ _
          rw [foldl_wstep_len, oneEach_len]
    | tt =>
      have hlen_tt : gs.length + 1 ≤ 2 * C.gates.length := htt ⟨C.output, hout, hpo⟩
      let gT : Gate := ⟨.and, []⟩
      let gsF : List Gate := (gs0 ++ gs) ++ [gT]
      refine ⟨⟨gsF, N + (gs0 ++ gs).length⟩, ?_, ?_, ?_⟩
      · intro g hg
        change g ∈ (gs0 ++ gs) ++ [gT] at hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hM g hg
        · exact ⟨Or.inl rfl, by decide⟩
      · simp only [Circuit.size, gsF, List.length_append, List.length_singleton]
        have : C.gates.length ≤ s := hsz
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        unfold Circuit.eval
        change (Circuit.wires ⟨gsF, 0⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false =
               (C.gates.foldl wstep (oneEach u v)).getD C.output false
        rw [← h1]
        simp only [evalRail]
        unfold Circuit.wires
        change (((gs0 ++ gs) ++ [gT]).foldl wstep (oneEach u v)).getD (N + (gs0 ++ gs).length) false = true
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set w := (gs0 ++ gs).foldl wstep (oneEach u v)
        have hwlen : w.length = N + (gs0 ++ gs).length := by
          simp only [w, foldl_wstep_len, oneEach_len, N]
        dsimp only [wstep]
        rw [← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp [gT, GateOp.eval]
    | wire p =>
      refine ⟨⟨gs0 ++ gs, p⟩, hM, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        have : C.gates.length ≤ s := hsz
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        exact h1
  · refine ⟨⟨gs0 ++ gs, N + (gs0 ++ gs).length⟩, hM, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append]
      have : C.gates.length ≤ s := hsz
      omega
    · intro u v
      have hrep := hRep u v
      rw [← hrep]
      unfold Circuit.eval
      have h1 : (Circuit.wires ⟨gs0 ++ gs, N + (gs0 ++ gs).length⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · unfold Circuit.wires
          change ((gs0 ++ gs).foldl wstep (oneEach u v)).length ≤ _
          rw [foldl_wstep_len, oneEach_len]
      have h2 : (C.wires (oneEach u v)).getD C.output false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · unfold Circuit.wires
          change (C.gates.foldl wstep (oneEach u v)).length ≤ _
          rw [foldl_wstep_len, oneEach_len]
          omega
      rw [h1, h2]


private def rl (N N' : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ := if i < N then σ i else i - N + N'

private def rlG (N N' : ℕ) (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rl N N' σ)⟩

private lemma getD_ge' (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma relabel (N N' : ℕ) (σ : ℕ → ℕ) (good : ℕ → Prop) (hσ : ∀ i < N, good i → σ i < N') :
    ∀ (gs : List Gate), (∀ g ∈ gs, ∀ a ∈ g.inputs, a < N → good a) →
    ∀ (j : ℕ) (x y : List Bool), x.length = N + j → y.length = N' + j →
    (∀ i, (N ≤ i ∨ good i) → y.getD (rl N N' σ i) false = x.getD i false) →
    ∀ i, (N ≤ i ∨ good i) →
      ((gs.map (rlG N N' σ)).foldl wstep y).getD (rl N N' σ i) false =
        (gs.foldl wstep x).getD i false := by
  intro gs
  induction gs with
  | nil => intro _ j x y _ _ h; exact h
  | cons g gs ih =>
    intro hgs j x y hx hy hinv
    refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (j + 1) (wstep x g)
      (wstep y (rlG N N' σ g)) (by simp [wstep, hx]; omega) (by simp [wstep, hy]; omega) ?_
    intro i hi
    have hmap : (g.inputs.map (rl N N' σ)).map (fun a => y.getD a false) =
        g.inputs.map (fun a => x.getD a false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      by_cases h : a < N
      · exact hinv a (Or.inr (hgs g (by simp) a ha h))
      · exact hinv a (Or.inl (by omega))
    rcases lt_trichotomy i (N + j) with h | h | h
    · have hr : rl N N' σ i < N' + j := by
        unfold rl; split_ifs with h1
        · have := hσ i h1 (hi.resolve_left (by omega)); omega
        · omega
      simp only [wstep]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hinv i hi
    · have hr : rl N N' σ i = N' + j := by unfold rl; rw [if_neg (by omega)]; omega
      simp only [wstep, rlG]
      rw [hr, ← hy, List.getD_append_right _ _ _ _ le_rfl, h, ← hx,
        List.getD_append_right _ _ _ _ le_rfl, hmap]
      simp
    · have hr : rl N N' σ i = i - N + N' := by unfold rl; rw [if_neg (by omega)]
      rw [hr, getD_ge' _ _ (by simp [wstep]; omega), getD_ge' _ _ (by simp [wstep]; omega)]

private def orChain (B : ℕ) : List ℕ → List Gate
  | [] => [⟨.or, []⟩]
  | r :: rs => orChain B rs ++ [⟨.or, [B + rs.length, r]⟩]

private lemma orChain_len (B : ℕ) (l : List ℕ) : (orChain B l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons r rs ih => simp [orChain, ih]

private lemma orChain_mono (B : ℕ) (l : List ℕ) :
    ∀ g ∈ orChain B l, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction l with
  | nil => intro g hg; simp only [orChain, List.mem_singleton] at hg; subst hg; simp
  | cons r rs ih =>
    intro g hg
    simp only [orChain, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · simp

private lemma orChain_val (B : ℕ) (w : List Bool) (hw : w.length = B) : ∀ l : List ℕ,
    (∀ r ∈ l, r < B) →
    ((orChain B l).foldl wstep w).getD (B + l.length) false = l.any (fun r => w.getD r false) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [orChain, List.foldl_cons, List.foldl_nil, wstep, List.length_nil, Nat.add_zero]
    rw [← hw, List.getD_append_right _ _ _ _ le_rfl]
    simp [GateOp.eval]
  | cons r rs ih =>
    intro hl
    simp only [orChain, List.foldl_append, List.foldl_cons, List.foldl_nil, wstep]
    have hlen : ((orChain B rs).foldl wstep w).length = B + rs.length + 1 := by
      rw [foldl_wstep_len, orChain_len, hw]; omega
    rw [List.length_cons, show B + (rs.length + 1) = ((orChain B rs).foldl wstep w).length by omega,
      List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil, or_eval_two]
    rw [ih (fun r' h => hl r' (by simp [h])),
      foldl_wstep_getD_lt _ _ _ (by rw [hw]; exact hl r (by simp))]
    simp [Bool.or_comm]

private lemma pos_iff (L : List ℕ) (hL : L.Nodup) (p t : ℕ) (hp : p < L.length) :
    L.getD p 0 = t ↔ p = L.idxOf t := by
  rw [List.getD_eq_getElem _ _ hp]
  constructor
  · rintro rfl; exact (hL.idxOf_getElem p hp).symm
  · rintro rfl; exact List.getElem_idxOf hp

private lemma any_rest (S L : List ℕ) (f : ℕ → Bool) (t : ℕ) (hf : ∀ c ∈ S, f c = decide (c = t))
    (ht : t ∈ S) : (S.filter (fun c => decide (c ∉ L))).any f = decide (t ∉ L) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, ⟨hcS, hcL⟩, hfc⟩
    rw [hf c hcS, decide_eq_true_eq] at hfc
    exact hfc ▸ hcL
  · intro h
    exact ⟨t, ⟨ht, h⟩, by rw [hf t ht]; simp⟩

private lemma filter_two (p q : ℕ → Bool) (hpq : ∀ x, p x = true → q x = false) :
    ∀ I : List ℕ, (I.filter p).length + (I.filter q).length ≤ I.length := by
  intro I
  induction I with
  | nil => simp
  | cons a I ih =>
    have := hpq a
    simp only [List.filter_cons, List.length_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

private lemma flat_len (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h g (by simp)
    have := ih (fun g' hg' => h g' (by simp [hg']))
    omega

theorem main19164 (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hF : FanInTwo C) (hsz : C.size ≤ s) (hRep : Represents A C) :
    RepSizeAtMost A (n + m + 2 * (s + 1) ^ 2) := by
  by_cases hout : C.output < n + m
  · refine ⟨⟨[], C.output⟩, fun _ h => by simp at h, by simp [Circuit.size], ?_⟩
    intro u v
    rw [← hRep u v]
    change (oneEach u v).getD C.output false = (C.gates.foldl wstep (oneEach u v)).getD C.output false
    rw [foldl_wstep_getD_lt _ _ _ (by rw [oneEach_len]; exact hout)]
  set I := C.gates.flatMap Gate.inputs with hI
  set Lr := (I.filter (fun i => decide (i < n))).dedup with hLr
  set Lc := (I.filter (fun i => decide (n ≤ i ∧ i < n + m))).dedup with hLc
  set k := Lr.length with hk
  set l := Lc.length with hl
  have hkl : k + l ≤ 2 * s := by
    have h1 : k ≤ (I.filter (fun i => decide (i < n))).length := (List.dedup_sublist _).length_le
    have h2 : l ≤ (I.filter (fun i => decide (n ≤ i ∧ i < n + m))).length :=
      (List.dedup_sublist _).length_le
    have h3 := filter_two (fun i => decide (i < n)) (fun i => decide (n ≤ i ∧ i < n + m))
      (fun x hx => by simp at hx ⊢; omega) I
    have h4 : I.length ≤ 2 * C.gates.length := flat_len C.gates (fun g hg => (hF g hg).2)
    have h5 : C.gates.length ≤ s := hsz
    omega
  have hLrN : Lr.Nodup := List.nodup_dedup _
  have hLcN : Lc.Nodup := List.nodup_dedup _
  have hLrM : ∀ i, i ∈ Lr ↔ i ∈ I ∧ i < n := by
    intro i; rw [hLr, List.mem_dedup, List.mem_filter]; simp
  have hLcM : ∀ i, i ∈ Lc ↔ i ∈ I ∧ n ≤ i ∧ i < n + m := by
    intro i; rw [hLc, List.mem_dedup, List.mem_filter]; simp
  -- the reduced circuit
  let N' := k + 1 + (l + 1)
  let σ1 : ℕ → ℕ := fun i => if i < n then Lr.idxOf i else k + 1 + Lc.idxOf i
  let C' : Circuit := ⟨C.gates.map (rlG (n + m) N' σ1), rl (n + m) N' σ1 C.output⟩
  let A' : Fin (k + 1) → Fin (l + 1) → Bool := fun p q => C'.eval (oneEach p q)
  have hF' : FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    simpa [rlG] using hF g0 hg0
  obtain ⟨D', hDM, hDs, hDrep⟩ := rep18925 (k + 1) (l + 1) s A' C' hF'
    (by simpa [Circuit.size, C'] using hsz) (fun _ _ => rfl)
  -- the prepared signals
  let B := n + m
  let RestR := (List.range n).filter (fun r => decide (r ∉ Lr))
  let RestC := ((List.range m).map (n + ·)).filter (fun c => decide (c ∉ Lc))
  let zr := B + RestR.length
  let B2 := zr + 1
  let zc := B2 + RestC.length
  let N'' := zc + 1
  let P := orChain B RestR ++ orChain B2 RestC
  let σ2 : ℕ → ℕ := fun p => if p < k then Lr.getD p 0 else if p = k then zr
    else if p - (k + 1) < l then Lc.getD (p - (k + 1)) 0 else zc
  refine ⟨⟨P ++ D'.gates.map (rlG N' N'' σ2), rl N' N'' σ2 D'.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, P] at hg
    rcases hg with (hg | hg) | hg
    · exact orChain_mono _ _ g hg
    · exact orChain_mono _ _ g hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      simpa [rlG] using hDM g0 hg0
  · have hRR : RestR.length ≤ n := (List.length_filter_le _ _).trans (by simp)
    have hRC : RestC.length ≤ m := (List.length_filter_le _ _).trans (by simp)
    have hD : D'.gates.length ≤ 2 * s + ((3 * (k + 1) - 6) + (3 * (l + 1) - 6)) := hDs
    have hsq : 8 * s ≤ 2 * (s + 1) ^ 2 + 1 := by
      have : (8 * s : ℤ) ≤ 2 * ((s : ℤ) + 1) ^ 2 + 1 := by nlinarith [sq_nonneg ((s : ℤ) - 1)]
      exact_mod_cast this
    have hsq2 : s + 1 ≤ (s + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    simp only [Circuit.size, List.length_append, List.length_map, P, orChain_len]
    omega
  · intro u v
    have hφ : Lr.idxOf u.val < k + 1 := Nat.lt_succ_of_le List.idxOf_le_length
    have hψ : Lc.idxOf (n + v.val) < l + 1 := Nat.lt_succ_of_le List.idxOf_le_length
    set x := oneEach u v with hx
    set x' := oneEach (⟨_, hφ⟩ : Fin (k + 1)) (⟨_, hψ⟩ : Fin (l + 1)) with hx'
    have hxl : x.length = n + m := oneEach_len u v
    have hx'l : x'.length = N' := oneEach_len _ _
    have hxL : ∀ r (hr : r < n), x.getD r false = decide (r = u.val) := by
      intro r hr
      have := oneEach_getD_left u v ⟨r, hr⟩
      simp only at this; rw [this]; simp [Fin.ext_iff]
    have hxR : ∀ c, n ≤ c → c < n + m → x.getD c false = decide (c = n + v.val) := by
      intro c h1 h2
      have := oneEach_getD_right u v ⟨c - n, by omega⟩
      simp only at this
      rw [show c = n + (c - n) by omega, this]; simp [Fin.ext_iff]
    have hx'L : ∀ p (hp : p < k + 1), x'.getD p false = decide (p = Lr.idxOf u.val) := by
      intro p hp
      have := oneEach_getD_left (⟨_, hφ⟩ : Fin (k + 1)) (⟨_, hψ⟩ : Fin (l + 1)) ⟨p, hp⟩
      simp only at this; rw [hx', this]; simp [Fin.ext_iff]
    have hx'R : ∀ q (hq : q < l + 1), x'.getD (k + 1 + q) false = decide (q = Lc.idxOf (n + v.val)) := by
      intro q hq
      have := oneEach_getD_right (⟨_, hφ⟩ : Fin (k + 1)) (⟨_, hψ⟩ : Fin (l + 1)) ⟨q, hq⟩
      simp only at this; rw [hx', this]; simp [Fin.ext_iff]
    -- step 3: C' at x' is C at x
    have hstep3 : C'.eval x' = C.eval x := by
      have := relabel (n + m) N' σ1 (fun i => i ∈ I)
        (fun i _ _ => by
          dsimp only [σ1]
          have := @List.idxOf_le_length _ _ _ Lr i
          have := @List.idxOf_le_length _ _ _ Lc i
          split_ifs <;> omega)
        C.gates (fun g hg a ha _ => List.mem_flatMap.2 ⟨g, hg, ha⟩) 0 x x' hxl hx'l ?_
        C.output (Or.inl (by omega))
      · exact this
      · intro i hi
        by_cases hiN : n + m ≤ i
        · unfold rl; rw [if_neg (by omega), getD_ge' _ _ (by omega), getD_ge' _ _ (by omega)]
        · have hiI : i ∈ I := hi.resolve_left hiN
          unfold rl; rw [if_pos (by omega)]
          dsimp only [σ1]
          split_ifs with hin
          · have hmem : i ∈ Lr := (hLrM i).2 ⟨hiI, hin⟩
            rw [hx'L _ (Nat.lt_succ_of_le List.idxOf_le_length), hxL i hin]
            exact decide_eq_decide.2 (List.idxOf_inj hmem)
          · have hmem : i ∈ Lc := (hLcM i).2 ⟨hiI, by omega, by omega⟩
            rw [hx'R _ (Nat.lt_succ_of_le List.idxOf_le_length), hxR i (by omega) (by omega)]
            exact decide_eq_decide.2 (List.idxOf_inj hmem)
    -- prepared wires
    set y := P.foldl wstep x with hy
    have hyl : y.length = N'' := by
      rw [hy, foldl_wstep_len, hxl]; simp only [P, List.length_append, orChain_len]; omega
    have hw1l : ((orChain B RestR).foldl wstep x).length = B2 := by
      rw [foldl_wstep_len, hxl, orChain_len]; omega
    have hysplit : y = (orChain B2 RestC).foldl wstep ((orChain B RestR).foldl wstep x) := by
      rw [hy]; simp only [P, List.foldl_append]
    have hyin : ∀ c < n + m, y.getD c false = x.getD c false := fun c hc =>
      foldl_wstep_getD_lt _ _ _ (by omega)
    have hw1in : ∀ c < n + m, ((orChain B RestR).foldl wstep x).getD c false = x.getD c false :=
      fun c hc => foldl_wstep_getD_lt _ _ _ (by omega)
    have hprep : ∀ p, (N' ≤ p ∨ True) → y.getD (rl N' N'' σ2 p) false = x'.getD p false := by
      intro p _
      by_cases hpN : N' ≤ p
      · unfold rl; rw [if_neg (by omega), getD_ge' _ _ (by omega), getD_ge' _ _ (by omega)]
      unfold rl; rw [if_pos (by omega)]
      dsimp only [σ2]
      split_ifs with h1 h2 h3
      · -- a read row
        have hmem : Lr.getD p 0 ∈ Lr := by
          rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1
        have hrn := ((hLrM _).1 hmem).2
        rw [hyin _ (by omega), hxL _ hrn, hx'L p (by omega)]
        exact decide_eq_decide.2 (pos_iff Lr hLrN p u.val h1)
      · -- the row of unread rows
        subst h2
        rw [hysplit, foldl_wstep_getD_lt _ _ _ (by omega), orChain_val B x hxl RestR
          (fun r hr => by simp [RestR] at hr; omega), hx'L _ (by omega)]
        rw [any_rest _ _ _ u.val (fun c hc => hxL c (by simpa using hc)) (by simp)]
        apply decide_eq_decide.2
        rw [eq_comm, List.idxOf_eq_length_iff]
      · -- a read column
        have hmem : Lc.getD (p - (k + 1)) 0 ∈ Lc := by
          rw [List.getD_eq_getElem _ _ h3]; exact List.getElem_mem h3
        have hcn := ((hLcM _).1 hmem).2
        rw [hyin _ (by omega), hxR _ hcn.1 hcn.2,
          show x'.getD p false = x'.getD (k + 1 + (p - (k + 1))) false by
            rw [Nat.add_sub_cancel' (by omega)], hx'R _ (by omega)]
        exact decide_eq_decide.2 (pos_iff Lc hLcN _ _ h3)
      · -- the column of unread columns
        have hpl : p - (k + 1) = l := by omega
        rw [hysplit, orChain_val B2 _ hw1l RestC
          (fun c hc => by simp [RestC] at hc; omega), show p = k + 1 + l by omega, hx'R _ (by omega)]
        rw [any_rest _ _ _ (n + v.val) (fun c hc => by
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨a, ha, rfl⟩ := hc
          rw [hw1in _ (by omega), hxR _ (by omega) (by omega)]) (by simp)]
        apply decide_eq_decide.2
        rw [eq_comm, List.idxOf_eq_length_iff]
    have hstep1 := relabel N' N'' σ2 (fun _ => True)
      (fun i hi _ => by
        dsimp only [σ2]
        split_ifs with h1 h2 h3
        · have hmem : Lr.getD i 0 ∈ Lr := by
            rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1
          have := ((hLrM _).1 hmem).2; omega
        · omega
        · have hmem : Lc.getD (i - (k + 1)) 0 ∈ Lc := by
            rw [List.getD_eq_getElem _ _ h3]; exact List.getElem_mem h3
          have := ((hLcM _).1 hmem).2; omega
        · omega)
      D'.gates (fun _ _ _ _ _ => trivial) 0 x' y hx'l hyl hprep D'.output (Or.inr trivial)
    rw [← hRep u v, ← hstep3]
    change ((P ++ D'.gates.map (rlG N' N'' σ2)).foldl wstep x).getD (rl N' N'' σ2 D'.output) false = _
    rw [List.foldl_append, ← hy, hstep1]
    exact hDrep _ _


theorem main_aux : ∀ (n m s c : ℕ) (A : Fin n → Fin m → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A c → n + m + 2 * (s + 1) ^ 2 ≤ c →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → ¬ PEqualNP.Represents.Represents A C := by
  intro n m s c A hA hc C hF hs hR
  obtain ⟨D, hD1, hD2, hD3⟩ := main19164 n m s A C hF hs hR
  exact hA ⟨D, hD1, le_trans hD2 hc, hD3⟩

end PEqualNP.Outside.L_meta_19302

theorem PEqualNP.Outside.L_meta_19302 : ∀ (n m s c : ℕ) (A : Fin n → Fin m → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A c → n + m + 2 * (s + 1) ^ 2 ≤ c →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → ¬ PEqualNP.Represents.Represents A C :=
  PEqualNP.Outside.L_meta_19302.main_aux
