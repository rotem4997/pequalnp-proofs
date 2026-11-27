import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19172_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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
         · trivial
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
         · trivial
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

private lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

private lemma cones_char (n : ℕ) (gs : List Gate) :
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

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
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

private lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

private lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

open Classical in
private lemma railAndC_spec (c : Prop) (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (r1 r2 : Rail) (hb1 : railBound (N + gs0.length + gs.length) r1) (hb2 : railBound (N + gs0.length + gs.length) r2) :
    ∃ res : List Gate × Rail,
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧
    gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + (if c then 1 else 0) ∧
    railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false = (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      (c → evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        (evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r1 && evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r2))) := by
  by_cases hc : c
  · obtain ⟨hM1, hge1, hle1, _, hbd1, hev1⟩ := railAnd_spec N gs0 gs hM r1 r2 hb1 hb2
    refine ⟨railAnd (N + gs0.length) gs r1 r2, hM1, hge1, by simpa [hc] using hle1, hbd1, ?_⟩
    intro inp hinp
    exact ⟨(hev1 inp hinp).1, fun _ => (hev1 inp hinp).2⟩
  · refine ⟨(gs, .ff), hM, le_rfl, by simp, trivial, ?_⟩
    intro inp _
    exact ⟨fun _ _ => rfl, fun h => absurd h hc⟩

open Classical in
private lemma railOrC_spec (c : Prop) (N : ℕ) (gs0 gs : List Gate) (hM : Monotone2 ⟨gs0 ++ gs, 0⟩)
    (r1 r2 : Rail) (hb1 : railBound (N + gs0.length + gs.length) r1) (hb2 : railBound (N + gs0.length + gs.length) r2) :
    ∃ res : List Gate × Rail,
    Monotone2 ⟨gs0 ++ res.1, 0⟩ ∧
    gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + (if c then 1 else 0) ∧
    railBound (N + gs0.length + res.1.length) res.2 ∧
    (∀ inp : List Bool, inp.length = N →
      (∀ u < N + gs0.length + gs.length,
        (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp).getD u false = (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD u false) ∧
      (c → evalRail (Circuit.wires ⟨gs0 ++ res.1, 0⟩ inp) res.2 =
        (evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r1 || evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) r2))) := by
  by_cases hc : c
  · obtain ⟨hM1, hge1, hle1, _, hbd1, hev1⟩ := railOr_spec N gs0 gs hM r1 r2 hb1 hb2
    refine ⟨railOr (N + gs0.length) gs r1 r2, hM1, hge1, by simpa [hc] using hle1, hbd1, ?_⟩
    intro inp hinp
    exact ⟨(hev1 inp hinp).1, fun _ => (hev1 inp hinp).2⟩
  · refine ⟨(gs, .ff), hM, le_rfl, by simp, trivial, ?_⟩
    intro inp _
    exact ⟨fun _ _ => rfl, fun h => absurd h hc⟩

open Classical in
private noncomputable def cost (n m : ℕ) (C : Circuit) (p h : ℕ) (k : ℕ) : ℕ :=
  if k = p then 0 else (if (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) then 1 else 0) + (if (k = h ∨ InCone (n + m) C k h) then 1 else 0)

private noncomputable def cnt (n m : ℕ) (C : Circuit) (p h : ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, cost n m C p h i

private lemma cnt_bound (n m : ℕ) (C : Circuit) (p h : ℕ) (hp : p < C.gates.length) :
    cnt n m C p h C.gates.length + 1 ≤ C.gates.length +
      ((Finset.range C.gates.length).filter (fun i => (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) ∧ (i = r ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs))).card := by
  classical
  have key : ∀ i ∈ Finset.range C.gates.length,
      cost n m C p h i + (if i = p then 1 else 0) ≤ 1 + (if ((i = h ∨ InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (i = r ∨ InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs)) then 1 else 0) := by
    intro i _
    unfold cost
    by_cases h1 : i = p
    · simp [h1]
    · by_cases h2 : (i = h ∨ InCone (n + m) C i h)
      · simp [h1, h2]
      · simp [h1, h2]
  have hsum := Finset.sum_le_sum key
  have hK : ((Finset.range C.gates.length).filter (fun i => (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) ∧ (i = r ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs))).card =
      ∑ i ∈ Finset.range C.gates.length, (if ((i = h ∨ InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (i = r ∨ InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs)) then 1 else 0) := by
    rw [Finset.card_filter]
  have hone : ∑ _i ∈ Finset.range C.gates.length, 1 = C.gates.length := by simp
  have ha : ∑ i ∈ Finset.range C.gates.length, (if i = p then 1 else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.range C.gates.length) p (fun _ => 1)]
    simp [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ha, hone, ← hK] at hsum
  unfold cnt
  omega

theorem main (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (p h : ℕ)
    (hF : FanInTwo C) (hsz : C.size ≤ s) (hRep : Represents A C)
    (hp : p < C.gates.length)
    (hpn : (gateAt C p).op = GateOp.not)
    (hph : (gateAt C p).inputs.head? = some (n + m + h))
    (hhp : h < p)
    (hnots : ∀ j < C.gates.length, (gateAt C j).op = GateOp.not → j = p) :
    RepSizeAtMost A (s - 1 + ((Finset.range C.gates.length).filter (fun i => (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) ∧ (i = r ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs))).card +
      ((3 * n - 6) + (3 * m - 6))) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun u => Fin.elim0 u⟩
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun _ v => Fin.elim0 v⟩
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨gL, hML, hlenL, rL, hbdL, hntL, hevL⟩ :=
    build_slice_loo (n + m) 0 n hn1 (by omega) [] (fun _ h => by simp at h)
  obtain ⟨gR, hMR, hlenR, rR, hbdR, hntR, hevR⟩ :=
    build_slice_loo (n + m) n m hm1 (by omega) ([] ++ gL) hML
  let gs0 : List Gate := ([] ++ gL) ++ gR
  have hM0 : Monotone2 ⟨gs0, 0⟩ := hMR
  have hlen0 : gs0.length ≤ (3 * n - 6) + (3 * m - 6) := by
    simp only [gs0, List.nil_append, List.length_append]; omega

  let pos0 : ℕ → Rail := fun w => if w < (n + m) then .wire w else .ff
  let neg0 : ℕ → Rail := fun w =>
    if h1 : w < n then rL ⟨w, h1⟩
    else if h2 : w - n < m then rR ⟨w - n, h2⟩
    else .tt
  have hSim : ∀ k ≤ C.gates.length,
      ∃ (gs : List Gate) (pM nM : ℕ → Rail),
        Monotone2 ⟨gs0 ++ gs, 0⟩ ∧
        gs.length ≤ cnt n m C p h k ∧
        (∀ w < (n + m) + k, railBound ((n + m) + gs0.length + gs.length) (pM w) ∧
                      railBound ((n + m) + gs0.length + gs.length) (nM w)) ∧
        (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < (n + m) + k →
          let cw := ((C.gates.take k).foldl wstep (oneEach u v)).getD w false
          let dw := Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)
          ((w < n + m ∨ w - (n + m) = p ∨ ¬ ((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h) ∨ (((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((w - (n + m)) = r ∨ InCone (n + m) C (w - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → evalRail dw (pM w) = cw) ∧
          ((w < n + m ∨ ((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h)) → evalRail dw (nM w) = !cw)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], pos0, neg0, by simpa using hM0, by simp [cnt], ?_, ?_⟩
      · intro w hw
        constructor
        · dsimp only [pos0]
          by_cases hwn : w < (n + m)
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
        have hboth : (let cw := ((C.gates.take 0).foldl wstep (oneEach u v)).getD w false
            let dw := Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v)
            evalRail dw (pos0 w) = cw ∧ evalRail dw (neg0 w) = !cw) := by
          dsimp only [List.take_zero, List.foldl_nil]
          have hkeep0 : ∀ idx < (n + m),
              (Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v)).getD idx false = (oneEach u v).getD idx false := by
            intro idx hidx
            simp only [List.append_nil, Circuit.wires]
            change (gs0.foldl wstep (oneEach u v)).getD idx false = _
            rw [foldl_wstep_getD_lt _ _ _ (by rw [oneEach_len]; exact hidx)]
          constructor
          · dsimp only [pos0]
            have hwn : w < (n + m) := by omega
            simp only [hwn, ite_true, evalRail]
            exact hkeep0 w hwn
          · dsimp only [neg0]
            by_cases h1 : w < n
            · simp only [h1, dite_true]
              have hkeepL : ∀ idx < (n + m) + ([] ++ gL).length,
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
        exact ⟨fun _ => hboth.1, fun _ => hboth.2⟩
    | succ k ih =>
      intro hk1
      have hk : k < C.gates.length := by omega
      obtain ⟨gs, pM, nM, hM, hlen, hbd, hev⟩ := ih (Nat.le_of_lt hk)
      set g := C.gates[k]
      have hg_mem : g ∈ C.gates := List.getElem_mem hk
      have hgF := hF g hg_mem
      have hgop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using hgF.1
      have hglen : g.inputs.length ≤ 2 := hgF.2
      have hgat : gateAt C k = g := by
        simp [gateAt, g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      have hcnt : cnt n m C p h (k + 1) = cnt n m C p h k + cost n m C p h k := by
        unfold cnt
        rw [Finset.sum_range_succ]
      have hInn : ∀ i ∈ g.inputs, i < n + m + k → n + m ≤ i → InCone (n + m) C (i - (n + m)) k := by
        intro i hi h1 h2
        rw [inCone_iff]
        refine ⟨hk, i - (n + m), by omega, ?_, Or.inl rfl⟩
        rw [show n + m + (i - (n + m)) = i by omega, hgat]
        exact hi
      have hkp_of : g.op ≠ GateOp.not → k ≠ p := by
        intro hne hkp
        exact hne (by rw [← hgat, hkp]; exact hpn)
      have hNegk : ((n + m + k) < n + m ∨ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h)) → (k = h ∨ InCone (n + m) C k h) := by
        intro hc
        rcases hc with hc | hc
        · omega
        · simpa only [Nat.add_sub_cancel_left] using hc
      have hPosk : g.op ≠ GateOp.not → ((n + m + k) < n + m ∨ (n + m + k) - (n + m) = p ∨ ¬ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∨ ((((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (((n + m + k) - (n + m)) = r ∨ InCone (n + m) C ((n + m + k) - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) := by
        intro hne hc
        rcases hc with hc | hc | hc
        · omega
        · rw [Nat.add_sub_cancel_left] at hc
          exact absurd hc (hkp_of hne)
        · simpa only [Nat.add_sub_cancel_left] using hc
      have hPin : g.op ≠ GateOp.not → ((n + m + k) < n + m ∨ (n + m + k) - (n + m) = p ∨ ¬ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∨ ((((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (((n + m + k) - (n + m)) = r ∨ InCone (n + m) C ((n + m + k) - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → ∀ i ∈ g.inputs, n + m + k ≤ i ∨ (i < n + m ∨ i - (n + m) = p ∨ ¬ ((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h) ∨ (((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((i - (n + m)) = r ∨ InCone (n + m) C (i - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) := by
        intro hne hc i hi
        by_cases h1 : n + m + k ≤ i
        · exact Or.inl h1
        · right
          by_cases h2 : i < n + m
          · exact Or.inl h2
          · right
            by_cases h3 : i - (n + m) = p
            · exact Or.inl h3
            · right
              by_cases h4 : ((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h)
              · right
                have hrk := hInn i hi (by omega) (by omega)
                rcases hPosk hne hc with h5 | h5
                · refine ⟨h4, i - (n + m), by omega, h4, Or.inl rfl, Or.inr ⟨k, hk, h5, hkp_of hne, ?_⟩⟩
                  rw [show n + m + (i - (n + m)) = i by omega, hgat]
                  exact hi
                · obtain ⟨_, r, hr, hNr, hkr, hexit⟩ := h5
                  refine ⟨h4, r, hr, hNr, Or.inr ?_, hexit⟩
                  rcases hkr with hkr | hkr
                  · exact hkr ▸ hrk
                  · exact inCone_trans (n + m) C _ k hrk r hkr
              · exact Or.inl h4
      have hNin : g.op ≠ GateOp.not → ((n + m + k) < n + m ∨ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h)) → ∀ i ∈ g.inputs, n + m + k ≤ i ∨ (i < n + m ∨ ((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h)) := by
        intro _ hc i hi
        by_cases h1 : n + m + k ≤ i
        · exact Or.inl h1
        · right
          by_cases h2 : i < n + m
          · exact Or.inl h2
          · right
            have hrk := hInn i hi (by omega) (by omega)
            rcases hNegk hc with h3 | h3
            · exact Or.inr (h3 ▸ hrk)
            · exact Or.inr (inCone_trans (n + m) C _ k hrk h h3)
      have hPnot : g.op = GateOp.not → ((n + m + k) < n + m ∨ (n + m + k) - (n + m) = p ∨ ¬ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∨ ((((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (((n + m + k) - (n + m)) = r ∨ InCone (n + m) C ((n + m + k) - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → ∀ a, g.inputs.head? = some a → n + m + k ≤ a ∨ (a < n + m ∨ ((a - (n + m)) = h ∨ InCone (n + m) C (a - (n + m)) h)) := by
        intro hop _ a ha
        right
        right
        have hkp := hnots k hk (by rw [hgat]; exact hop)
        have hph' := hph
        rw [← hkp, hgat, ha] at hph'
        have hae : a = n + m + h := Option.some.inj hph'
        subst hae
        rw [Nat.add_sub_cancel_left]
        exact Or.inl rfl
      have hNnot : g.op = GateOp.not → ((n + m + k) < n + m ∨ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h)) → ∀ a, g.inputs.head? = some a → n + m + k ≤ a ∨ (a < n + m ∨ a - (n + m) = p ∨ ¬ ((a - (n + m)) = h ∨ InCone (n + m) C (a - (n + m)) h) ∨ (((a - (n + m)) = h ∨ InCone (n + m) C (a - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((a - (n + m)) = r ∨ InCone (n + m) C (a - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) := by
        intro hop hc a ha
        have hkp := hnots k hk (by rw [hgat]; exact hop)
        rcases hNegk hc with h3 | h3
        · omega
        · have := (inCone_lt (n + m) C k h h3).1
          omega
      have hC1 : g.op ≠ GateOp.not → ((n + m + k) < n + m ∨ (n + m + k) - (n + m) = p ∨ ¬ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∨ ((((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (((n + m + k) - (n + m)) = r ∨ InCone (n + m) C ((n + m + k) - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) := hPosk
      have hC2 : g.op ≠ GateOp.not → ((n + m + k) < n + m ∨ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h)) → (k = h ∨ InCone (n + m) C k h) := fun _ hc => hNegk hc
      have hcostk : g.op ≠ GateOp.not →
          (if (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) then 1 else 0) + (if (k = h ∨ InCone (n + m) C k h) then 1 else 0) ≤ cost n m C p h k := by
        intro hne
        unfold cost
        rw [ite_eq_right_of_eq_false _ _ (eq_false (hkp_of hne))]

      let getP (i : ℕ) : Rail := if i < (n + m) + k then pM i else .ff
      let getN (i : ℕ) : Rail := if i < (n + m) + k then nM i else .tt
      have hget_bd : ∀ i, railBound ((n + m) + gs0.length + gs.length) (getP i) ∧
                          railBound ((n + m) + gs0.length + gs.length) (getN i) := by
        intro i
        dsimp only [getP, getN]
        by_cases hi : i < (n + m) + k
        · simp only [hi, ite_true]; exact hbd i hi
        · simp only [hi, ite_false]; exact ⟨trivial, trivial⟩
      have hget_ev : ∀ (u : Fin n) (v : Fin m) (i : ℕ),
          let cw := ((C.gates.take k).foldl wstep (oneEach u v)).getD i false
          let dw := Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)
          (((n + m) + k ≤ i ∨ (i < n + m ∨ i - (n + m) = p ∨ ¬ ((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h) ∨ (((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((i - (n + m)) = r ∨ InCone (n + m) C (i - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs)))) → evalRail dw (getP i) = cw) ∧
          (((n + m) + k ≤ i ∨ (i < n + m ∨ ((i - (n + m)) = h ∨ InCone (n + m) C (i - (n + m)) h))) → evalRail dw (getN i) = !cw) := by
        intro u v i
        dsimp only [getP, getN]
        by_cases hi : i < (n + m) + k
        · simp only [hi, ite_true]
          have h := hev u v i hi
          exact ⟨fun hc => h.1 (hc.resolve_left (by omega)), fun hc => h.2 (hc.resolve_left (by omega))⟩
        · simp only [hi, ite_false, evalRail]
          have hcw_len : ((C.gates.take k).foldl wstep (oneEach u v)).length = (n + m) + k := by
            rw [foldl_wstep_len, oneEach_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
          have hcw0 : ((C.gates.take k).foldl wstep (oneEach u v)).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
          rw [hcw0]
          exact ⟨fun _ => rfl, fun _ => rfl⟩
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [g] := List.take_succ_eq_append_getElem hk
      have hfinish : ∀ (gs' : List Gate) (pNew nNew : Rail),
          Monotone2 ⟨gs0 ++ gs', 0⟩ →
          gs.length ≤ gs'.length → gs'.length ≤ gs.length + cost n m C p h k →
          railBound ((n + m) + gs0.length + gs'.length) pNew →
          railBound ((n + m) + gs0.length + gs'.length) nNew →
          (∀ (u : Fin n) (v : Fin m),
            (∀ idx < (n + m) + gs0.length + gs.length,
              (Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)).getD idx false =
              (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false) ∧
            let cw_pre := (C.gates.take k).foldl wstep (oneEach u v)
            let val := g.op.eval (g.inputs.map fun i => cw_pre.getD i false)
            let dw' := Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)
            (((n + m + k) < n + m ∨ (n + m + k) - (n + m) = p ∨ ¬ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∨ ((((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (((n + m + k) - (n + m)) = r ∨ InCone (n + m) C ((n + m + k) - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → evalRail dw' pNew = val) ∧
            (((n + m + k) < n + m ∨ (((n + m + k) - (n + m)) = h ∨ InCone (n + m) C ((n + m + k) - (n + m)) h)) → evalRail dw' nNew = !val)) →
          ∃ (gs'' : List Gate) (pM' nM' : ℕ → Rail),
            Monotone2 ⟨gs0 ++ gs'', 0⟩ ∧
            gs''.length ≤ cnt n m C p h (k + 1) ∧
            (∀ w < (n + m) + (k + 1), railBound ((n + m) + gs0.length + gs''.length) (pM' w) ∧
                                railBound ((n + m) + gs0.length + gs''.length) (nM' w)) ∧
            (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < (n + m) + (k + 1) →
              let cw := ((C.gates.take (k + 1)).foldl wstep (oneEach u v)).getD w false
              let dw := Circuit.wires ⟨gs0 ++ gs'', 0⟩ (oneEach u v)
              ((w < n + m ∨ w - (n + m) = p ∨ ¬ ((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h) ∨ (((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((w - (n + m)) = r ∨ InCone (n + m) C (w - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) → evalRail dw (pM' w) = cw) ∧
              ((w < n + m ∨ ((w - (n + m)) = h ∨ InCone (n + m) C (w - (n + m)) h)) → evalRail dw (nM' w) = !cw)) := by
        intro gs' pNew nNew hM' hge hle hbp hbn hev_new
        let pM' : ℕ → Rail := fun w => if w = (n + m) + k then pNew else pM w
        let nM' : ℕ → Rail := fun w => if w = (n + m) + k then nNew else nM w
        refine ⟨gs', pM', nM', hM', by omega, ?_, ?_⟩
        · intro w hw
          dsimp only [pM', nM']
          by_cases heq : w = (n + m) + k
          · simp only [heq, ite_true]; exact ⟨hbp, hbn⟩
          · simp only [heq, ite_false]
            have hb := hbd w (by omega)
            exact ⟨railBound_mono (by omega) hb.1, railBound_mono (by omega) hb.2⟩
        · intro u v w hw
          obtain ⟨hkeep, hpv, hnv⟩ := hev_new u v
          set cw_pre := (C.gates.take k).foldl wstep (oneEach u v)
          have hpre_len : cw_pre.length = (n + m) + k := by
            simp only [cw_pre, foldl_wstep_len, oneEach_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
          have hcw_next : (C.gates.take (k + 1)).foldl wstep (oneEach u v) =
              cw_pre ++ [g.op.eval (g.inputs.map fun i => cw_pre.getD i false)] := by
            rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
          dsimp only [pM', nM']
          by_cases heq : w = (n + m) + k
          · subst heq
            simp only [ite_true]
            have hval : ((C.gates.take (k + 1)).foldl wstep (oneEach u v)).getD ((n + m) + k) false =
                g.op.eval (g.inputs.map fun i => cw_pre.getD i false) := by
              rw [hcw_next, ← hpre_len, List.getD_append_right _ _ _ _ le_rfl]
              simp only [Nat.sub_self, List.getD_cons_zero]
            rw [hval]
            exact ⟨hpv, hnv⟩
          · simp only [heq, ite_false]
            rw [hcw_next, List.getD_append _ _ _ _ (by omega)]
            have hb := hbd w (by omega)
            have hevw := hev u v w (by omega)
            rw [evalRail_congr hkeep hb.1, evalRail_congr hkeep hb.2]
            exact hevw
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · rcases hgop with hop | hop | hop
        · exact hfinish gs .tt .ff hM le_rfl (by omega) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
        · exact hfinish gs .ff .tt hM le_rfl (by omega) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
        · exact hfinish gs .tt .ff hM le_rfl (by omega) trivial trivial
            (fun u v => ⟨fun _ _ => rfl, by simp [hop, hgi, GateOp.eval, evalRail]⟩)
      · have hain : a ∈ g.inputs := by simp [hgi]
        have hahead : g.inputs.head? = some a := by simp [hgi]
        rcases hgop with hop | hop | hop
        · have hmono : g.op ≠ GateOp.not := by simp [hop]
          exact hfinish gs (getP a) (getN a) hM le_rfl (by omega)
            (hget_bd a).1 (hget_bd a).2
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              dsimp only
              refine ⟨fun hc => ?_, fun hc => ?_⟩
              · have h1 := h.1 (hPin hmono hc a hain)
                simp [hop, hgi, GateOp.eval, h1]
              · have h2 := h.2 (hNin hmono hc a hain)
                simp [hop, hgi, GateOp.eval, h2]⟩)
        · have hmono : g.op ≠ GateOp.not := by simp [hop]
          exact hfinish gs (getP a) (getN a) hM le_rfl (by omega)
            (hget_bd a).1 (hget_bd a).2
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              dsimp only
              refine ⟨fun hc => ?_, fun hc => ?_⟩
              · have h1 := h.1 (hPin hmono hc a hain)
                simp [hop, hgi, GateOp.eval, h1]
              · have h2 := h.2 (hNin hmono hc a hain)
                simp [hop, hgi, GateOp.eval, h2]⟩)
        · exact hfinish gs (getN a) (getP a) hM le_rfl (by omega)
            (hget_bd a).2 (hget_bd a).1
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              dsimp only
              refine ⟨fun hc => ?_, fun hc => ?_⟩
              · have h2 := h.2 (hPnot hop hc a hahead)
                simp [hop, hgi, GateOp.eval, h2]
              · have h1 := h.1 (hNnot hop hc a hahead)
                simp [hop, hgi, GateOp.eval, h1]⟩)
      · have hain : a ∈ g.inputs := by simp [hgi]
        have hbin : b ∈ g.inputs := by simp [hgi]
        have hahead : g.inputs.head? = some a := by simp [hgi]
        rcases hgop with hop | hop | hop
        · have hmono : g.op ≠ GateOp.not := by simp [hop]
          obtain ⟨res1, hM1, hge1, hle1, hbd1, hev1⟩ := railAndC_spec (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) (n + m) gs0 gs hM
            (getP a) (getP b) (hget_bd a).1 (hget_bd b).1
          obtain ⟨res2, hM2, hge2, hle2, hbd2, hev2⟩ := railOrC_spec (k = h ∨ InCone (n + m) C k h) (n + m) gs0 res1.1 hM1
            (getN a) (getN b)
            (railBound_mono (by omega) (hget_bd a).2) (railBound_mono (by omega) (hget_bd b).2)
          have hcost : res2.1.length ≤ gs.length + cost n m C p h k := by
            have hck := hcostk hmono
            split_ifs at hle1 hle2 hck <;> omega
          refine hfinish res2.1 res1.2 res2.2 hM2 (by omega) hcost
            (railBound_mono (by omega) hbd1) hbd2 ?_
          intro u v
          have h1 := hev1 (oneEach u v) (oneEach_len u v)
          have h2 := hev2 (oneEach u v) (oneEach_len u v)
          have hkeep : ∀ idx < (n + m) + gs0.length + gs.length,
              (Circuit.wires ⟨gs0 ++ res2.1, 0⟩ (oneEach u v)).getD idx false =
              (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false := by
            intro idx hidx
            rw [h2.1 idx (by omega), h1.1 idx hidx]
          have ha := hget_ev u v a
          have hb := hget_ev u v b
          refine ⟨hkeep, fun hc => ?_, fun hc => ?_⟩
          · rw [evalRail_congr h2.1 hbd1, h1.2 (hC1 hmono hc)]
            have ha1 := ha.1 (hPin hmono hc a hain)
            have hb1 := hb.1 (hPin hmono hc b hbin)
            simp [hop, hgi, GateOp.eval, ha1, hb1]
          · rw [h2.2 (hC2 hmono hc)]
            rw [evalRail_congr h1.1 (hget_bd a).2, evalRail_congr h1.1 (hget_bd b).2]
            have ha2 := ha.2 (hNin hmono hc a hain)
            have hb2 := hb.2 (hNin hmono hc b hbin)
            simp [hop, hgi, GateOp.eval, ha2, hb2, Bool.not_and]
        · have hmono : g.op ≠ GateOp.not := by simp [hop]
          obtain ⟨res1, hM1, hge1, hle1, hbd1, hev1⟩ := railOrC_spec (¬ (k = h ∨ InCone (n + m) C k h) ∨ ((k = h ∨ InCone (n + m) C k h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ (k = r ∨ InCone (n + m) C k r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) (n + m) gs0 gs hM
            (getP a) (getP b) (hget_bd a).1 (hget_bd b).1
          obtain ⟨res2, hM2, hge2, hle2, hbd2, hev2⟩ := railAndC_spec (k = h ∨ InCone (n + m) C k h) (n + m) gs0 res1.1 hM1
            (getN a) (getN b)
            (railBound_mono (by omega) (hget_bd a).2) (railBound_mono (by omega) (hget_bd b).2)
          have hcost : res2.1.length ≤ gs.length + cost n m C p h k := by
            have hck := hcostk hmono
            split_ifs at hle1 hle2 hck <;> omega
          refine hfinish res2.1 res1.2 res2.2 hM2 (by omega) hcost
            (railBound_mono (by omega) hbd1) hbd2 ?_
          intro u v
          have h1 := hev1 (oneEach u v) (oneEach_len u v)
          have h2 := hev2 (oneEach u v) (oneEach_len u v)
          have hkeep : ∀ idx < (n + m) + gs0.length + gs.length,
              (Circuit.wires ⟨gs0 ++ res2.1, 0⟩ (oneEach u v)).getD idx false =
              (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD idx false := by
            intro idx hidx
            rw [h2.1 idx (by omega), h1.1 idx hidx]
          have ha := hget_ev u v a
          have hb := hget_ev u v b
          refine ⟨hkeep, fun hc => ?_, fun hc => ?_⟩
          · rw [evalRail_congr h2.1 hbd1, h1.2 (hC1 hmono hc)]
            have ha1 := ha.1 (hPin hmono hc a hain)
            have hb1 := hb.1 (hPin hmono hc b hbin)
            simp [hop, hgi, GateOp.eval, ha1, hb1]
          · rw [h2.2 (hC2 hmono hc)]
            rw [evalRail_congr h1.1 (hget_bd a).2, evalRail_congr h1.1 (hget_bd b).2]
            have ha2 := ha.2 (hNin hmono hc a hain)
            have hb2 := hb.2 (hNin hmono hc b hbin)
            simp [hop, hgi, GateOp.eval, ha2, hb2, Bool.not_or]
        · exact hfinish gs (getN a) (getP a) hM le_rfl (by omega)
            (hget_bd a).2 (hget_bd a).1
            (fun u v => ⟨fun _ _ => rfl, by
              have h := hget_ev u v a
              dsimp only
              refine ⟨fun hc => ?_, fun hc => ?_⟩
              · have h2 := h.2 (hPnot hop hc a hahead)
                simp [hop, hgi, GateOp.eval, h2]
              · have h1 := h.1 (hNnot hop hc a hahead)
                simp [hop, hgi, GateOp.eval, h1]⟩)
      · simp [hgi] at hglen
  obtain ⟨gs, pM, nM, hM, hlen, hbd, hev⟩ := hSim C.gates.length le_rfl
  have hcb := cnt_bound n m C p h hp
  have hsz' : C.gates.length ≤ s := hsz
  by_cases hout : C.output < (n + m) + C.gates.length
  ·
    have hokout : (C.output < n + m ∨ C.output - (n + m) = p ∨ ¬ ((C.output - (n + m)) = h ∨ InCone (n + m) C (C.output - (n + m)) h) ∨ (((C.output - (n + m)) = h ∨ InCone (n + m) C (C.output - (n + m)) h) ∧ ∃ r < C.gates.length, (r = h ∨ InCone (n + m) C r h) ∧ ((C.output - (n + m)) = r ∨ InCone (n + m) C (C.output - (n + m)) r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (gateAt C j).inputs))) := by
      by_cases h1 : C.output < n + m
      · exact Or.inl h1
      · right
        by_cases h2 : C.output - (n + m) = p
        · exact Or.inl h2
        · right
          by_cases h3 : ((C.output - (n + m)) = h ∨ InCone (n + m) C (C.output - (n + m)) h)
          · exact Or.inr ⟨h3, C.output - (n + m), by omega, h3, Or.inl rfl, Or.inl (by omega)⟩
          · exact Or.inl h3
    cases hpo : pM C.output with
    | ff =>
      refine ⟨⟨gs0 ++ gs, (n + m) + (gs0 ++ gs).length⟩, hM, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1 hokout
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        unfold Circuit.eval
        change (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD ((n + m) + (gs0 ++ gs).length) false =
               (C.gates.foldl wstep (oneEach u v)).getD C.output false
        rw [← h1]
        simp only [evalRail]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · unfold Circuit.wires
          change ((gs0 ++ gs).foldl wstep (oneEach u v)).length ≤ _
          rw [foldl_wstep_len, oneEach_len]
    | tt =>
      refine ⟨⟨[⟨.and, []⟩], (n + m)⟩, ?_, ?_, ?_⟩
      · intro g hg
        rw [List.mem_singleton] at hg
        subst hg
        exact ⟨Or.inl rfl, by decide⟩
      · simp only [Circuit.size, List.length_singleton]
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1 hokout
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        unfold Circuit.eval
        change ((([⟨.and, []⟩] : List Gate).foldl wstep (oneEach u v)).getD (n + m) false) =
               (C.gates.foldl wstep (oneEach u v)).getD C.output false
        rw [← h1]
        simp only [evalRail]
        rw [List.foldl_cons, List.foldl_nil]
        dsimp only [wstep]
        rw [← oneEach_len u v, List.getD_append_right _ _ _ _ le_rfl]
        simp [GateOp.eval]
    | wire p0 =>
      refine ⟨⟨gs0 ++ gs, p0⟩, hM, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        omega
      · intro u v
        have h1 := (hev u v C.output hout).1 hokout
        rw [hpo, List.take_length] at h1
        have hrep := hRep u v
        rw [← hrep]
        exact h1
  · refine ⟨⟨gs0 ++ gs, (n + m) + (gs0 ++ gs).length⟩, hM, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append]
      omega
    · intro u v
      have hrep := hRep u v
      rw [← hrep]
      unfold Circuit.eval
      have h1 : (Circuit.wires ⟨gs0 ++ gs, (n + m) + (gs0 ++ gs).length⟩ (oneEach u v)).getD ((n + m) + (gs0 ++ gs).length) false = false := by
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

end PEqualNP.Outside.L_meta_19172_aux

theorem PEqualNP.Outside.L_meta_19172 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → p < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → h < p → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p) → PEqualNP.Represents.RepSizeAtMost A (s - 1 + ((Finset.range C.gates.length).filter (fun i => (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) ∧ (i = r ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs))).card + ((3 * n - 6) + (3 * m - 6))) :=
  fun n m s A C p h hF hsz hRep hp hpn hph hhp hnots =>
    PEqualNP.Outside.L_meta_19172_aux.main n m s A C p h hF hsz hRep hp hpn hph hhp hnots
