import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3805

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private lemma foldl_snoc_length {α β : Type*} (h : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_snoc_getD_lt {α β : Type*} (h : List α → β → α) (gs : List β) (init : List α)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [h init g]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih (init ++ [h init g]) hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma foldl_snoc_getD_add {α β : Type*} (h : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (d : α) (hj : j < gs.length) :
    (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD (init.length + j) d =
      h ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init) (gs[j]) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, Nat.add_zero]
      have hlt : init.length < (init ++ [h init g]).length := by
        rw [List.length_append, List.length_singleton]; omega
      rw [foldl_snoc_getD_lt h gs (init ++ [h init g]) init.length d hlt]
      simp [List.getD_eq_getElem?_getD]
    | succ j =>
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have hlen : (init ++ [h init g]).length = init.length + 1 := by simp
      have hj' : j < gs.length := by simp at hj; omega
      have hidx : init.length + (j + 1) = (init ++ [h init g]).length + j := by rw [hlen]; omega
      rw [hidx]
      exact ih (init ++ [h init g]) j hj'

private lemma foldl_snoc_take_getD {α β : Type*} (h : List α → β → α) (gs : List β) (init : List α)
    (j k : ℕ) (d : α) (hj : j ≤ gs.length) (hk : k < init.length + j) :
    ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).getD k d =
      (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD k d := by
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + j := by
    rw [foldl_snoc_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_snoc_getD_lt h (gs.drop j) _ k d (by omega)]

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  unfold opnd
  have hb : (b : ℕ) < (gateAt C j).inputs.length := by omega
  rw [List.getD_eq_getElem _ _ hb]
  exact List.getElem_mem hb

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem_inputs hAO j hj b)

private lemma inputs_eq_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  match h : (gateAt C j).inputs with
  | [a, b] =>
    unfold opnd
    simp [h]
  | [] => simp [h] at hlen
  | [_] => simp [h] at hlen
  | _ :: _ :: _ :: _ => simp [h] at hlen

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hlt : i.val < (List.ofFn x).length := by simp
  rw [foldl_snoc_getD_lt (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates (List.ofFn x) i.val false hlt]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma gateVal_eq_wireVal {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

private lemma gateVal_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateVal n C j x = (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
  unfold gateVal Circuit.wires
  let f : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)
  have hlen : (List.ofFn x).length = n := by simp
  have hstep := foldl_snoc_getD_add f C.gates (List.ofFn x) j false hj
  rw [hlen] at hstep
  change (C.gates.foldl (fun acc g => acc ++ [f acc g]) (List.ofFn x)).getD (n + j) false = _
  rw [hstep, ← gateAt_eq_getElem C j hj]
  simp only [f]
  rw [inputs_eq_two hAO j hj]
  simp only [List.map_cons, List.map_nil]
  have h0 : opnd C j 0 < (List.ofFn x).length + j := by rw [hlen]; exact opnd_lt hAO j hj 0
  have h1 : opnd C j 1 < (List.ofFn x).length + j := by rw [hlen]; exact opnd_lt hAO j hj 1
  rw [foldl_snoc_take_getD f C.gates (List.ofFn x) j (opnd C j 0) false (Nat.le_of_lt hj) h0]
  rw [foldl_snoc_take_getD f C.gates (List.ofFn x) j (opnd C j 1) false (Nat.le_of_lt hj) h1]
  rfl

private lemma gateVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [gateVal_eval hAO j hj x, hand]
  simp [GateOp.eval]

private lemma gateVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C j x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [gateVal_eval hAO j hj x, hor]
  simp [GateOp.eval]

private lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones coneStep
  simpa using foldl_snoc_length
    (fun (cs : List (List ℕ)) (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates []

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  unfold InCone cones coneStep
  change i ∈ (C.gates.foldl (fun acc g => acc ++ [f acc g]) []).getD j [] ↔ _
  have hstep := foldl_snoc_getD_add f C.gates [] j [] hj
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep, ← gateAt_eq_getElem C j hj]
  have hplen : ((C.gates.take j).foldl (fun acc g => acc ++ [f acc g]) []).length = j := by
    rw [foldl_snoc_length, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  simp only [f, hplen, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hnw, hlt⟩, hi⟩
    refine ⟨w, hw, hnw, hlt, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
      rwa [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub] at hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ⟨hw, hnw, hlt⟩, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
      rwa [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub]

private lemma inCone_bounds (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j → i < j ∧ j < C.gates.length := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    by_cases hj : j < C.gates.length
    · rw [inCone_iff n C i j hj] at h
      rcases h with ⟨w, _, hnw, hlt, rfl | h2⟩
      · exact ⟨by omega, hj⟩
      · have ⟨h1, _⟩ := ih (w - n) (by omega) h2
        exact ⟨by omega, hj⟩
    · exfalso
      unfold InCone at h
      have hlen : (cones n C).length = C.gates.length := cones_length n C
      have hge : (cones n C).length ≤ j := by omega
      rw [List.getD_eq_default _ _ hge] at h
      simp at h

private lemma inCone_trans (n : ℕ) (C : Circuit) (i k j : ℕ) :
    InCone n C i k → InCone n C k j → InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hik hkj
    have ⟨_, hj⟩ := inCone_bounds n C k j hkj
    rw [inCone_iff n C k j hj] at hkj
    rw [inCone_iff n C i j hj]
    rcases hkj with ⟨w, hw, hnw, hlt, rfl | hkw⟩
    · exact ⟨w, hw, hnw, hlt, Or.inr hik⟩
    · exact ⟨w, hw, hnw, hlt, Or.inr (ih (w - n) (by omega) hik hkw)⟩

private lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  simpa using foldl_snoc_length
    (fun (cs : List (List ℕ)) (g : Gate) =>
      cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else []))
    C.gates []

private lemma orReaches_iff_gate (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq _ _)
      ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []))
      [])
  unfold OrReaches orSets orStep
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, true_and]
  change g ∈ (C.gates.foldl (fun acc g => acc ++ [f acc g]) []).getD j [] ↔ _
  have hstep := foldl_snoc_getD_add f C.gates [] j [] hj
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [hstep, ← gateAt_eq_getElem C j hj]
  have hplen : ((C.gates.take j).foldl (fun acc g => acc ++ [f acc g]) []).length = j := by
    rw [foldl_snoc_length, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  simp only [f, hplen, List.mem_cons]
  constructor
  · rintro (rfl | hmem)
    · exact Or.inl rfl
    · right
      split_ifs at hmem with hor
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hmem
        rcases hmem with ⟨w, ⟨hw, hnw, hlt⟩, hg⟩
        have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
        rw [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub] at hg
        exact ⟨hor, w, hw, hnw, hlt, hnw, hg⟩
      · simp at hmem
  · rintro (rfl | ⟨hor, w, hw, hnw, hlt, _, hg⟩)
    · exact Or.inl rfl
    · right
      rw [if_pos hor]
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
      refine ⟨w, ⟨hw, hnw, hlt⟩, ?_⟩
      have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
      rwa [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub]

private lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff_gate n C j j hj).2 (Or.inl rfl)

private lemma orReaches_bounds (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length ∧ g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hlt : w - n < C.gates.length := by
    by_contra hge
    have hge' : (orSets n C).length ≤ w - n := by rw [orSets_length]; omega
    have hmem := h.2
    rw [List.getD_eq_default _ _ hge'] at hmem
    simp at hmem
  suffices ∀ j < C.gates.length, OrReaches n C (n + j) g → g ≤ j by
    have hwn : n + (w - n) = w := Nat.add_sub_of_le hnw
    exact ⟨hnw, hlt, this (w - n) hlt (by rwa [hwn])⟩
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hreach
    rw [orReaches_iff_gate n C j g hj] at hreach
    rcases hreach with rfl | ⟨_, w', _, hnw', hlt', hr'⟩
    · exact le_rfl
    · have hsub : w' - n < j := by omega
      have hwn' : n + (w' - n) = w' := Nat.add_sub_of_le hnw'
      have hle := ih (w' - n) hsub (by omega) (by rwa [hwn'])
      omega

private lemma orReaches_trans (n : ℕ) (C : Circuit) (w k g : ℕ) :
    OrReaches n C w k → OrReaches n C (n + k) g → OrReaches n C w g := by
  intro h1 h2
  have ⟨hnw, hlt, _⟩ := orReaches_bounds n C w k h1
  have hwn : n + (w - n) = w := Nat.add_sub_of_le hnw
  rw [← hwn] at h1 ⊢
  generalize w - n = j at hlt h1 ⊢
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_iff_gate n C j k hlt] at h1
    rcases h1 with rfl | ⟨hor, w', hw', hnw', hlt', hr'⟩
    · exact h2
    · rw [orReaches_iff_gate n C j g hlt]
      right
      refine ⟨hor, w', hw', hnw', hlt', ?_⟩
      have hwn' : n + (w' - n) = w' := Nat.add_sub_of_le hnw'
      rw [← hwn'] at hr' ⊢
      exact ih (w' - n) (by omega) (by omega) hr'

private lemma orReaches_gateVal {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w g : ℕ) (x : Fin n → Bool) (h : OrReaches n C w g) (hg : gateVal n C g x = true) :
    wireVal n C w x = true := by
  have ⟨hnw, hlt, _⟩ := orReaches_bounds n C w g h
  have hwn : n + (w - n) = w := Nat.add_sub_of_le hnw
  rw [← hwn] at h ⊢
  generalize w - n = j at hlt h ⊢
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_iff_gate n C j g hlt] at h
    rcases h with rfl | ⟨hor, w', hw', hnw', hlt', hr'⟩
    · exact hg
    · rw [← gateVal_eq_wireVal, gateVal_or hAO j hlt hor x]
      have hwn' : n + (w' - n) = w' := Nat.add_sub_of_le hnw'
      have hwv : wireVal n C w' x = true := by
        rw [← hwn'] at hr' ⊢
        exact ih (w' - n) (by omega) (by omega) hr'
      rw [inputs_eq_two hAO j hlt] at hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · simp [hwv]
      · simp [hwv]

private lemma orIn_sound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (u : Fin n) (x : Fin n → Bool) (hu : u ∈ orIn n C w) (hx : x u = true) :
    wireVal n C w x = true := by
  unfold orIn at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | ⟨k, hk, hreach, hor, hmem⟩
  · rw [wireVal_input]; exact hx
  · apply orReaches_gateVal hAO w k x hreach
    rw [gateVal_or hAO k hk hor x]
    rw [inputs_eq_two hAO k hk] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h0 | h1
    · rw [← h0, wireVal_input]; simp [hx]
    · rw [← h1, wireVal_input]; simp [hx]

private lemma orIn_mono_of_orReaches (n : ℕ) (C : Circuit) (w k : ℕ)
    (h : OrReaches n C w k) :
    orIn n C (n + k) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with heq | ⟨j, hj, hreach, hor, hmem⟩
  · omega
  · exact Or.inr ⟨j, hj, orReaches_trans n C w k j h hreach, hor, hmem⟩

private lemma orIn_or_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heq | ⟨k, hk, hreach, hork, hmem⟩)
    · omega
    · rw [orReaches_iff_gate n C j k hj] at hreach
      rcases hreach with hkj | ⟨_, w, hw, hnw, hlt, hr⟩
      · rw [hkj, inputs_eq_two hAO j hj] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · rw [inputs_eq_two hAO j hj] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hr, hork, hmem⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hr, hork, hmem⟩)
  · rintro ((h0 | ⟨k, hk, hr, hork, hmem⟩) | (h1 | ⟨k, hk, hr, hork, hmem⟩))
    · right
      refine ⟨j, hj, orReaches_self n C j hj, hor, ?_⟩
      rw [h0]; exact opnd_mem_inputs hAO j hj 0
    · right
      have ⟨hnw, _, _⟩ := orReaches_bounds n C (opnd C j 0) k hr
      refine ⟨k, hk, ?_, hork, hmem⟩
      rw [orReaches_iff_gate n C j k hj]
      exact Or.inr ⟨hor, opnd C j 0, opnd_mem_inputs hAO j hj 0, hnw, opnd_lt hAO j hj 0, hr⟩
    · right
      refine ⟨j, hj, orReaches_self n C j hj, hor, ?_⟩
      rw [h1]; exact opnd_mem_inputs hAO j hj 1
    · right
      have ⟨hnw, _, _⟩ := orReaches_bounds n C (opnd C j 1) k hr
      refine ⟨k, hk, ?_, hork, hmem⟩
      rw [orReaches_iff_gate n C j k hj]
      exact Or.inr ⟨hor, opnd C j 1, opnd_mem_inputs hAO j hj 1, hnw, opnd_lt hAO j hj 1, hr⟩

private lemma orIn_input_card_le (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    (orIn n C w).card ≤ 1 := by
  have hsub : orIn n C w ⊆ {⟨w, hw⟩} := by
    intro u hu
    unfold orIn at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with heq | ⟨_, _, hreach, _, _⟩
    · simp only [Finset.mem_singleton]
      exact Fin.ext heq
    · have hnw := hreach.1
      omega
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma orIn_and_eq_empty (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (heq | ⟨k, hk, hreach, hork, _⟩)
  · omega
  · rw [orReaches_iff_gate n C j k hj] at hreach
    rcases hreach with rfl | ⟨hor, _⟩
    · rw [hand] at hork; cases hork
    · rw [hand] at hor; cases hor

private lemma wireVal_of_or_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g : ℕ) (hcone : ∀ k, InCone n C k g → (gateAt C k).op = GateOp.or)
    (w : ℕ) (hwo : ∀ k, w = n + k → InCone n C k g) (x : Fin n → Bool) :
    wireVal n C w x = true ↔ ∃ z ∈ orIn n C w, x z = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    constructor
    · intro hw
      by_cases hwn : w < n
      · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · unfold orIn; simp
        · rwa [← wireVal_input C ⟨w, hwn⟩ x]
      · set k := w - n
        have hwk : w = n + k := by omega
        have hinc : InCone n C k g := hwo k hwk
        have ⟨hkg, hglt⟩ := inCone_bounds n C k g hinc
        have hk : k < C.gates.length := by omega
        have hork : (gateAt C k).op = GateOp.or := hcone k hinc
        rw [hwk, ← gateVal_eq_wireVal, gateVal_or hAO k hk hork x, Bool.or_eq_true] at hw
        rw [hwk, orIn_or_eq hAO k hk hork]
        rcases hw with h0 | h1
        · have h0lt : opnd C k 0 < w := by rw [hwk]; exact opnd_lt hAO k hk 0
          have h0wo : ∀ k', opnd C k 0 = n + k' → InCone n C k' g := by
            intro k' hk'
            apply inCone_trans n C k' k g _ hinc
            rw [inCone_iff n C k' k hk]
            exact ⟨opnd C k 0, opnd_mem_inputs hAO k hk 0, by omega, opnd_lt hAO k hk 0, Or.inl (by omega)⟩
          obtain ⟨z, hz, hxz⟩ := (ih (opnd C k 0) h0lt h0wo).1 h0
          exact ⟨z, Finset.mem_union_left _ hz, hxz⟩
        · have h1lt : opnd C k 1 < w := by rw [hwk]; exact opnd_lt hAO k hk 1
          have h1wo : ∀ k', opnd C k 1 = n + k' → InCone n C k' g := by
            intro k' hk'
            apply inCone_trans n C k' k g _ hinc
            rw [inCone_iff n C k' k hk]
            exact ⟨opnd C k 1, opnd_mem_inputs hAO k hk 1, by omega, opnd_lt hAO k hk 1, Or.inl (by omega)⟩
          obtain ⟨z, hz, hxz⟩ := (ih (opnd C k 1) h1lt h1wo).1 h1
          exact ⟨z, Finset.mem_union_right _ hz, hxz⟩
    · rintro ⟨z, hz, hxz⟩
      exact orIn_sound hAO w z x hz hxz

private lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} :
    g ∈ junk G C ↔ g < C.gates.length ∧ IsDirtyAnd n G C g := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

private lemma mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {a : ℕ} :
    a ∈ tops G C ↔ a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  unfold tops gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]

private lemma junk_cone_or_only {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hNoCone : ∀ g1 ∈ junk G C, ∀ g2 ∈ junk G C, ¬ InCone n C g1 g2)
    {g : ℕ} (hg : g ∈ junk G C) (k : ℕ) (hk : InCone n C k g) :
    (gateAt C k).op = GateOp.or := by
  have ⟨hkg, hglt⟩ := inCone_bounds n C k g hk
  have hklt : k < C.gates.length := by omega
  have hgk_or_and : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
    rw [gateAt_eq_getElem C k hklt]
    exact hAO.1 C.gates[k] (List.getElem_mem hklt)
  rcases hgk_or_and with hand | hor
  · exfalso
    have hgand : (gateAt C g).op = GateOp.and := (mem_junk_iff.1 hg).2.1
    by_cases hbf : BelowF G C k
    · exact hTF k hklt g hglt hand hbf hgand hk
    · have hk_junk : k ∈ junk G C := by
        rw [mem_junk_iff]
        refine ⟨hklt, hand, hklt, ?_⟩
        unfold BelowF at hbf
        push_neg at hbf
        rcases hbf with ⟨x, hkx, hfx⟩
        exact ⟨x, hkx, Bool.eq_false_iff.2 hfx⟩
      exact hNoCone k hk_junk g hg hk
  · exact hor

private lemma junk_gateVal_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hNoCone : ∀ g1 ∈ junk G C, ∀ g2 ∈ junk G C, ¬ InCone n C g1 g2)
    {g : ℕ} (hg : g ∈ junk G C) (x : Fin n → Bool) :
    gateVal n C g x = true ↔
      (∃ p ∈ side C g 0, x p = true) ∧ (∃ q ∈ side C g 1, x q = true) := by
  have hglt : g < C.gates.length := (mem_junk_iff.1 hg).1
  have hgand : (gateAt C g).op = GateOp.and := (mem_junk_iff.1 hg).2.1
  rw [gateVal_and hAO g hglt hgand x, Bool.and_eq_true]
  have hcone : ∀ k, InCone n C k g → (gateAt C k).op = GateOp.or :=
    junk_cone_or_only hAO hTF hNoCone hg
  have h0 : ∀ k, opnd C g 0 = n + k → InCone n C k g := by
    intro k hk
    rw [inCone_iff n C k g hglt]
    exact ⟨opnd C g 0, opnd_mem_inputs hAO g hglt 0, by omega, opnd_lt hAO g hglt 0, Or.inl (by omega)⟩
  have h1 : ∀ k, opnd C g 1 = n + k → InCone n C k g := by
    intro k hk
    rw [inCone_iff n C k g hglt]
    exact ⟨opnd C g 1, opnd_mem_inputs hAO g hglt 1, by omega, opnd_lt hAO g hglt 1, Or.inl (by omega)⟩
  rw [wireVal_of_or_cone hAO g hcone (opnd C g 0) h0 x]
  rw [wireVal_of_or_cone hAO g hcone (opnd C g 1) h1 x]
  rfl

private lemma graphFun_empty_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun
  simp

private lemma top_wmax {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {a g : ℕ} {b : Fin 2} {u : Fin n}
    (ha : a ∈ tops G C) (hu : u ∈ side C a b) (hr : OrReaches n C (opnd C a (1 - b)) g)
    (x : Fin n → Bool) (hxu : x u = true) (hxg : gateVal n C g x = true) :
    ∃ v1 v2 : Fin n, G.Adj v1 v2 ∧ x v1 = true ∧ x v2 = true := by
  obtain ⟨halt, haand, habf⟩ := mem_tops_iff.1 ha
  have h1 : wireVal n C (opnd C a b) x = true := orIn_sound hAO (opnd C a b) u x hu hxu
  have h2 : wireVal n C (opnd C a (1 - b)) x = true := orReaches_gateVal hAO (opnd C a (1 - b)) g x hr hxg
  have ha_true : gateVal n C a x = true := by
    rw [gateVal_and hAO a halt haand x, Bool.and_eq_true]
    fin_cases b
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  exact (graphFun_empty_true x).1 (habf x ha_true)

private lemma noFourCycle_of_girth5 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) :
    NoFourCycle G := by
  intro a b hab
  rw [Finset.card_le_one]
  intro w1 hw1 w2 hw2
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  have hw1a : w1 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw1.1)
  have hw1b : w1 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw1.2)
  have hw2a : w2 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw2.1)
  have hw2b : w2 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw2.2)
  let p : G.Walk a a :=
    SimpleGraph.Walk.cons hw1.1
      (SimpleGraph.Walk.cons hw1.2.symm
        (SimpleGraph.Walk.cons hw2.2
          (SimpleGraph.Walk.cons hw2.1.symm SimpleGraph.Walk.nil)))
  have hcyc : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp [p, SimpleGraph.Walk.edges, Sym2.eq_iff, hw1a, hw1b, hw2a, hw2b, hab, hne,
        hab.symm, Ne.symm hne, hw1a.symm, hw1b.symm, hw2a.symm, hw2b.symm]
    · simp [p]
    · simp [p, SimpleGraph.Walk.support, hw1a, hw2a, hw1b, hw2b, hab, hne, hab.symm, Ne.symm hne,
        hw1a.symm, hw2a.symm, hw1b.symm, hw2b.symm]
  have hlen := hgirth a p hcyc
  simp [p] at hlen

private lemma nbr_inter_card_le_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter (G.Adj a) ∩ Finset.univ.filter (G.Adj b)).card ≤ 1 := by
  have heq : Finset.univ.filter (G.Adj a) ∩ Finset.univ.filter (G.Adj b) =
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    ext w; simp
  rw [heq]
  exact h4 a b hab

private lemma at_most_two_centers {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun c : Fin n =>
      3 ≤ (S ∩ Finset.univ.filter (G.Adj c)).card ∧
      ∃ p : Fin n, S ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p))).card ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  set F := Finset.univ.filter (fun c : Fin n =>
    3 ≤ (S ∩ Finset.univ.filter (G.Adj c)).card ∧
    ∃ p : Fin n, S ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p))
  obtain ⟨c0, hc0⟩ := Finset.card_pos.1 (by omega : 0 < F.card)
  have hF1 : 1 < (F.erase c0).card := by rw [Finset.card_erase_of_mem hc0]; omega
  obtain ⟨c1, hc1⟩ := Finset.card_pos.1 (by omega : 0 < (F.erase c0).card)
  have hF2 : 0 < ((F.erase c0).erase c1).card := by rw [Finset.card_erase_of_mem hc1]; omega
  obtain ⟨c2, hc2⟩ := Finset.card_pos.1 hF2
  rw [Finset.mem_erase] at hc2
  rw [Finset.mem_erase] at hc1 hc2
  have h01 : c0 ≠ c1 := hc1.1.symm
  have h02 : c0 ≠ c2 := hc2.2.1.symm
  have h12 : c1 ≠ c2 := hc2.1.symm
  have hc0' := (Finset.mem_filter.1 hc0).2
  have hc1' := (Finset.mem_filter.1 hc1.2).2
  have hc2' := (Finset.mem_filter.1 hc2.2.2).2
  obtain ⟨_, p0, hp0⟩ := hc0'
  have hbound : ∀ c : Fin n, c ≠ c0 → c ≠ p0 → (S ∩ Finset.univ.filter (G.Adj c)).card ≤ 2 := by
    intro c hcc0 hcp0
    have hsub : S ∩ Finset.univ.filter (G.Adj c) ⊆
        (Finset.univ.filter (G.Adj c0) ∩ Finset.univ.filter (G.Adj c)) ∪
        (Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj c)) := by
      intro w hw
      rw [Finset.mem_inter] at hw
      have hwp := hp0 hw.1
      rw [Finset.mem_union] at hwp ⊢
      rcases hwp with h | h
      · exact Or.inl (Finset.mem_inter.2 ⟨h, hw.2⟩)
      · exact Or.inr (Finset.mem_inter.2 ⟨h, hw.2⟩)
    calc (S ∩ Finset.univ.filter (G.Adj c)).card
        ≤ ((Finset.univ.filter (G.Adj c0) ∩ Finset.univ.filter (G.Adj c)) ∪
            (Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj c))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (G.Adj c0) ∩ Finset.univ.filter (G.Adj c)).card +
            (Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj c)).card :=
          Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (nbr_inter_card_le_one h4 hcc0.symm) (nbr_inter_card_le_one h4 hcp0.symm)
      _ = 2 := rfl
  by_cases h1p : c1 = p0
  · have h2p : c2 ≠ p0 := by rw [← h1p]; exact h12.symm
    have := hbound c2 h02.symm h2p
    have := hc2'.1
    omega
  · have := hbound c1 h01.symm h1p
    have := hc1'.1
    omega

private lemma card_biUnion_le_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → Finset β) (k : ℕ) (h : ∀ a ∈ s, (f a).card ≤ k) :
    (s.biUnion f).card ≤ s.card * k := by
  calc (s.biUnion f).card
      ≤ ∑ a ∈ s, (f a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ s, k := Finset.sum_le_sum h
    _ = s.card * k := by simp

private lemma edge_bound_bucketA {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h4 : NoFourCycle G) (hAO : IsAO2 n C) :
    (G.edgeFinset.filter (fun e => ∃ c d : Fin n, e = s(c, d) ∧
      ∃ k < C.gates.length, ∃ b : Fin 2,
        d ∈ orIn n C (opnd C k b) ∧
        3 ≤ (orIn n C (opnd C k b) ∩ Finset.univ.filter (G.Adj c)).card ∧
        ∃ p : Fin n, orIn n C (opnd C k b) ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p))).card
      ≤ 8 * C.size := by
  let T : Fin n → Finset ℕ := fun c =>
    (Finset.range C.gates.length).filter (fun h =>
      (gateAt C h).op = GateOp.or ∧
      3 ≤ (orIn n C (n + h) ∩ Finset.univ.filter (G.Adj c)).card ∧
      ∃ p : Fin n, orIn n C (n + h) ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p))
  let E_of : Fin n → ℕ → Fin 2 → Finset (Sym2 (Fin n)) := fun c h b =>
    if (orIn n C (opnd C h b) ∩ Finset.univ.filter (G.Adj c)).card ≤ 2 then
      (orIn n C (opnd C h b) ∩ Finset.univ.filter (G.Adj c)).image (fun d => s(c, d))
    else ∅
  have hsub : G.edgeFinset.filter (fun e => ∃ c d : Fin n, e = s(c, d) ∧
      ∃ k < C.gates.length, ∃ b : Fin 2,
        d ∈ orIn n C (opnd C k b) ∧
        3 ≤ (orIn n C (opnd C k b) ∩ Finset.univ.filter (G.Adj c)).card ∧
        ∃ p : Fin n, orIn n C (opnd C k b) ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p)) ⊆
      Finset.univ.biUnion (fun c : Fin n => (T c).biUnion (fun h => Finset.univ.biUnion (fun b : Fin 2 => E_of c h b))) := by
    intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨hedge, c, d, rfl, k, hk, b, hd, hcard3, p, hp⟩ := he
    have hadj : G.Adj c d := G.mem_edgeSet.1 hedge
    have hwn : n ≤ opnd C k b := by
      by_contra hlt
      have := orIn_input_card_le n C (opnd C k b) (by omega)
      have := Finset.card_le_card (Finset.inter_subset_left (s₁ := orIn n C (opnd C k b)) (s₂ := Finset.univ.filter (G.Adj c)))
      omega
    set h0 := opnd C k b - n
    have hh0eq : opnd C k b = n + h0 := by omega
    have hh0lt : h0 < C.gates.length := by
      have := opnd_lt hAO k hk b
      omega
    have hh0or : (gateAt C h0).op = GateOp.or := by
      have hok : (gateAt C h0).op = GateOp.and ∨ (gateAt C h0).op = GateOp.or := by
        rw [gateAt_eq_getElem C h0 hh0lt]
        exact hAO.1 C.gates[h0] (List.getElem_mem hh0lt)
      rcases hok with hand | hor
      · exfalso
        rw [hh0eq, orIn_and_eq_empty n C h0 hh0lt hand] at hcard3
        simp at hcard3
      · exact hor
    have hh0T : h0 ∈ T c := by
      simp only [T, Finset.mem_filter, Finset.mem_range]
      exact ⟨hh0lt, hh0or, by rwa [← hh0eq], p, by rwa [← hh0eq]⟩
    let Sd := (T c).filter (fun h => d ∈ orIn n C (n + h))
    have hSd_ne : Sd.Nonempty := ⟨h0, Finset.mem_filter.2 ⟨hh0T, by rwa [← hh0eq]⟩⟩
    set h := Sd.min' hSd_ne
    have hhSd : h ∈ Sd := Finset.min'_mem Sd hSd_ne
    have hhT : h ∈ T c := (Finset.mem_filter.1 hhSd).1
    have hdh : d ∈ orIn n C (n + h) := (Finset.mem_filter.1 hhSd).2
    have hhT' := Finset.mem_filter.1 hhT
    have hhlt : h < C.gates.length := Finset.mem_range.1 hhT'.1
    obtain ⟨hhor, hhcard3, ph, hph⟩ := hhT'.2
    rw [orIn_or_eq hAO h hhlt hhor, Finset.mem_union] at hdh
    have hex : ∃ b' : Fin 2, d ∈ orIn n C (opnd C h b') := by
      rcases hdh with h0' | h1'
      · exact ⟨0, h0'⟩
      · exact ⟨1, h1'⟩
    obtain ⟨b', hdb'⟩ := hex
    have hle2 : (orIn n C (opnd C h b') ∩ Finset.univ.filter (G.Adj c)).card ≤ 2 := by
      by_contra hgt2
      push_neg at hgt2
      have hwn' : n ≤ opnd C h b' := by
        by_contra hlt'
        have := orIn_input_card_le n C (opnd C h b') (by omega)
        have := Finset.card_le_card (Finset.inter_subset_left (s₁ := orIn n C (opnd C h b')) (s₂ := Finset.univ.filter (G.Adj c)))
        omega
      set h' := opnd C h b' - n
      have hh'eq : opnd C h b' = n + h' := by omega
      have hh'lt_h : h' < h := by
        have := opnd_lt hAO h hhlt b'
        omega
      have hh'lt : h' < C.gates.length := by omega
      have hh'or : (gateAt C h').op = GateOp.or := by
        have hok : (gateAt C h').op = GateOp.and ∨ (gateAt C h').op = GateOp.or := by
          rw [gateAt_eq_getElem C h' hh'lt]
          exact hAO.1 C.gates[h'] (List.getElem_mem hh'lt)
        rcases hok with hand | hor
        · exfalso
          rw [hh'eq, orIn_and_eq_empty n C h' hh'lt hand] at hgt2
          simp at hgt2
        · exact hor
      have hh'reach : OrReaches n C (n + h) h' := by
        rw [orReaches_iff_gate n C h h' hhlt]
        right
        exact ⟨hhor, opnd C h b', opnd_mem_inputs hAO h hhlt b', hwn', opnd_lt hAO h hhlt b',
          by rw [hh'eq]; exact orReaches_self n C h' hh'lt⟩
      have hh'sub : orIn n C (n + h') ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj ph) :=
        (orIn_mono_of_orReaches n C (n + h) h' hh'reach).trans hph
      have hh'T : h' ∈ T c := by
        simp only [T, Finset.mem_filter, Finset.mem_range]
        exact ⟨hh'lt, hh'or, by rwa [← hh'eq], ph, hh'sub⟩
      have hh'Sd : h' ∈ Sd := Finset.mem_filter.2 ⟨hh'T, by rwa [← hh'eq]⟩
      have hmin := Finset.min'_le Sd h' hh'Sd
      omega
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨c, h, hhT, b', ?_⟩
    simp only [E_of, if_pos hle2, Finset.mem_image, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨d, ⟨hdb', hadj⟩, rfl⟩
  have hstep1 : (Finset.univ.biUnion (fun c : Fin n => (T c).biUnion (fun h => Finset.univ.biUnion (fun b : Fin 2 => E_of c h b)))).card ≤
      ∑ c : Fin n, 4 * (T c).card := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c _ => ?_)
    have hinner : ∀ h ∈ T c, (Finset.univ.biUnion (fun b : Fin 2 => E_of c h b)).card ≤ 4 := by
      intro h _
      calc (Finset.univ.biUnion (fun b : Fin 2 => E_of c h b)).card
          ≤ ∑ b : Fin 2, (E_of c h b).card := Finset.card_biUnion_le
        _ ≤ ∑ _b : Fin 2, 2 := by
            refine Finset.sum_le_sum fun b _ => ?_
            simp only [E_of]
            split_ifs with hle
            · exact Finset.card_image_le.trans hle
            · simp
        _ = 4 := by simp
    have := card_biUnion_le_mul (T c) (fun h => Finset.univ.biUnion (fun b : Fin 2 => E_of c h b)) 4 hinner
    omega
  have hstep2 : (∑ c : Fin n, (T c).card) ≤ 2 * C.gates.length := by
    have hswap : ∑ c : Fin n, (T c).card =
        ∑ h ∈ Finset.range C.gates.length, (Finset.univ.filter (fun c : Fin n => h ∈ T c)).card := by
      simp only [Finset.card_eq_sum_ones]
      calc ∑ c : Fin n, ∑ _h ∈ T c, 1
          = ∑ c : Fin n, ∑ h ∈ Finset.range C.gates.length, if h ∈ T c then 1 else 0 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← Finset.sum_filter]
            congr 1
            ext h
            simp only [Finset.mem_filter]
            exact ⟨fun hh => ⟨(Finset.mem_filter.1 hh).1, hh⟩, fun hh => hh.2⟩
        _ = ∑ h ∈ Finset.range C.gates.length, ∑ c : Fin n, if h ∈ T c then 1 else 0 :=
            Finset.sum_comm
        _ = ∑ h ∈ Finset.range C.gates.length, ∑ _c ∈ Finset.univ.filter (fun c : Fin n => h ∈ T c), 1 := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [Finset.sum_filter]
    rw [hswap]
    calc ∑ h ∈ Finset.range C.gates.length, (Finset.univ.filter (fun c : Fin n => h ∈ T c)).card
        ≤ ∑ _h ∈ Finset.range C.gates.length, 2 := by
          refine Finset.sum_le_sum fun h _ => ?_
          have hsub' : Finset.univ.filter (fun c : Fin n => h ∈ T c) ⊆
              Finset.univ.filter (fun c : Fin n =>
                3 ≤ (orIn n C (n + h) ∩ Finset.univ.filter (G.Adj c)).card ∧
                ∃ p : Fin n, orIn n C (n + h) ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p)) := by
            intro c hc
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hc ⊢
            exact hc.2.2
          exact (Finset.card_le_card hsub').trans (at_most_two_centers h4 (orIn n C (n + h)))
      _ = 2 * C.gates.length := by simp [Nat.mul_comm]
  calc _ ≤ ∑ c : Fin n, 4 * (T c).card := (Finset.card_le_card hsub).trans hstep1
    _ = 4 * ∑ c : Fin n, (T c).card := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * C.gates.length) := Nat.mul_le_mul_left 4 hstep2
    _ = 8 * C.size := by unfold Circuit.size; omega

private def vSpecial {n : ℕ} (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  (if (side (n := n) C g 0).card = 1 then side (n := n) C g 0 else ∅) ∪
  (if (side (n := n) C g 1).card = 1 then side (n := n) C g 1 else ∅) ∪
  (if (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1 then side (n := n) C g 0 ∩ side (n := n) C g 1 else ∅)

private lemma vSpecial_card_le {n : ℕ} (C : Circuit) (g : ℕ) :
    (vSpecial (n := n) C g).card ≤ 3 := by
  unfold vSpecial
  have h0 : (if (side (n := n) C g 0).card = 1 then side (n := n) C g 0 else ∅).card ≤ 1 := by
    split_ifs with h <;> simp [h]
  have h1 : (if (side (n := n) C g 1).card = 1 then side (n := n) C g 1 else ∅).card ≤ 1 := by
    split_ifs with h <;> simp [h]
  have h2 : (if (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1 then
      side (n := n) C g 0 ∩ side (n := n) C g 1 else ∅).card ≤ 1 := by
    split_ifs with h <;> simp [h]
  calc _ ≤ (if (side (n := n) C g 0).card = 1 then side (n := n) C g 0 else ∅).card +
            (if (side (n := n) C g 1).card = 1 then side (n := n) C g 1 else ∅).card +
            (if (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1 then
              side (n := n) C g 0 ∩ side (n := n) C g 1 else ∅).card := by
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 1 + 1 + 1 := by omega
    _ = 3 := rfl

private lemma edge_bound_bucketB {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h4 : NoFourCycle G) (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hNoCone : ∀ g1 ∈ junk G C, ∀ g2 ∈ junk G C, ¬ InCone n C g1 g2) :
    (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        v ∈ vSpecial (n := n) C g ∧
        u ∈ side C a b ∧
        (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 ∧
        OrReaches n C (opnd C a (1 - b)) g)).card ≤ 40 * C.size := by
  let U : ℕ → Finset (Fin n) := fun h =>
    Finset.univ.filter (fun u => ∃ a ∈ tops G C, ∃ b : Fin 2,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) h)
  let H : Fin n → Finset ℕ := fun v =>
    (Finset.range C.gates.length).filter (fun h =>
      (gateAt C h).op = GateOp.or ∧
      (∃ g ∈ junk G C, OrReaches n C (n + h) g) ∧
      3 ≤ (U h ∩ Finset.univ.filter (G.Adj v)).card)
  have hH_le_two : ∀ h : ℕ, (Finset.univ.filter (fun v : Fin n => h ∈ H v)).card ≤ 2 := by
    intro h
    by_cases hex : ∃ g ∈ junk G C, OrReaches n C (n + h) g
    · obtain ⟨g, hg, hrhg⟩ := hex
      have hdirty : IsDirtyAnd n G C g := (mem_junk_iff.1 hg).2
      obtain ⟨_, _, x0, hgx0, hfx0⟩ := hdirty
      obtain ⟨⟨p0, hp0, hxp0⟩, ⟨q0, hq0, hxq0⟩⟩ := (junk_gateVal_iff hAO hTF hNoCone hg x0).1 hgx0
      have hna : ¬ G.Adj p0 q0 := by
        intro hadj
        have htrue : graphFun G ∅ x0 = true :=
          (graphFun_empty_true x0).2 ⟨p0, q0, hadj, hxp0, hxq0⟩
        rw [hfx0] at htrue; cases htrue
      have hUsub : U h ⊆ Finset.univ.filter (G.Adj p0) ∪ Finset.univ.filter (G.Adj q0) := by
        intro u hu
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨a, ha, b, hua, hrah⟩ := hu
        have hrag : OrReaches n C (opnd C a (1 - b)) g :=
          orReaches_trans n C (opnd C a (1 - b)) h g hrah hrhg
        let x : Fin n → Bool := fun w => decide (w = u ∨ w = p0 ∨ w = q0)
        have hxu : x u = true := by simp [x]
        have hxg : gateVal n C g x = true := by
          rw [junk_gateVal_iff hAO hTF hNoCone hg x]
          exact ⟨⟨p0, hp0, by simp [x]⟩, ⟨q0, hq0, by simp [x]⟩⟩
        obtain ⟨v1, v2, hadj, hv1, hv2⟩ := top_wmax hAO ha hua hrag x hxu hxg
        simp only [x, decide_eq_true_eq] at hv1 hv2
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hv1 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl
        · exact False.elim (G.loopless.irrefl _ hadj)
        · exact Or.inl hadj.symm
        · exact Or.inr hadj.symm
        · exact Or.inl hadj
        · exact False.elim (G.loopless.irrefl _ hadj)
        · exact False.elim (hna hadj)
        · exact Or.inr hadj
        · exact False.elim (hna hadj.symm)
        · exact False.elim (G.loopless.irrefl _ hadj)
      have hsub : Finset.univ.filter (fun v : Fin n => h ∈ H v) ⊆ {p0, q0} := by
        intro v hv
        simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv
        by_contra hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hsub' : U h ∩ Finset.univ.filter (G.Adj v) ⊆
            (Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj v)) ∪
            (Finset.univ.filter (G.Adj q0) ∩ Finset.univ.filter (G.Adj v)) := by
          intro w hw
          rw [Finset.mem_inter] at hw
          have hw' := hUsub hw.1
          rw [Finset.mem_union] at hw' ⊢
          rcases hw' with h1 | h2
          · exact Or.inl (Finset.mem_inter.2 ⟨h1, hw.2⟩)
          · exact Or.inr (Finset.mem_inter.2 ⟨h2, hw.2⟩)
        have hle2 : (U h ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 := by
          calc (U h ∩ Finset.univ.filter (G.Adj v)).card
              ≤ ((Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj v)) ∪
                  (Finset.univ.filter (G.Adj q0) ∩ Finset.univ.filter (G.Adj v))).card :=
                Finset.card_le_card hsub'
            _ ≤ (Finset.univ.filter (G.Adj p0) ∩ Finset.univ.filter (G.Adj v)).card +
                  (Finset.univ.filter (G.Adj q0) ∩ Finset.univ.filter (G.Adj v)).card :=
                Finset.card_union_le _ _
            _ ≤ 1 + 1 := Nat.add_le_add (nbr_inter_card_le_one h4 (Ne.symm hnot.1))
                (nbr_inter_card_le_one h4 (Ne.symm hnot.2))
            _ = 2 := rfl
        have hge3 : 3 ≤ (U h ∩ Finset.univ.filter (G.Adj v)).card := hv.2.2.2
        omega
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · have hemp : Finset.univ.filter (fun v : Fin n => h ∈ H v) = ∅ := by
        ext v
        simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hc
        exact hex hc.2.2.1
      rw [hemp]; simp
  let B1 : ℕ → Fin 2 → Finset (Sym2 (Fin n)) := fun a b =>
    let g := opnd C a (1 - b) - n
    (vSpecial (n := n) C g).biUnion (fun v =>
      if (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
        (side C a b ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v))
      else ∅)
  let B2 : ℕ → Fin 2 → Finset (Sym2 (Fin n)) := fun a b =>
    let h0 := opnd C a (1 - b) - n
    (Finset.univ.filter (fun v : Fin n => h0 ∈ H v)).biUnion (fun v =>
      if (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
        (side C a b ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v))
      else ∅)
  let B3 : ℕ → Fin 2 → Finset (Sym2 (Fin n)) := fun h1 b' =>
    let h2 := opnd C h1 b' - n
    ((Finset.univ.filter (fun v : Fin n => h2 ∈ H v)) ∪ vSpecial (n := n) C h2).biUnion (fun v =>
      if (U h1 ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
        (U h1 ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v))
      else ∅)
  have hsub : G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        v ∈ vSpecial (n := n) C g ∧
        u ∈ side C a b ∧
        (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 ∧
        OrReaches n C (opnd C a (1 - b)) g) ⊆
      ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B1 a b))) ∪
      ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B2 a b))) ∪
      ((Finset.range C.gates.length).biUnion (fun h1 => Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b'))) := by
    intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨hedge, u, v, rfl, a, ha, b, g, hg, hvsp, hu, hle2, hreach⟩ := he
    have hadj : G.Adj u v := G.mem_edgeSet.1 hedge
    have halt : a < C.gates.length := (mem_tops_iff.1 ha).1
    have ⟨hnw, hh0lt, _⟩ := orReaches_bounds n C (opnd C a (1 - b)) g hreach
    set h0 := opnd C a (1 - b) - n
    have hh0eq : opnd C a (1 - b) = n + h0 := by omega
    by_cases h0g : h0 = g
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
      refine ⟨a, halt, b, ?_⟩
      simp only [B1, Finset.mem_biUnion]
      refine ⟨v, by rwa [show opnd C a (1 - b) - n = g from h0g], ?_⟩
      rw [if_pos hle2]
      simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, ⟨hu, hadj.symm⟩, rfl⟩
    · by_cases h0H : h0 ∈ H v
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
        refine ⟨a, halt, b, ?_⟩
        simp only [B2, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨v, h0H, ?_⟩
        rw [if_pos hle2]
        simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, ⟨hu, hadj.symm⟩, rfl⟩
      · apply Finset.mem_union_right
        let Spath := (Finset.range C.gates.length).filter (fun h =>
          OrReaches n C (opnd C a (1 - b)) h ∧ OrReaches n C (n + h) g ∧ h ∉ H v ∧ h ≠ g)
        have hSpath_ne : Spath.Nonempty := by
          refine ⟨h0, Finset.mem_filter.2 ⟨Finset.mem_range.2 hh0lt, ?_, ?_, h0H, h0g⟩⟩
          · rw [hh0eq]; exact orReaches_self n C h0 hh0lt
          · rwa [← hh0eq]
        set h1 := Spath.min' hSpath_ne
        have hh1m := Finset.mem_filter.1 (Finset.min'_mem Spath hSpath_ne)
        have hh1lt : h1 < C.gates.length := Finset.mem_range.1 hh1m.1
        obtain ⟨hr_ah1, hr_h1g, hh1notH, hh1neg⟩ := hh1m.2
        rw [orReaches_iff_gate n C h1 g hh1lt] at hr_h1g
        rcases hr_h1g with hEq | ⟨hh1or, w', hw', hnw', hw'lt, hr_w'g⟩
        · exact False.elim (hh1neg hEq.symm)
        · rw [inputs_eq_two hAO h1 hh1lt] at hw'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
          have hex : ∃ b' : Fin 2, opnd C h1 b' = w' := by
            rcases hw' with h0w | h1w
            · exact ⟨0, h0w.symm⟩
            · exact ⟨1, h1w.symm⟩
          obtain ⟨b', hb'⟩ := hex
          set h2 := opnd C h1 b' - n
          have hh2eq : opnd C h1 b' = n + h2 := by omega
          have hh2lt_h1 : h2 < h1 := by omega
          have hh2lt : h2 < C.gates.length := by omega
          have hr_ah2 : OrReaches n C (opnd C a (1 - b)) h2 := by
            apply orReaches_trans n C (opnd C a (1 - b)) h1 h2 hr_ah1
            rw [orReaches_iff_gate n C h1 h2 hh1lt]
            right
            exact ⟨hh1or, opnd C h1 b', opnd_mem_inputs hAO h1 hh1lt b', by omega, by omega,
              by rw [hh2eq]; exact orReaches_self n C h2 hh2lt⟩
          have hr_h2g : OrReaches n C (n + h2) g := by
            rw [← hh2eq, hb']; exact hr_w'g
          have hh2_mem : h2 ∈ H v ∨ h2 = g := by
            by_contra hneither
            push_neg at hneither
            have hh2S : h2 ∈ Spath :=
              Finset.mem_filter.2 ⟨Finset.mem_range.2 hh2lt, hr_ah2, hr_h2g, hneither.1, hneither.2⟩
            have hmin := Finset.min'_le Spath h2 hh2S
            omega
          have hUh1_le : (U h1 ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 := by
            by_contra hgt2
            push_neg at hgt2
            have hh1H : h1 ∈ H v := by
              simp only [H, Finset.mem_filter, Finset.mem_range]
              refine ⟨hh1lt, hh1or, ⟨g, hg, ?_⟩, hgt2⟩
              rw [orReaches_iff_gate n C h1 g hh1lt]
              exact Or.inr ⟨hh1or, w', by rw [← hb']; exact opnd_mem_inputs hAO h1 hh1lt b', hnw', hw'lt, hr_w'g⟩
            exact hh1notH hh1H
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
          refine ⟨h1, hh1lt, b', ?_⟩
          simp only [B3, Finset.mem_biUnion, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨v, ?_, ?_⟩
          · rcases hh2_mem with h2H | h2g
            · exact Or.inl h2H
            · right; rwa [show opnd C h1 b' - n = g from h2g]
          · rw [if_pos hUh1_le]
            simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨u, ⟨?_, hadj.symm⟩, rfl⟩
            simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨a, ha, b, hu, hr_ah1⟩
  have hB1 : ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B1 a b))).card ≤ 12 * C.size := by
    have hinner : ∀ a ∈ Finset.range C.gates.length, (Finset.univ.biUnion (fun b : Fin 2 => B1 a b)).card ≤ 12 := by
      intro a _
      calc (Finset.univ.biUnion (fun b : Fin 2 => B1 a b)).card
          ≤ ∑ b : Fin 2, (B1 a b).card := Finset.card_biUnion_le
        _ ≤ ∑ _b : Fin 2, 6 := by
            refine Finset.sum_le_sum fun b _ => ?_
            have h1 := card_biUnion_le_mul (vSpecial (n := n) C (opnd C a (1 - b) - n))
              (fun v => if (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
                (side C a b ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v)) else ∅) 2 (by
                intro v _
                split_ifs with hle
                · exact Finset.card_image_le.trans hle
                · simp)
            have h2 := vSpecial_card_le (n := n) C (opnd C a (1 - b) - n)
            exact h1.trans (by omega)
        _ = 12 := by simp
    have := card_biUnion_le_mul (Finset.range C.gates.length) (fun a => Finset.univ.biUnion (fun b : Fin 2 => B1 a b)) 12 hinner
    simp only [Finset.card_range] at this
    unfold Circuit.size; omega
  have hB2 : ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B2 a b))).card ≤ 8 * C.size := by
    have hinner : ∀ a ∈ Finset.range C.gates.length, (Finset.univ.biUnion (fun b : Fin 2 => B2 a b)).card ≤ 8 := by
      intro a _
      calc (Finset.univ.biUnion (fun b : Fin 2 => B2 a b)).card
          ≤ ∑ b : Fin 2, (B2 a b).card := Finset.card_biUnion_le
        _ ≤ ∑ _b : Fin 2, 4 := by
            refine Finset.sum_le_sum fun b _ => ?_
            have h1 := card_biUnion_le_mul (Finset.univ.filter (fun v : Fin n => opnd C a (1 - b) - n ∈ H v))
              (fun v => if (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
                (side C a b ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v)) else ∅) 2 (by
                intro v _
                split_ifs with hle
                · exact Finset.card_image_le.trans hle
                · simp)
            have h2 := hH_le_two (opnd C a (1 - b) - n)
            exact h1.trans (by omega)
        _ = 8 := by simp
    have := card_biUnion_le_mul (Finset.range C.gates.length) (fun a => Finset.univ.biUnion (fun b : Fin 2 => B2 a b)) 8 hinner
    simp only [Finset.card_range] at this
    unfold Circuit.size; omega
  have hB3 : ((Finset.range C.gates.length).biUnion (fun h1 => Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b'))).card ≤ 20 * C.size := by
    have hinner : ∀ h1 ∈ Finset.range C.gates.length, (Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b')).card ≤ 20 := by
      intro h1 _
      calc (Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b')).card
          ≤ ∑ b' : Fin 2, (B3 h1 b').card := Finset.card_biUnion_le
        _ ≤ ∑ _b' : Fin 2, 10 := by
            refine Finset.sum_le_sum fun b' _ => ?_
            have h1' := card_biUnion_le_mul
              ((Finset.univ.filter (fun v : Fin n => opnd C h1 b' - n ∈ H v)) ∪ vSpecial (n := n) C (opnd C h1 b' - n))
              (fun v => if (U h1 ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 then
                (U h1 ∩ Finset.univ.filter (G.Adj v)).image (fun u => s(u, v)) else ∅) 2 (by
                intro v _
                split_ifs with hle
                · exact Finset.card_image_le.trans hle
                · simp)
            have h2' : ((Finset.univ.filter (fun v : Fin n => opnd C h1 b' - n ∈ H v)) ∪
                vSpecial (n := n) C (opnd C h1 b' - n)).card ≤ 5 := by
              exact (Finset.card_union_le _ _).trans
                (Nat.add_le_add (hH_le_two (opnd C h1 b' - n)) (vSpecial_card_le (n := n) C (opnd C h1 b' - n)))
            exact h1'.trans (by omega)
        _ = 20 := by simp
    have := card_biUnion_le_mul (Finset.range C.gates.length) (fun h1 => Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b')) 20 hinner
    simp only [Finset.card_range] at this
    unfold Circuit.size; omega
  calc _ ≤ (((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B1 a b))) ∪
            ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B2 a b))) ∪
            ((Finset.range C.gates.length).biUnion (fun h1 => Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b')))).card :=
          Finset.card_le_card hsub
    _ ≤ ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B1 a b))).card +
        ((Finset.range C.gates.length).biUnion (fun a => Finset.univ.biUnion (fun b : Fin 2 => B2 a b))).card +
        ((Finset.range C.gates.length).biUnion (fun h1 => Finset.univ.biUnion (fun b' : Fin 2 => B3 h1 b'))).card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 12 * C.size + 8 * C.size + 20 * C.size := by omega
    _ = 40 * C.size := by omega

private lemma edge_bound_type1_small {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h4 : NoFourCycle G) :
    (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
      (v ∈ side (n := n) C g 1 ∧ (side (n := n) C g 1).card = 2 ∧ ∀ q ∈ side (n := n) C g 1, G.Adj u q) ∨
      (v ∈ side (n := n) C g 0 ∧ (side (n := n) C g 0).card = 2 ∧ ∀ p ∈ side (n := n) C g 0, G.Adj u p) ∨
      (v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 ∧
        2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card ∧
        (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2 ∧
        ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w))).card ≤ 6 * C.size := by
  have huniq : ∀ S : Finset (Fin n), 2 ≤ S.card →
      (Finset.univ.filter (fun u : Fin n => ∀ w ∈ S, G.Adj u w)).card ≤ 1 := by
    intro S hS
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    have hsub : Finset.univ.filter (fun u : Fin n => ∀ w ∈ S, G.Adj u w) ⊆
        Finset.univ.filter (G.Adj w1) ∩ Finset.univ.filter (G.Adj w2) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter] at hu ⊢
      exact ⟨(hu w1 hw1).symm, (hu w2 hw2).symm⟩
    exact (Finset.card_le_card hsub).trans (nbr_inter_card_le_one h4 hne)
  let F1 : ℕ → Finset (Sym2 (Fin n)) := fun g =>
    if (side (n := n) C g 1).card = 2 then
      (Finset.univ.filter (fun u : Fin n => ∀ q ∈ side (n := n) C g 1, G.Adj u q)).biUnion
        (fun u => (side (n := n) C g 1).image (fun v => s(u, v)))
    else ∅
  let F2 : ℕ → Finset (Sym2 (Fin n)) := fun g =>
    if (side (n := n) C g 0).card = 2 then
      (Finset.univ.filter (fun u : Fin n => ∀ p ∈ side (n := n) C g 0, G.Adj u p)).biUnion
        (fun u => (side (n := n) C g 0).image (fun v => s(u, v)))
    else ∅
  let F3 : ℕ → Finset (Sym2 (Fin n)) := fun g =>
    if 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card then
      (Finset.univ.filter (fun u : Fin n => ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w)).biUnion
        (fun u => if (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2 then
          (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).image (fun v => s(u, v)) else ∅)
    else ∅
  have hsub : G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
      (v ∈ side (n := n) C g 1 ∧ (side (n := n) C g 1).card = 2 ∧ ∀ q ∈ side (n := n) C g 1, G.Adj u q) ∨
      (v ∈ side (n := n) C g 0 ∧ (side (n := n) C g 0).card = 2 ∧ ∀ p ∈ side (n := n) C g 0, G.Adj u p) ∨
      (v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 ∧
        2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card ∧
        (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2 ∧
        ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w)) ⊆
      (Finset.range C.gates.length).biUnion (fun g => F1 g ∪ F2 g ∪ F3 g) := by
    intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨hedge, u, v, rfl, g, hg, hcase⟩ := he
    have hadj : G.Adj u v := G.mem_edgeSet.1 hedge
    simp only [Finset.mem_biUnion, Finset.mem_range]
    refine ⟨g, hg, ?_⟩
    rcases hcase with ⟨hv, hc, hall⟩ | ⟨hv, hc, hall⟩ | ⟨hv, hc, hle2, hall⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [F1, if_pos hc, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨u, hall, v, hv, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [F2, if_pos hc, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨u, hall, v, hv, rfl⟩
    · apply Finset.mem_union_right
      simp only [F3, if_pos hc, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨u, hall, ?_⟩
      rw [if_pos hle2]
      simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, ⟨(Finset.mem_inter.1 hv).2, hadj⟩, rfl⟩
  have hF : ∀ g ∈ Finset.range C.gates.length, (F1 g ∪ F2 g ∪ F3 g).card ≤ 6 := by
    intro g _
    have h1 : (F1 g).card ≤ 2 := by
      simp only [F1]
      split_ifs with hc
      · have := card_biUnion_le_mul (Finset.univ.filter (fun u : Fin n => ∀ q ∈ side (n := n) C g 1, G.Adj u q))
          (fun u => (side (n := n) C g 1).image (fun v => s(u, v))) 2 (fun u _ => Finset.card_image_le.trans (by omega))
        have hu := huniq (side (n := n) C g 1) (by omega)
        omega
      · simp
    have h2 : (F2 g).card ≤ 2 := by
      simp only [F2]
      split_ifs with hc
      · have := card_biUnion_le_mul (Finset.univ.filter (fun u : Fin n => ∀ p ∈ side (n := n) C g 0, G.Adj u p))
          (fun u => (side (n := n) C g 0).image (fun v => s(u, v))) 2 (fun u _ => Finset.card_image_le.trans (by omega))
        have hu := huniq (side (n := n) C g 0) (by omega)
        omega
      · simp
    have h3 : (F3 g).card ≤ 2 := by
      simp only [F3]
      split_ifs with hc
      · have := card_biUnion_le_mul
          (Finset.univ.filter (fun u : Fin n => ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w))
          (fun u => if (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2 then
            (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).image (fun v => s(u, v)) else ∅) 2 (by
            intro u _
            split_ifs with hle
            · exact Finset.card_image_le.trans hle
            · simp)
        have hu := huniq (side (n := n) C g 0 ∩ side (n := n) C g 1) hc
        omega
      · simp
    exact ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)).trans (by omega)
  have htot := card_biUnion_le_mul (Finset.range C.gates.length) (fun g => F1 g ∪ F2 g ∪ F3 g) 6 hF
  simp only [Finset.card_range] at htot
  calc _ ≤ ((Finset.range C.gates.length).biUnion (fun g => F1 g ∪ F2 g ∪ F3 g)).card :=
        Finset.card_le_card hsub
    _ ≤ 6 * C.size := by unfold Circuit.size; omega

private lemma main_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    (hNoCone : ∀ g1 ∈ junk G C, ∀ g2 ∈ junk G C, ¬ InCone n C g1 g2) :
    {e ∈ Ustar G C | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput u v) = Bool.true}.card ≤ 54 * (C.size + 1) := by
  have h4 : NoFourCycle G := noFourCycle_of_girth5 hgirth
  have hAO : IsAO2 n C := hLeast.1
  let SA := G.edgeFinset.filter (fun e => ∃ c d : Fin n, e = s(c, d) ∧
    ∃ k < C.gates.length, ∃ b : Fin 2,
      d ∈ orIn n C (opnd C k b) ∧
      3 ≤ (orIn n C (opnd C k b) ∩ Finset.univ.filter (G.Adj c)).card ∧
      ∃ p : Fin n, orIn n C (opnd C k b) ⊆ Finset.univ.filter (G.Adj c) ∪ Finset.univ.filter (G.Adj p))
  let SB := G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      v ∈ vSpecial (n := n) C g ∧
      u ∈ side C a b ∧
      (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2 ∧
      OrReaches n C (opnd C a (1 - b)) g)
  let S1 := G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
    (v ∈ side (n := n) C g 1 ∧ (side (n := n) C g 1).card = 2 ∧ ∀ q ∈ side (n := n) C g 1, G.Adj u q) ∨
    (v ∈ side (n := n) C g 0 ∧ (side (n := n) C g 0).card = 2 ∧ ∀ p ∈ side (n := n) C g 0, G.Adj u p) ∨
    (v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 ∧
      2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card ∧
      (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2 ∧
      ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w))
  have hsub : {e ∈ Ustar G C | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput u v) = Bool.true} ⊆ SA ∪ SB ∪ S1 := by
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨hU, u, v, rfl, a, ha, b, g, hg, hu, hreach, hgv⟩ := he
    have hedge : s(u, v) ∈ G.edgeFinset := (Finset.mem_sdiff.1 hU).1
    have hadj : G.Adj u v := G.mem_edgeSet.1 (SimpleGraph.mem_edgeFinset.1 hedge)
    have halt : a < C.gates.length := (mem_tops_iff.1 ha).1
    have hglt : g < C.gates.length := (mem_junk_iff.1 hg).1
    have hdirty : IsDirtyAnd n G C g := (mem_junk_iff.1 hg).2
    obtain ⟨_, _, x0, hgx0, hfx0⟩ := hdirty
    obtain ⟨⟨p0, hp0, hxp0⟩, ⟨q0, hq0, hxq0⟩⟩ := (junk_gateVal_iff hAO hTF hNoCone hg x0).1 hgx0
    have hna : ¬ G.Adj p0 q0 := by
      intro hadj'
      have htrue : graphFun G ∅ x0 = true := (graphFun_empty_true x0).2 ⟨p0, q0, hadj', hxp0, hxq0⟩
      rw [hfx0] at htrue; cases htrue
    have hside_sub : side C a b ⊆ Finset.univ.filter (G.Adj p0) ∪ Finset.univ.filter (G.Adj q0) := by
      intro w hw
      let x : Fin n → Bool := fun z => decide (z = w ∨ z = p0 ∨ z = q0)
      have hxw : x w = true := by simp [x]
      have hxg : gateVal n C g x = true := by
        rw [junk_gateVal_iff hAO hTF hNoCone hg x]
        exact ⟨⟨p0, hp0, by simp [x]⟩, ⟨q0, hq0, by simp [x]⟩⟩
      obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hw hreach x hxw hxg
      simp only [x, decide_eq_true_eq] at hv1 hv2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv1 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl
      · exact False.elim (G.loopless.irrefl _ hadj')
      · exact Or.inl hadj'.symm
      · exact Or.inr hadj'.symm
      · exact Or.inl hadj'
      · exact False.elim (G.loopless.irrefl _ hadj')
      · exact False.elim (hna hadj')
      · exact Or.inr hadj'
      · exact False.elim (hna hadj'.symm)
      · exact False.elim (G.loopless.irrefl _ hadj')
    obtain ⟨⟨p, hp, hpp⟩, ⟨q, hq, hqq⟩⟩ := (junk_gateVal_iff hAO hTF hNoCone hg (pairInput u v)).1 hgv
    simp only [pairInput, decide_eq_true_eq] at hpp hqq
    rcases hpp with hpu | hpv <;> rcases hqq with hqu | hqv
    · rw [hpu] at hp; rw [hqu] at hq
      exfalso
      have hgu : gateVal n C g (pairInput u u) = true := by
        rw [junk_gateVal_iff hAO hTF hNoCone hg (pairInput u u)]
        exact ⟨⟨u, hp, by simp [pairInput]⟩, ⟨u, hq, by simp [pairInput]⟩⟩
      obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hu hreach (pairInput u u) (by simp [pairInput]) hgu
      simp only [pairInput, decide_eq_true_eq, or_self] at hv1 hv2
      subst hv1; subst hv2
      exact G.loopless.irrefl _ hadj'
    · rw [hpu] at hp; rw [hqv] at hq
      have hB_sub : side (n := n) C g 1 ⊆ Finset.univ.filter (G.Adj u) := by
        intro q' hq'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hguq : gateVal n C g (pairInput u q') = true := by
          rw [junk_gateVal_iff hAO hTF hNoCone hg (pairInput u q')]
          exact ⟨⟨u, hp, by simp [pairInput]⟩, ⟨q', hq', by simp [pairInput]⟩⟩
        obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hu hreach (pairInput u q') (by simp [pairInput]) hguq
        simp only [pairInput, decide_eq_true_eq] at hv1 hv2
        rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
        · exact False.elim (G.loopless.irrefl _ hadj')
        · exact hadj'
        · exact hadj'.symm
        · exact False.elim (G.loopless.irrefl _ hadj')
      have hBpos : 0 < (side (n := n) C g 1).card := Finset.card_pos.2 ⟨v, hq⟩
      by_cases hB1 : (side (n := n) C g 1).card = 1
      · have hq0v : q0 = v := Finset.card_le_one.1 (le_of_eq hB1) q0 hq0 v hq
        have hvsp : v ∈ vSpecial (n := n) C g := by
          unfold vSpecial
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (by rw [if_pos hB1]; exact hq))
        by_cases hle2 : (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          simp only [SB, Finset.mem_filter]
          exact ⟨hedge, u, v, rfl, a, ha, b, g, hg, hvsp, hu, hle2, hreach⟩
        · push_neg at hle2
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [SA, Finset.mem_filter]
          refine ⟨hedge, v, u, Sym2.eq_swap, a, halt, b, hu, hle2, p0, ?_⟩
          intro w hw
          have := hside_sub hw
          rw [hq0v] at this
          rw [Finset.mem_union] at this ⊢
          tauto
      · by_cases hB2 : (side (n := n) C g 1).card = 2
        · apply Finset.mem_union_right
          simp only [S1, Finset.mem_filter]
          refine ⟨hedge, u, v, rfl, g, hglt, Or.inl ⟨hq, hB2, fun q' hq' => ?_⟩⟩
          exact (Finset.mem_filter.1 (hB_sub hq')).2
        · have hB3 : 3 ≤ (side (n := n) C g 1).card := by omega
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [SA, Finset.mem_filter]
          refine ⟨hedge, u, v, rfl, g, hglt, 1, hq, ?_, u, ?_⟩
          · have heq : side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u) = side (n := n) C g 1 :=
              Finset.inter_eq_left.2 hB_sub
            change 3 ≤ (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card
            rw [heq]; exact hB3
          · intro w hw
            exact Finset.mem_union_left _ (hB_sub hw)
    · rw [hpv] at hp; rw [hqu] at hq
      have hA_sub : side (n := n) C g 0 ⊆ Finset.univ.filter (G.Adj u) := by
        intro p' hp'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hgup : gateVal n C g (pairInput u p') = true := by
          rw [junk_gateVal_iff hAO hTF hNoCone hg (pairInput u p')]
          exact ⟨⟨p', hp', by simp [pairInput]⟩, ⟨u, hq, by simp [pairInput]⟩⟩
        obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hu hreach (pairInput u p') (by simp [pairInput]) hgup
        simp only [pairInput, decide_eq_true_eq] at hv1 hv2
        rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
        · exact False.elim (G.loopless.irrefl _ hadj')
        · exact hadj'
        · exact hadj'.symm
        · exact False.elim (G.loopless.irrefl _ hadj')
      have hApos : 0 < (side (n := n) C g 0).card := Finset.card_pos.2 ⟨v, hp⟩
      by_cases hA1 : (side (n := n) C g 0).card = 1
      · have hp0v : p0 = v := Finset.card_le_one.1 (le_of_eq hA1) p0 hp0 v hp
        have hvsp : v ∈ vSpecial (n := n) C g := by
          unfold vSpecial
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (by rw [if_pos hA1]; exact hp))
        by_cases hle2 : (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          simp only [SB, Finset.mem_filter]
          exact ⟨hedge, u, v, rfl, a, ha, b, g, hg, hvsp, hu, hle2, hreach⟩
        · push_neg at hle2
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [SA, Finset.mem_filter]
          refine ⟨hedge, v, u, Sym2.eq_swap, a, halt, b, hu, hle2, q0, ?_⟩
          intro w hw
          have := hside_sub hw
          rwa [hp0v] at this
      · by_cases hA2 : (side (n := n) C g 0).card = 2
        · apply Finset.mem_union_right
          simp only [S1, Finset.mem_filter]
          refine ⟨hedge, u, v, rfl, g, hglt, Or.inr (Or.inl ⟨hp, hA2, fun p' hp' => ?_⟩)⟩
          exact (Finset.mem_filter.1 (hA_sub hp')).2
        · have hA3 : 3 ≤ (side (n := n) C g 0).card := by omega
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [SA, Finset.mem_filter]
          refine ⟨hedge, u, v, rfl, g, hglt, 0, hp, ?_, u, ?_⟩
          · have heq : side (n := n) C g 0 ∩ Finset.univ.filter (G.Adj u) = side (n := n) C g 0 :=
              Finset.inter_eq_left.2 hA_sub
            change 3 ≤ (side (n := n) C g 0 ∩ Finset.univ.filter (G.Adj u)).card
            rw [heq]; exact hA3
          · intro w hw
            exact Finset.mem_union_left _ (hA_sub hw)
    · rw [hpv] at hp; rw [hqv] at hq
      have hvAB : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.2 ⟨hp, hq⟩
      have hAB_pos : 0 < (side (n := n) C g 0 ∩ side (n := n) C g 1).card := Finset.card_pos.2 ⟨v, hvAB⟩
      by_cases hAB1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1
      · have hvsp : v ∈ vSpecial (n := n) C g := by
          unfold vSpecial
          exact Finset.mem_union_right _ (by rw [if_pos hAB1]; exact hvAB)
        by_cases hle2 : (side C a b ∩ Finset.univ.filter (G.Adj v)).card ≤ 2
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          simp only [SB, Finset.mem_filter]
          exact ⟨hedge, u, v, rfl, a, ha, b, g, hg, hvsp, hu, hle2, hreach⟩
        · push_neg at hle2
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [SA, Finset.mem_filter]
          refine ⟨hedge, v, u, Sym2.eq_swap, a, halt, b, hu, hle2, v, ?_⟩
          intro w hw
          have hgv' : gateVal n C g (pairInput w v) = true := by
            rw [junk_gateVal_iff hAO hTF hNoCone hg (pairInput w v)]
            exact ⟨⟨v, hp, by simp [pairInput]⟩, ⟨v, hq, by simp [pairInput]⟩⟩
          obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hw hreach (pairInput w v) (by simp [pairInput]) hgv'
          simp only [pairInput, decide_eq_true_eq] at hv1 hv2
          apply Finset.mem_union_left
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
          · exact False.elim (G.loopless.irrefl _ hadj')
          · exact hadj'.symm
          · exact hadj'
          · exact False.elim (G.loopless.irrefl _ hadj')
      · have hAB2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card := by omega
        have hAB_adj : ∀ w ∈ side (n := n) C g 0 ∩ side (n := n) C g 1, G.Adj u w := by
          intro w hw
          have hgw : gateVal n C g (pairInput u w) = true := by
            rw [junk_gateVal_iff hAO hTF hNoCone hg (pairInput u w)]
            exact ⟨⟨w, (Finset.mem_inter.1 hw).1, by simp [pairInput]⟩,
              ⟨w, (Finset.mem_inter.1 hw).2, by simp [pairInput]⟩⟩
          obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hu hreach (pairInput u w) (by simp [pairInput]) hgw
          simp only [pairInput, decide_eq_true_eq] at hv1 hv2
          rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
          · exact False.elim (G.loopless.irrefl _ hadj')
          · exact hadj'
          · exact hadj'.symm
          · exact False.elim (G.loopless.irrefl _ hadj')
        by_cases hle2 : (side (n := n) C g 1 ∩ Finset.univ.filter (G.Adj u)).card ≤ 2
        · apply Finset.mem_union_right
          simp only [S1, Finset.mem_filter]
          exact ⟨hedge, u, v, rfl, g, hglt, Or.inr (Or.inr ⟨hvAB, hAB2, hle2, hAB_adj⟩)⟩
        · push_neg at hle2
          by_cases hAll : ∃ p' ∈ side (n := n) C g 0, ¬ G.Adj u p'
          · obtain ⟨p', hp', hna'⟩ := hAll
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            simp only [SA, Finset.mem_filter]
            refine ⟨hedge, u, v, rfl, g, hglt, 1, hq, hle2, p', fun q' hq' => ?_⟩
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases huq : G.Adj u q'
            · exact Or.inl huq
            · right
              let x : Fin n → Bool := fun z => decide (z = u ∨ z = p' ∨ z = q')
              have hxu : x u = true := by simp [x]
              have hxg : gateVal n C g x = true := by
                rw [junk_gateVal_iff hAO hTF hNoCone hg x]
                exact ⟨⟨p', hp', by simp [x]⟩, ⟨q', hq', by simp [x]⟩⟩
              obtain ⟨v1, v2, hadj', hv1, hv2⟩ := top_wmax hAO ha hu hreach x hxu hxg
              simp only [x, decide_eq_true_eq] at hv1 hv2
              rcases hv1 with rfl | rfl | rfl <;> rcases hv2 with rfl | rfl | rfl
              · exact False.elim (G.loopless.irrefl _ hadj')
              · exact False.elim (hna' hadj')
              · exact False.elim (huq hadj')
              · exact False.elim (hna' hadj'.symm)
              · exact False.elim (G.loopless.irrefl _ hadj')
              · exact hadj'
              · exact False.elim (huq hadj'.symm)
              · exact hadj'.symm
              · exact False.elim (G.loopless.irrefl _ hadj')
          · push_neg at hAll
            have hA_le : (side (n := n) C g 0 ∩ side (n := n) C g 1).card ≤ (side (n := n) C g 0).card :=
              Finset.card_le_card Finset.inter_subset_left
            by_cases hA2 : (side (n := n) C g 0).card = 2
            · apply Finset.mem_union_right
              simp only [S1, Finset.mem_filter]
              exact ⟨hedge, u, v, rfl, g, hglt, Or.inr (Or.inl ⟨hp, hA2, hAll⟩)⟩
            · have hA3 : 3 ≤ (side (n := n) C g 0).card := by omega
              have hA_sub : side (n := n) C g 0 ⊆ Finset.univ.filter (G.Adj u) := fun p' hp' =>
                Finset.mem_filter.2 ⟨Finset.mem_univ _, hAll p' hp'⟩
              apply Finset.mem_union_left
              apply Finset.mem_union_left
              simp only [SA, Finset.mem_filter]
              refine ⟨hedge, u, v, rfl, g, hglt, 0, hp, ?_, u, fun w hw => Finset.mem_union_left _ (hA_sub hw)⟩
              have heq : side (n := n) C g 0 ∩ Finset.univ.filter (G.Adj u) = side (n := n) C g 0 :=
                Finset.inter_eq_left.2 hA_sub
              change 3 ≤ (side (n := n) C g 0 ∩ Finset.univ.filter (G.Adj u)).card
              rw [heq]; exact hA3
  have hA : SA.card ≤ 8 * C.size := edge_bound_bucketA (C := C) h4 hAO
  have hB : SB.card ≤ 40 * C.size := edge_bound_bucketB (C := C) h4 hAO hTF hNoCone
  have h1 : S1.card ≤ 6 * C.size := edge_bound_type1_small (C := C) h4
  calc _ ≤ (SA ∪ SB ∪ S1).card := Finset.card_le_card hsub
    _ ≤ SA.card + SB.card + S1.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 8 * C.size + 40 * C.size + 6 * C.size := by omega
    _ ≤ 54 * (C.size + 1) := by omega

end PEqualNP.Outside.L_meta_3805

theorem PEqualNP.Outside.L_meta_3805 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x13 ∈ PEqualNP.TopForm.side x7 x15 x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 ((1 : Fin (2 : ℕ)) - x16)) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  exact ⟨54, fun _ G _ hgirth _ C hLeast hTF _ hNoCone =>
    PEqualNP.Outside.L_meta_3805.main_bound G hgirth C hLeast hTF hNoCone⟩
