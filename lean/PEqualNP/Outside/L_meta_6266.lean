import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem coneS (n : ℕ) (gs : List Gate) :
    (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] →
      (∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧ (d = w - n ∨
        d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (EdgeOwnership.coneStep n) [] with hr
    have hold : ∀ i, i < gs.length → (EdgeOwnership.coneStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [EdgeOwnership.coneStep, h1], fun j hj d hd => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt] at hd
      rw [List.getElem_append_left hlt]
      obtain ⟨w, q1, q2, q3, q4⟩ := h2 j hlt d hd
      exact ⟨w, q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (EdgeOwnership.coneStep n r g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => (w - n) :: r.getD (w - n) []) := by
        rw [← h1]
        exact getD_at' _ _ _
      rw [e2, List.mem_flatMap] at hd
      obtain ⟨w, hw, hd⟩ := hd
      simp only [List.mem_filter, decide_eq_true_eq, h1] at hw
      refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
      rw [hold _ (by omega)]
      exact List.mem_cons.1 hd

theorem cone_rd (n : ℕ) (C : Circuit) : ∀ j d, EdgeOwnership.InCone n C d j →
    j < C.gates.length ∧ d < j ∧ ∃ r < C.gates.length, n + d ∈ (gateAt C r).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro d hd
    obtain ⟨h1, h2⟩ := coneS n C.gates
    by_cases hj : j < C.gates.length
    · obtain ⟨w, q1, q2, q3, q4⟩ := h2 j hj d hd
      rcases q4 with q4 | q4
      · refine ⟨hj, by omega, j, hj, ?_⟩
        have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
        rw [e, q4, show n + (w - n) = w by omega]; exact q1
      · obtain ⟨_, t1, t2⟩ := ih (w - n) (by omega) d q4
        exact ⟨hj, by omega, t2⟩
    · unfold EdgeOwnership.InCone at hd
      rw [List.getD_eq_default _ _ (by unfold EdgeOwnership.cones; omega)] at hd
      simp at hd

theorem coneI (n : ℕ) (gs : List Gate) :
    (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] ↔
      (∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧ (d = w - n ∨
        d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (EdgeOwnership.coneStep n) [] with hr
    have hold : ∀ i, i < gs.length → (EdgeOwnership.coneStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [EdgeOwnership.coneStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun hw => ?_
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (EdgeOwnership.coneStep n r g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => (w - n) :: r.getD (w - n) []) := by
        rw [← h1]
        exact getD_at' _ _ _
      rw [e2, List.mem_flatMap]
      simp only [List.mem_filter, decide_eq_true_eq, h1, List.mem_cons]
      refine exists_congr fun w => ?_
      constructor
      · rintro ⟨⟨q1, q2, q3⟩, q4⟩
        exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
      · rintro ⟨q1, q2, q3, q4⟩
        rw [hold _ (by omega)] at q4
        exact ⟨⟨q1, q2, q3⟩, q4⟩

theorem cone_trans (n : ℕ) (C : Circuit) : ∀ j, j < C.gates.length → ∀ r i,
    EdgeOwnership.InCone n C r j → EdgeOwnership.InCone n C i r →
    EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj r i hr hi
    obtain ⟨w, q1, q2, q3, q4⟩ := (((coneI n C.gates).2 j hj r)).1 hr
    refine (((coneI n C.gates).2 j hj i)).2 ⟨w, q1, q2, q3, Or.inr ?_⟩
    rcases q4 with rfl | q4
    · exact hi
    · exact ih (w - n) (by omega) (by omega) r i q4 hi


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6266

theorem PEqualNP.Outside.L_meta_6266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), (∃ (x4 : ℕ), PEqualNP.EdgeOwnership.InCone x1 x2 x4 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x5 < x3, PEqualNP.EdgeOwnership.InCone x1 x2 x5 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ (x6 : ℕ), PEqualNP.EdgeOwnership.InCone x1 x2 x6 x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ x6 < x5, ¬(PEqualNP.EdgeOwnership.InCone x1 x2 x6 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and) := by
  classical
  intro n C x3 hex
  obtain ⟨hc, ho⟩ := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ (PEqualNP.EdgeOwnership.InCone n C m x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and) :=
    fun m hm => Nat.find_min hex hm
  obtain ⟨hl, hlt, _⟩ := PEqualNP.Outside.L_meta_6266.cone_rd n C _ _ hc
  refine ⟨Nat.find hex, hlt, hc, ho, ?_, hmin⟩
  intro y hy hand
  have hylt := (PEqualNP.Outside.L_meta_6266.cone_rd n C _ _ hy).2.1
  exact hmin y hylt ⟨PEqualNP.Outside.L_meta_6266.cone_trans n C x3 hl _ _ hc hy, hand⟩
