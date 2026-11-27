import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One evaluation step: append the value of gate `g` read off the wires so far. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The wires produced by a list of gates from a starting wire list. -/
def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wf C.gates x := rfl

theorem wf_nil (w : List Bool) : wf [] w = w := rfl

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (step w g) := rfl

theorem wf_append (gs gs' : List Gate) (w : List Bool) :
    wf (gs ++ gs') w = wf gs' (wf gs w) := by
  simp [wf, List.foldl_append]

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem length_wf (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    rw [wf_cons, ih, length_step]
    simp; omega

theorem getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_wf_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [wf_cons, ih _ _ (by rw [length_step]; omega), getD_step_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- Lemma A: changing a wire that no gate reads commutes with evaluation. -/
theorem wf_set (k : ℕ) (b : Bool) (gs : List Gate) (hgs : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ w : List Bool, k < w.length → wf gs (w.set k b) = (wf gs w).set k b := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hk
    have hg : k ∉ g.inputs := hgs g (by simp)
    have hrest : ∀ g' ∈ gs, k ∉ g'.inputs := fun g' hg' => hgs g' (by simp [hg'])
    rw [wf_cons, wf_cons]
    have hmap : (g.inputs.map fun i => (w.set k b).getD i false)
        = (g.inputs.map fun i => w.getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hik : i ≠ k := fun h => hg (h ▸ hi)
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hik)]
    have hs : step (w.set k b) g = (step w g).set k b := by
      unfold step
      rw [hmap, List.set_append_left _ _ (by simpa using hk)]
    rw [hs, ih hrest _ (by rw [length_step]; omega)]

/-- The re-indexing of wire numbers once gate `L` (reading input `x2`) is removed. -/
def r (L x2 i : ℕ) : ℕ := if i < L then i else if i = L then x2 else i - 1

/-- Re-index the inputs of a gate. -/
def reidx (L x2 : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (r L x2)⟩

/-- Lemma B: the wire correspondence is preserved by evaluating gates that do not read `x2`. -/
theorem corr (L x2 : ℕ) (hx2 : x2 < L) (gs : List Gate) (hgs : ∀ g ∈ gs, x2 ∉ g.inputs) :
    ∀ A B : List Bool, A.length = B.length + 1 → L + 1 ≤ A.length →
      (∀ i, i ≠ x2 → A.getD i false = B.getD (r L x2 i) false) →
      ∀ i, i ≠ x2 → (wf gs A).getD i false
        = (wf (gs.map (reidx L x2)) B).getD (r L x2 i) false := by
  induction gs with
  | nil => intro A B _ _ hAB i hi; exact hAB i hi
  | cons g gs ih =>
    intro A B hlen hL hAB
    have hg : x2 ∉ g.inputs := hgs g (by simp)
    have hrest : ∀ g' ∈ gs, x2 ∉ g'.inputs := fun g' hg' => hgs g' (by simp [hg'])
    rw [List.map_cons]
    intro i hi
    rw [wf_cons, wf_cons]
    -- the two appended values agree
    have hval : g.op.eval (g.inputs.map fun j => A.getD j false)
        = (reidx L x2 g).op.eval ((reidx L x2 g).inputs.map fun j => B.getD j false) := by
      simp only [reidx, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj2 : j ≠ x2 := fun h => hg (h ▸ hj)
      simpa using hAB j hj2
    apply ih hrest
    · simp [step, hlen]
    · simp [step]; omega
    · intro i' hi'
      unfold step
      by_cases hlt : i' < A.length
      · have hrlt : r L x2 i' < B.length := by
          unfold r; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hlt, hAB i' hi', List.getD_append _ _ _ _ hrlt]
      · by_cases heq : i' = A.length
        · subst heq
          have hr : r L x2 A.length = B.length := by unfold r; split_ifs <;> omega
          rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact hval
        · have hgt : A.length < i' := by omega
          have hr : r L x2 i' = i' - 1 := by unfold r; split_ifs <;> omega
          rw [hr, getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · exact hi

/-- Splitting a gate list at the unique gate reading `x2`. -/
theorem split_unique (x2 : ℕ) : ∀ gs : List Gate, (gs.flatMap Gate.inputs).count x2 = 1 →
    ∃ pre g post, gs = pre ++ g :: post ∧ x2 ∈ g.inputs ∧ (∀ h ∈ pre, x2 ∉ h.inputs) ∧
      (∀ h ∈ post, x2 ∉ h.inputs) := by
  intro gs
  induction gs with
  | nil => intro h; simp at h
  | cons h t ih =>
    intro hc
    rw [List.flatMap_cons, List.count_append] at hc
    by_cases h0 : h.inputs.count x2 = 0
    · rw [h0, Nat.zero_add] at hc
      obtain ⟨pre, g, post, rfl, hg, hpre, hpost⟩ := ih hc
      refine ⟨h :: pre, g, post, rfl, hg, ?_, hpost⟩
      intro h' hh'
      rcases List.mem_cons.1 hh' with rfl | hh'
      · exact List.count_eq_zero.1 h0
      · exact hpre h' hh'
    · have h1 : (t.flatMap Gate.inputs).count x2 = 0 := by omega
      refine ⟨[], h, t, rfl, List.count_pos_iff.1 (Nat.pos_of_ne_zero h0), by simp, ?_⟩
      intro h' hh' hx
      have : x2 ∈ t.flatMap Gate.inputs := List.mem_flatMap.2 ⟨h', hh', hx⟩
      exact (List.count_eq_zero.1 h1) this

end PEqualNP.Outside.L_meta_2804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2804 in
theorem PEqualNP.Outside.L_meta_2804 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 < x1 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.output ≠ x2 → List.count x2 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (1 : ℕ) = x3.size ∧ x1 ≤ x9 ∧ x9 ≤ x1 + x8.size ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ x10.inputs.length ≤ (2 : ℕ) ∧ x2 ∈ x10.inputs ∧ (∀ x11 ∈ List.take (x9 - x1) x8.gates, x2 ∉ x11.inputs) ∧ ∀ (x11 : List Bool), x11.length = x1 → x3.eval x11 = x8.eval (x11.set x2 (x10.op.eval (List.map (fun (x13 : ℕ) => if x13 < x9 then (x8.wires x11).getD x13 Bool.false else Bool.false) x10.inputs))) := by
  intro x1 x2 x3 hx2 hfan hout hcount
  obtain ⟨pre, g, post, hgs, hg, hpre, hpost⟩ := split_unique x2 x3.gates hcount
  let L := x1 + pre.length
  have hgmem : g ∈ x3.gates := by rw [hgs]; simp
  have hfg := hfan g hgmem
  refine ⟨⟨pre ++ post.map (reidx L x2), r L x2 x3.output⟩, L, g, ?_, ?_, ?_, ?_, ?_, hfg.2, hg, ?_, ?_⟩
  · -- FanInTwo of the new circuit
    intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hfan h (by rw [hgs]; simp [hh])
    · obtain ⟨h0, hh0, rfl⟩ := List.mem_map.1 hh
      have := hfan h0 (by rw [hgs]; simp [hh0])
      exact ⟨this.1, by simpa [reidx] using this.2⟩
  · simp [Circuit.size, hgs]; omega
  · show x1 ≤ x1 + pre.length; omega
  · show x1 + pre.length ≤ x1 + (pre ++ post.map (reidx L x2)).length; simp
  · have h := hfg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  · intro h hh
    have : List.take (L - x1) (pre ++ post.map (reidx L x2)) = pre := by
      show List.take (x1 + pre.length - x1) _ = pre
      rw [Nat.add_sub_cancel_left, List.take_left]
    rw [this] at hh
    exact hpre h hh
  · intro x11 hlen
    -- the wires before the removed gate
    set P := wf pre x11 with hP
    have hPlen : P.length = L := by rw [hP, length_wf, hlen]
    have hx2P : x2 < P.length := by rw [hPlen]; omega
    -- the value substituted for input x2
    have hv : (g.op.eval (List.map (fun x13 => if x13 < L then
        ((⟨pre ++ post.map (reidx L x2), r L x2 x3.output⟩ : Circuit).wires x11).getD x13 false
        else false) g.inputs)) = g.op.eval (g.inputs.map fun i => P.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [wires_eq, wf_append, ← hP, getD_wf_lt _ _ _ (by rw [hPlen]; exact hi)]
      · rw [getD_ge _ _ (by rw [hPlen]; omega)]
    rw [hv]
    set v := g.op.eval (g.inputs.map fun i => P.getD i false) with hvdef
    -- evaluate both circuits
    simp only [Circuit.eval]
    rw [wires_eq, wires_eq, hgs, wf_append, wf_cons, ← hP, wf_append,
      wf_set x2 v pre hpre x11 (by rw [hlen]; exact hx2), ← hP]
    apply corr L x2 (by omega) post hpost
    · simp [step, hPlen]
    · simp [step, hPlen]
    · intro i hi
      unfold step
      by_cases hlt : i < L
      · have hr : r L x2 i = i := by unfold r; simp [hlt]
        rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPlen]; exact hlt),
          List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]
      · by_cases heq : i = L
        · subst heq
          have hr : r (x1 + pre.length) x2 (x1 + pre.length) = x2 := by unfold r; simp
          rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hPlen]),
            List.getD_eq_getElem?_getD, List.getElem?_set_self hx2P]
          simp [hPlen, hvdef]
        · have hr : r L x2 i = i - 1 := by unfold r; split_ifs <;> omega
          rw [hr, getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · exact hout
