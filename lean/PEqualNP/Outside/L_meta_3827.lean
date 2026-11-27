import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3827

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def evalG (g : Gate) (u : List Bool) : Bool := g.op.eval (g.inputs.map fun i => u.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [evalG g w]

theorem step_eq (u : List Bool) (g : Gate) : step u g = u ++ [evalG g u] := rfl

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem length_foldl : ∀ (l : List Gate) (u : List Bool),
    (l.foldl step u).length = u.length + l.length := by
  intro l
  induction l with
  | nil => intro u; simp
  | cons g l ih => intro u; simp [ih, step]; omega

theorem getD_foldl_lt : ∀ (l : List Gate) (u : List Bool) (i : ℕ), i < u.length →
    (l.foldl step u).getD i false = u.getD i false := by
  intro l
  induction l with
  | nil => intro u i _; rfl
  | cons g l ih =>
    intro u i hi
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def R (u u' : List Bool) : Prop :=
  u.length = u'.length ∧ (∀ i, i ≠ 0 → u'.getD i false = u.getD i false) ∧
    u'.getD 0 false = !(u.getD 0 false)

theorem R_pos {u u' : List Bool} (h : R u u') : 0 < u.length := by
  rcases Nat.eq_zero_or_pos u.length with h0 | h0
  · exfalso
    have h1 : u'.length = 0 := by rw [← h.1]; exact h0
    have := h.2.2
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)] at this
    simp at this
  · exact h0

theorem R_app {u u' : List Bool} (h : R u u') (v : Bool) : R (u ++ [v]) (u' ++ [v]) := by
  have hp := R_pos h
  obtain ⟨hl, ha, h0⟩ := h
  refine ⟨by simp [hl], ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_or_ge i u.length with h1 | h1
    · rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ (by omega)]
      exact ha i hi
    · rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ (by omega), hl]
  · rw [List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ (by omega)]
    exact h0

theorem evalG_noZero (g : Gate) (hg : (0 : ℕ) ∉ g.inputs) {u u' : List Bool} (h : R u u') :
    evalG g u' = evalG g u := by
  unfold evalG
  congr 1
  apply List.map_congr_left
  intro i hi
  apply h.2.1
  rintro rfl
  exact hg hi

theorem sim0 : ∀ (l : List Gate), (∀ g ∈ l, (0 : ℕ) ∉ g.inputs) →
    ∀ (u u' : List Bool), R u u' → R (l.foldl step u) (l.foldl step u') := by
  intro l
  induction l with
  | nil => intro _ u u' h; exact h
  | cons g l ih =>
    intro hl u u' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
    unfold step
    rw [evalG_noZero g (hl g (List.mem_cons_self)) h]
    exact R_app h _

theorem split : ∀ (l : List Gate),
    (l.filter (fun g => g.inputs.contains (0 : ℕ))).length ≤ 1 →
    (∀ g ∈ l, (0 : ℕ) ∉ g.inputs) ∨ ∃ pre g post, l = pre ++ g :: post ∧ (0 : ℕ) ∈ g.inputs ∧
      (∀ h ∈ pre, (0 : ℕ) ∉ h.inputs) ∧ ∀ h ∈ post, (0 : ℕ) ∉ h.inputs := by
  intro l
  induction l with
  | nil => intro _; left; simp
  | cons a l ih =>
    intro hl
    by_cases ha : (0 : ℕ) ∈ a.inputs
    · right
      have hc : a.inputs.contains 0 = true := List.contains_iff_mem.mpr ha
      simp only [List.filter_cons, hc, ite_true, List.length_cons] at hl
      have h0 : (l.filter (fun g => g.inputs.contains (0 : ℕ))).length = 0 := by omega
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
      refine ⟨[], a, l, rfl, ha, by simp, ?_⟩
      intro h hh h0'
      exact h0 h hh (List.contains_iff_mem.mpr h0')
    · have hc : ¬ a.inputs.contains 0 = true := fun h => ha (List.contains_iff_mem.mp h)
      simp only [List.filter_cons, hc, Bool.false_eq_true, ite_false] at hl
      rcases ih hl with h1 | ⟨pre, g, post, h1, h2, h3, h4⟩
      · left
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ha
        · exact h1 g hg
      · right
        refine ⟨a :: pre, g, post, by simp [h1], h2, ?_, h4⟩
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · exact ha
        · exact h3 h hh

theorem R_input (x : Fin 9 → Bool) :
    R (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i) (List.ofFn x) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      List.getElem?_ofFn]
    by_cases h1 : i < 9
    · have : (⟨i, h1⟩ : Fin 9) ≠ 0 := by
        intro h; apply hi; exact congrArg Fin.val h
      simp [h1, this]
    · simp [h1]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      List.getElem?_ofFn]
    simp

theorem gateCase (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (h0 : (0 : ℕ) ∈ g.inputs) (n : ℕ) :
    (∃ a, 0 < a ∧ a < n ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [0, a] ∨ g.inputs = [a, 0])) ∨
    ∃ g' : Gate, (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g'.inputs.length ≤ 2) ∧
      ∀ u u', R u u' → u.length = n → evalG g' u' = evalG g u := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen h0 ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at h0
  · have ha : a = 0 := by simp at h0; omega
    subst ha
    right
    rcases hop with rfl | rfl | rfl
    · refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
      intro u u' hR hn
      obtain ⟨-, h1, h2⟩ := hR
      simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
      simp [evalG, GateOp.eval, h2]
    · refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
      intro u u' hR hn
      obtain ⟨-, h1, h2⟩ := hR
      simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
      simp [evalG, GateOp.eval, h2]
    · refine ⟨⟨GateOp.and, [0]⟩, by simp, ?_⟩
      intro u u' hR hn
      obtain ⟨-, h1, h2⟩ := hR
      simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
      simp [evalG, GateOp.eval, h2]
  · by_cases ha : a = 0
    · subst ha
      rcases hop with rfl | rfl | rfl
      · by_cases hb : b = 0
        · subst hb
          right
          refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
          intro u u' hR hn
          obtain ⟨-, h1, h2⟩ := hR
          simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
          simp [evalG, GateOp.eval, h2]
        · by_cases hbn : b < n
          · left
            exact ⟨b, Nat.pos_of_ne_zero hb, hbn, by simp, by simp⟩
          · right
            refine ⟨⟨GateOp.or, []⟩, by simp, ?_⟩
            intro u u' hR hn
            obtain ⟨-, h1, h2⟩ := hR
            have h3 : u.getD b false = false := List.getD_eq_default _ _ (by omega)
            simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
            simp [evalG, GateOp.eval, h3]
      · by_cases hb : b = 0
        · subst hb
          right
          refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
          intro u u' hR hn
          obtain ⟨-, h1, h2⟩ := hR
          simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
          simp [evalG, GateOp.eval, h2]
        · by_cases hbn : b < n
          · left
            exact ⟨b, Nat.pos_of_ne_zero hb, hbn, by simp, by simp⟩
          · right
            refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
            intro u u' hR hn
            obtain ⟨-, h1, h2⟩ := hR
            have h3 : u.getD b false = false := List.getD_eq_default _ _ (by omega)
            simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
            simp [evalG, GateOp.eval, h2, h3]
      · right
        refine ⟨⟨GateOp.and, [0]⟩, by simp, ?_⟩
        intro u u' hR hn
        obtain ⟨-, h1, h2⟩ := hR
        simp only [List.getD_eq_getElem?_getD] at h1 h2 ⊢
        simp [evalG, GateOp.eval, h2]
    · have hb : b = 0 := by
        simp at h0
        omega
      subst hb
      rcases hop with rfl | rfl | rfl
      · by_cases han : a < n
        · left
          exact ⟨a, Nat.pos_of_ne_zero ha, han, by simp, by simp⟩
        · right
          refine ⟨⟨GateOp.or, []⟩, by simp, ?_⟩
          intro u u' hR hn
          obtain ⟨-, h1, h2⟩ := hR
          have h3 : u.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
          simp [evalG, GateOp.eval, h3]
      · by_cases han : a < n
        · left
          exact ⟨a, Nat.pos_of_ne_zero ha, han, by simp, by simp⟩
        · right
          refine ⟨⟨GateOp.not, [0]⟩, by simp, ?_⟩
          intro u u' hR hn
          obtain ⟨-, h1, h2⟩ := hR
          have h3 : u.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
          simp [evalG, GateOp.eval, h2, h3]
      · right
        refine ⟨⟨GateOp.not, [a, 0]⟩, by simp, ?_⟩
        intro u u' hR hn
        obtain ⟨-, h1, h2⟩ := hR
        have h3 := h1 a ha
        simp only [List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
        simp [evalG, GateOp.eval, h2, h3]
  · simp at hlen

theorem notCircuit (x : Fin 9 → Bool) :
    circuitFun 9 ⟨[⟨GateOp.not, [0]⟩], 9⟩ x = !x 0 := by
  simp [circuitFun, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
    ]

theorem fan_mid (pre post : List Gate) (g g' : Gate)
    (hC : FanInTwo ⟨pre ++ g :: post, 0⟩)
    (hg' : g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2)
    (o : ℕ) : FanInTwo ⟨pre ++ g' :: post, o⟩ := by
  intro h hh
  simp only [List.mem_append, List.mem_cons] at hh
  rcases hh with hh | rfl | hh
  · exact hC h (by simp [hh])
  · exact hg'
  · exact hC h (by simp [hh])

end PEqualNP.Outside.L_meta_3827

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3827 in
theorem PEqualNP.Outside.L_meta_3827 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : (Fin (9 : ℕ) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) = x3 x7) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (14 : ℕ) ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 x9 = x3 x9) ∨ ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (14 : ℕ) ∧ (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.inputs.contains (0 : ℕ)) x8.gates).length = (1 : ℕ) ∧ x9 < x8.gates.length ∧ (0 : ℕ) < x10 ∧ x10 < (9 : ℕ) + x9 ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).inputs = [(0 : ℕ), x10] ∧ ∀ (x11 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 fun (x12 : Fin (9 : ℕ)) => if x12 = (0 : Fin (9 : ℕ)) then !x11 (0 : Fin (9 : ℕ)) else x11 x12) = x3 x11 := by
  intro C b F hfan hsize hfilt hF
  cases b with
  | false =>
    left
    refine ⟨C, hfan, hsize, fun x => ?_⟩
    rw [← hF x]
    congr 1
    funext i
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  | true =>
    have hF' : ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i) = F x := by
      intro x
      have := hF x
      simp only [Bool.true_bne] at this
      exact this
    obtain ⟨gs, o⟩ := C
    simp only [Circuit.size] at hsize
    simp only at hfilt
    by_cases hout : o = 0
    · subst hout
      left
      refine ⟨⟨[⟨GateOp.not, [0]⟩], 9⟩, ?_, by simp [Circuit.size], ?_⟩
      · intro g hg
        simp at hg
        subst hg
        simp
      · intro x
        rw [notCircuit, ← hF' x]
        simp only [Circuit.eval]
        rw [wires_eq, getD_foldl_lt _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
    · rcases split gs hfilt with hno | ⟨pre, g, post, hgs, hg0, hpre, hpost⟩
      · left
        refine ⟨⟨gs, o⟩, hfan, hsize, fun x => ?_⟩
        rw [← hF' x]
        have hR := sim0 gs hno _ _ (R_input x)
        simp only [circuitFun, Circuit.eval, wires_eq]
        exact hR.2.1 o hout
      · subst hgs
        have hgf := hfan g (by simp)
        have hfan0 : FanInTwo ⟨pre ++ g :: post, 0⟩ := hfan
        rcases gateCase g hgf.1 hgf.2 hg0 (9 + pre.length) with
          ⟨a, ha0, han, hop, hins⟩ | ⟨g', hg'f, hg'⟩
        · right
          have hev : ∀ u, evalG ⟨g.op, [0, a]⟩ u = evalG g u := by
            intro u
            rcases hins with h | h
            · simp [evalG, h]
            · rcases hop with h' | h'
              · simp [evalG, h, h', GateOp.eval, Bool.and_comm]
              · simp [evalG, h, h', GateOp.eval, Bool.or_comm]
          refine ⟨⟨pre ++ ⟨g.op, [0, a]⟩ :: post, o⟩, pre.length, a,
            fan_mid pre post g ⟨g.op, [0, a]⟩ hfan0 ⟨hgf.1, by simp⟩ o, by simpa [Circuit.size] using hsize,
            ?_, by simp, ha0, han, ?_, ?_, ?_⟩
          · have h1 : ∀ h ∈ pre, ¬ h.inputs.contains 0 = true :=
              fun h hh hc => hpre h hh (List.contains_iff_mem.mp hc)
            have h2 : ∀ h ∈ post, ¬ h.inputs.contains 0 = true :=
              fun h hh hc => hpost h hh (List.contains_iff_mem.mp hc)
            rw [List.filter_append, List.filter_eq_nil_iff.mpr h1, List.filter_cons,
              List.filter_eq_nil_iff.mpr h2]
            simp
          · simp only [NestedCover.gateAt]
            rw [List.getD_append_right _ _ _ _ le_rfl]
            simpa using hop
          · simp only [NestedCover.gateAt]
            rw [List.getD_append_right _ _ _ _ le_rfl]
            simp
          · intro x
            rw [← hF' x]
            simp only [circuitFun, Circuit.eval, wires_eq, List.foldl_append, List.foldl_cons]
            simp only [step_eq, hev]
        · left
          refine ⟨⟨pre ++ g' :: post, o⟩, fan_mid pre post g g' hfan0 hg'f o,
            by simpa [Circuit.size] using hsize, fun x => ?_⟩
          rw [← hF' x]
          simp only [circuitFun, Circuit.eval, wires_eq, List.foldl_append, List.foldl_cons]
          have hR1 := sim0 pre hpre _ _ (R_input x)
          have hl : (pre.foldl step
              (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).length = 9 + pre.length := by
            rw [length_foldl]; simp
          have hR2 : R (step (pre.foldl step
              (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)) g)
              (step (pre.foldl step (List.ofFn x)) g') := by
            rw [step_eq, step_eq, hg' _ _ hR1 hl]
            exact R_app hR1 _
          exact (sim0 post hpost _ _ hR2).2.1 o hout
