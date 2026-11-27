import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7802

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CleanedNonEdge

def orun (n : ℕ) (gs : List Gate) : List (List ℕ) := gs.foldl (orStep n) []

lemma orun_append (n : ℕ) (gs : List Gate) (a : Gate) :
    orun n (gs ++ [a]) = orStep n (orun n gs) a := by
  simp [orun, List.foldl_append]

lemma orun_length (n : ℕ) (gs : List Gate) : (orun n gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [orun]
  | append_singleton gs a ih => rw [orun_append]; simp [orStep, ih]

lemma pre (n : ℕ) (gs : List Gate) (a : Gate) (i : ℕ) (h : i < gs.length) :
    (orun n (gs ++ [a])).getD i [] = (orun n gs).getD i [] := by
  rw [orun_append]
  unfold orStep
  exact List.getD_append _ _ _ _ (by rw [orun_length]; exact h)

lemma getD_top {α : Type} (l : List α) (x d : α) : (l ++ [x]).getD l.length d = x := by
  simp

lemma step_mem (n : ℕ) (cs : List (List ℕ)) (a : Gate) (g : ℕ) :
    g ∈ (orStep n cs a).getD cs.length [] ↔ g = cs.length ∨ (a.op = GateOp.or ∧
      ∃ w ∈ a.inputs, n ≤ w ∧ w < n + cs.length ∧ g ∈ cs.getD (w - n) []) := by
  unfold orStep
  rw [getD_top, List.mem_cons]
  split_ifs with hop
  · rw [List.mem_flatMap]
    constructor
    · rintro (h | ⟨w, hw, hg⟩)
      · exact Or.inl h
      · rw [List.mem_filter, decide_eq_true_eq] at hw
        exact Or.inr ⟨hop, w, hw.1, hw.2.1, hw.2.2, hg⟩
    · rintro (h | ⟨_, w, hw, h1, h2, hg⟩)
      · exact Or.inl h
      · refine Or.inr ⟨w, ?_, hg⟩
        rw [List.mem_filter, decide_eq_true_eq]
        exact ⟨hw, h1, h2⟩
  · constructor
    · rintro (h | h)
      · exact Or.inl h
      · simp at h
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h hop

lemma top_mem (n : ℕ) (gs : List Gate) (a : Gate) (g : ℕ) :
    g ∈ (orun n (gs ++ [a])).getD gs.length [] ↔ g = gs.length ∨ (a.op = GateOp.or ∧
      ∃ w ∈ a.inputs, n ≤ w ∧ w < n + gs.length ∧ g ∈ (orun n gs).getD (w - n) []) := by
  rw [orun_append]
  have := step_mem n (orun n gs) a g
  rw [orun_length] at this
  exact this

lemma sets_iff (n : ℕ) (d : Gate) (gs : List Gate) : ∀ k g : ℕ,
    g ∈ (orun n gs).getD k [] ↔ k < gs.length ∧ (g = k ∨ ((gs.getD k d).op = GateOp.or ∧
      ∃ w ∈ (gs.getD k d).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orun n gs).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g; simp [orun]
  | append_singleton gs a ih =>
    intro k g
    rcases Nat.lt_trichotomy k gs.length with hlt | heq | hgt
    · have e : (gs ++ [a]).getD k d = gs.getD k d := List.getD_append _ _ _ _ hlt
      rw [pre n gs a k hlt, ih k g, e]
      constructor
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact ⟨by simp; omega, Or.inl h⟩
        · exact ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)]; exact hg⟩⟩
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact ⟨hlt, Or.inl h⟩
        · exact ⟨hlt, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)] at hg; exact hg⟩⟩
    · subst heq
      have e : (gs ++ [a]).getD gs.length d = a := by simp
      rw [top_mem, e]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, hg⟩)
        · exact ⟨by simp, Or.inl h⟩
        · exact ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)]; exact hg⟩⟩
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)] at hg; exact hg⟩
    · constructor
      · intro h
        rw [List.getD_eq_default _ _ (by rw [orun_length]; simp; omega)] at h
        simp at h
      · rintro ⟨h, _⟩
        simp at h
        omega


def R (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => ∃ (x8 : ℕ), x6 = n + x8 ∧ x8 < C.gates.length ∧ (NestedCover.gateAt C x8).op = GateOp.or ∧ x7 ∈ (NestedCover.gateAt C x8).inputs

lemma reach_iff (n : ℕ) (C : Circuit) (w g : ℕ) :
    OrReaches n C w g ↔ n ≤ w ∧ w - n < C.gates.length ∧ (g = w - n ∨
      ((NestedCover.gateAt C (w - n)).op = GateOp.or ∧
      ∃ w' ∈ (NestedCover.gateAt C (w - n)).inputs, n ≤ w' ∧ w' < n + (w - n) ∧
        OrReaches n C w' g)) := by
  unfold OrReaches
  have := sets_iff n ⟨GateOp.or, []⟩ C.gates (w - n) g
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, b⟩ := this.mp h2
    refine ⟨h1, a, ?_⟩
    rcases b with b | ⟨hop, w', hw', c1, c2, c3⟩
    · exact Or.inl b
    · exact Or.inr ⟨hop, w', hw', c1, c2, c1, c3⟩
  · rintro ⟨h1, a, b⟩
    refine ⟨h1, this.mpr ⟨a, ?_⟩⟩
    rcases b with b | ⟨hop, w', hw', c1, c2, _, c3⟩
    · exact Or.inl b
    · exact Or.inr ⟨hop, w', hw', c1, c2, c3⟩

lemma fwd (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g →
    g < C.gates.length ∧ Relation.ReflTransGen (R n C) w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, a, b | ⟨hop, w', hw', c1, c2, c3⟩⟩ := (reach_iff n C w g).mp h
    · subst b
      refine ⟨a, ?_⟩
      have : n + (w - n) = w := by omega
      rw [this]
    · obtain ⟨i1, i2⟩ := ih w' (by omega) c3
      exact ⟨i1, Relation.ReflTransGen.head ⟨w - n, by omega, a, hop, hw'⟩ i2⟩

lemma bwd (n : ℕ) (C : Circuit)
    (hC : ∀ x3 < C.gates.length, ∀ i ∈ (NestedCover.gateAt C x3).inputs, i < n + x3)
    (g : ℕ) (hg : g < C.gates.length) (w : ℕ)
    (h : Relation.ReflTransGen (R n C) w (n + g)) : OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine (reach_iff n C (n + g) g).mpr ⟨by omega, ?_, Or.inl (by omega)⟩
    have : n + g - n = g := by omega
    rw [this]; exact hg
  | head hab _ ih =>
    obtain ⟨x8, rfl, hlt, hop, hin⟩ := hab
    have e : n + x8 - n = x8 := by omega
    refine (reach_iff n C (n + x8) g).mpr ⟨by omega, by rw [e]; exact hlt, Or.inr ?_⟩
    rw [e]
    exact ⟨hop, _, hin, ((reach_iff n C _ g).mp ih).1, hC x8 hlt _ hin, ih⟩

end PEqualNP.Outside.L_meta_7802

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_7802 in
theorem PEqualNP.Outside.L_meta_7802 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x3 < x2.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs = [x5, x6] ∧ x5 < x1 + x3 ∧ x6 < x1 + x3) → ∀ (x4 : ℕ) (x5 : Fin x1), x5 ∈ PEqualNP.TopForm.orIn x1 x2 x4 ↔ Relation.ReflTransGen (fun (x6 x7 : ℕ) => ∃ (x8 : ℕ), x6 = x1 + x8 ∧ x8 < x2.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs) x4 ↑x5 := by
  intro x1 x2 hyp x4 x5
  have hC : ∀ x3 < x2.gates.length, ∀ i ∈ (NestedCover.gateAt x2 x3).inputs, i < x1 + x3 := by
    intro x3 h3 i hi
    obtain ⟨_, a, b, e, ha, hb⟩ := hyp x3 h3
    rw [e] at hi
    simp at hi
    rcases hi with rfl | rfl <;> assumption
  change _ ↔ Relation.ReflTransGen (R x1 x2) x4 x5
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter]
  constructor
  · rintro ⟨_, h | ⟨k, hk, hr, hop, hin⟩⟩
    · rw [h]
    · exact Relation.ReflTransGen.tail (fwd x1 x2 k x4 hr).2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, hb, k, rfl, hk, hop, hin⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk, bwd x1 x2 hC k hk x4 hb, hop, hin⟩
