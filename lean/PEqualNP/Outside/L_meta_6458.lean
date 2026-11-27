import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6458

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton l a ih => rw [W_snoc]; simp [ih]; omega

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem getD_left (l : List Bool) (v : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_last (l : List Bool) (v : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [v]).getD i false = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

theorem key (x1 : ℕ) (init : List Gate) (g0 : Gate) (o a b : ℕ) (hb : b < init.length)
    (ha : a ≤ b)
    (hm : PEqualNP.MetaComplexity.Monotone2 ⟨init ++ [g0], o⟩)
    (hr : ∀ (x6 : Fin (init ++ [g0]).length), ∀ x7 ∈ ((init ++ [g0]).get x6).inputs,
      x7 ≤ x1 + ↑x6) :
    ∃ (x8 : Circuit), x8.size = init.length + 1 ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧
      (∀ (x9 : Fin x8.gates.length), ∀ x10 ∈ (x8.gates.get x9).inputs, x10 ≤ x1 + ↑x9) ∧
      ∀ (x9 : List Bool), x9.length = x1 →
        ((x8.wires x9).getD (x1 + a) Bool.false &&
          (x8.wires x9).getD (x1 + (x8.size - (1 : ℕ))) Bool.false) =
        (((⟨init ++ [g0], o⟩ : Circuit).wires x9).getD (x1 + a) Bool.false &&
          ((⟨init ++ [g0], o⟩ : Circuit).wires x9).getD (x1 + b) Bool.false) := by
  refine ⟨⟨init ++ [⟨GateOp.or, [x1 + b]⟩], o⟩, by simp [Circuit.size], ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hm g (by simp [hg])
    · simp
  · rintro ⟨i, hi⟩ x7 h7
    simp only [List.get_eq_getElem] at h7
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i < init.length
    · rw [List.getElem_append_left h] at h7
      have := hr ⟨i, by simp; omega⟩ x7 (by
        simp only [List.get_eq_getElem]; rw [List.getElem_append_left h]; exact h7)
      exact this
    · have hi2 : i = init.length := by omega
      subst hi2
      simp at h7
      subst h7
      simp; omega
  · intro x hx
    have hl : (W init x).length = x1 + init.length := by rw [W_length, hx]
    simp only [wires_eq, Circuit.size, W_snoc, List.length_append, List.length_singleton,
      Nat.add_sub_cancel]
    rw [getD_left _ _ (x1 + a) (by omega), getD_last _ _ (x1 + init.length) (by omega),
      getD_left _ _ (x1 + a) (by omega), getD_left _ _ (x1 + b) (by omega)]
    simp [GateOp.eval]

end PEqualNP.Outside.L_meta_6458

theorem PEqualNP.Outside.L_meta_6458 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x2.size), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : Fin x2.gates.length), ∀ x7 ∈ (x2.gates.get x6).inputs, x7 ≤ x1 + ↑x6) → x3 ≤ x4 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size = x2.size ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x8.gates.length), ∀ x10 ∈ (x8.gates.get x9).inputs, x10 ≤ x1 + ↑x9) ∧ ∀ (x9 : List Bool), x9.length = x1 → ((x8.wires x9).getD (x1 + ↑x3) Bool.false && (x8.wires x9).getD (x1 + (x8.size - (1 : ℕ))) Bool.false) = ((x2.wires x9).getD (x1 + ↑x3) Bool.false && (x2.wires x9).getD (x1 + ↑x4) Bool.false) := by
  intro x1 x2 x3 x4 hm hr h34
  by_cases h : (x4 : ℕ) = x2.size - 1
  · exact ⟨x2, rfl, hm, hr, fun x9 _ => by rw [h]⟩
  · obtain ⟨gates, o⟩ := x2
    have h4 := x4.isLt
    have h3 : (x3 : ℕ) ≤ x4 := h34
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at h h4
    rcases List.eq_nil_or_concat gates with hg | ⟨init, g0, hg⟩
    · subst hg; simp at h4
    · rw [List.concat_eq_append] at hg
      subst hg
      simp only [List.length_append, List.length_singleton] at h h4
      have := PEqualNP.Outside.L_meta_6458.key x1 init g0 o x3 x4 (by omega) h3
        (by simpa using hm) (by simpa using hr)
      simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using this
