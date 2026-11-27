import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3006_aux

open PEqualNP.CircuitLowerBounds

theorem getD_map (L : List ℕ) (x7 a : ℕ) (ha : a < L.length) :
    (L.map fun x8 : ℕ => x8.testBit x7).getD a false = L[a].testBit x7 := by
  simp [List.getD_eq_getElem?_getD, ha]

theorem key (x1 x2 : List ℕ)
    (h : ∀ (x4 : Fin x2.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2,
      x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) :
    ∀ n : ℕ, n ≤ x2.length → ∃ gs : List Gate, gs.length = n ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ x7 : ℕ, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (x1.map fun x8 : ℕ => x8.testBit x7) = (x1 ++ x2.take n).map (fun x8 : ℕ => x8.testBit x7) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨gs, hl, hm, hf⟩ := ih (by omega)
    obtain ⟨x5, h5, x6, h6, hor⟩ := h ⟨n, hn⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp h5
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp h6
    have ht : x2.take (n + 1) = x2.take n ++ [x2[n]] := by simp
    simp only [List.get_eq_getElem] at hor
    rcases hor with hor | hor
    · refine ⟨gs ++ [⟨GateOp.and, [a, b]⟩], by simp [hl], ?_, ?_⟩
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hm g hg
        · simp at hg
          subst hg
          simp
      · intro x7
        rw [List.foldl_append, hf x7, ht]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← List.append_assoc, List.map_append (l₂ := [x2[n]])]
        congr 1
        simp only [List.map_cons, List.map_nil, GateOp.eval, getD_map _ _ _ ha, getD_map _ _ _ hb,
          hor, Nat.testBit_land]
        simp
    · refine ⟨gs ++ [⟨GateOp.or, [a, b]⟩], by simp [hl], ?_, ?_⟩
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hm g hg
        · simp at hg
          subst hg
          simp
      · intro x7
        rw [List.foldl_append, hf x7, ht]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← List.append_assoc, List.map_append (l₂ := [x2[n]])]
        congr 1
        simp only [List.map_cons, List.map_nil, GateOp.eval, getD_map _ _ _ ha, getD_map _ _ _ hb,
          hor, Nat.testBit_lor]
        simp

end PEqualNP.Outside.L_meta_3006_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3006_aux in
theorem PEqualNP.Outside.L_meta_3006 : ∀ (x1 x2 : List ℕ) (x3 : ℕ), (∀ (x4 : Fin x2.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2, x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) → x3 ∈ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x2.length ∧ ∀ (x7 : ℕ), x6.eval (List.map (fun (x8 : ℕ) => x8.testBit x7) x1) = x3.testBit x7 := by
  intro x1 x2 x3 h h3
  obtain ⟨gs, hl, hm, hf⟩ := key x1 x2 h x2.length le_rfl
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h3
  refine ⟨⟨gs, x1.length + k⟩, hm, by simp [Circuit.size, hl], ?_⟩
  intro x7
  unfold Circuit.eval Circuit.wires
  simp only []
  rw [hf x7, List.take_length, getD_map _ _ _ (by simp; omega)]
  simp
