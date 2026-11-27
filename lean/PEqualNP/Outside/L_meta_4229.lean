import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4229_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def phi (n w : ℕ) : ℕ := if w < n then w else w + 2

def rho (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi n)⟩

lemma key (n : ℕ) (x T : List Bool) (hx : x.length = n) (a b : Bool) (i : ℕ) :
    (x ++ [a, b] ++ T).getD (phi n i) false = (x ++ T).getD i false := by
  subst hx
  unfold phi
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < x.length
  · rw [if_pos h, List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [if_neg h]
    have h1 : (x ++ [a, b] ++ T)[i + 2]? = T[i - x.length]? := by
      rw [List.append_assoc, List.getElem?_append_right (by omega),
        List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
      congr 1
      simp only [List.length_cons, List.length_nil]
      omega
    have h2 : (x ++ T)[i]? = T[i - x.length]? := by
      rw [List.getElem?_append_right (by omega)]
    rw [h1, h2]

lemma step_eq (x T : List Bool) (g : Gate) :
    step (x ++ T) g = x ++ (T ++ [g.op.eval (g.inputs.map fun i => (x ++ T).getD i false)]) := by
  simp [step]

lemma fold_rel (n : ℕ) (x : List Bool) (hx : x.length = n) (a b : Bool) :
    ∀ (gs : List Gate) (T : List Bool), ∃ T' : List Bool,
      gs.foldl step (x ++ T) = x ++ T' ∧
      (gs.map (rho n)).foldl step (x ++ [a, b] ++ T) = x ++ [a, b] ++ T' := by
  intro gs
  induction gs with
  | nil =>
    intro T
    exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hv : (rho n g).op.eval ((rho n g).inputs.map fun i => (x ++ [a, b] ++ T).getD i false) =
        g.op.eval (g.inputs.map fun i => (x ++ T).getD i false) := by
      simp only [rho, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact key n x T hx a b i
    obtain ⟨T', h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (x ++ T).getD i false)])
    refine ⟨T', ?_, ?_⟩
    · rw [List.foldl_cons, step_eq]
      exact h1
    · rw [List.map_cons, List.foldl_cons, step_eq (x ++ [a, b]) T (rho n g), hv]
      exact h2

lemma main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (x1 + (2 : ℕ)) x6 ∧ x6.size = x2.size ∧ x6.output < x1 + (2 : ℕ) + x6.size ∧ (∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 x10 : Bool), x6.eval (x7 ++ [x9, x10]) = x2.eval x7) ∧ ∀ x7 < x1, (∃ x9 ∈ x2.gates, x7 ∈ x9.inputs) → ∃ x10 ∈ x6.gates, x7 ∈ x10.inputs := by
  intro n C hM hR hO
  refine ⟨⟨C.gates.map (rho n), phi n C.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hM g0 hg0
    exact ⟨h1, by simpa [rho] using h2⟩
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    have hg : gateAt ⟨C.gates.map (rho n), phi n C.output⟩ j = rho n (gateAt C j) := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj']
    rw [hg] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    have := hR j hj' i0 hi0
    unfold phi
    split_ifs <;> omega
  · simp [Circuit.size]
  · have hO' : C.output < n + C.gates.length := hO
    show phi n C.output < n + 2 + (C.gates.map (rho n)).length
    rw [List.length_map]
    unfold phi
    split_ifs <;> omega
  · intro x hx a b
    obtain ⟨T', h1, h2⟩ := fold_rel n x hx a b C.gates []
    simp only [List.append_nil] at h1 h2
    show ((C.gates.map (rho n)).foldl step (x ++ [a, b])).getD (phi n C.output) false =
      (C.gates.foldl step x).getD C.output false
    rw [h1, h2]
    exact key n x T' hx a b C.output
  · intro w hw ⟨g, hg, hwg⟩
    refine ⟨rho n g, List.mem_map_of_mem hg, ?_⟩
    show w ∈ g.inputs.map (phi n)
    exact List.mem_map.mpr ⟨w, hwg, by simp [phi, hw]⟩

end PEqualNP.Outside.L_meta_4229_aux

theorem PEqualNP.Outside.L_meta_4229 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (x1 + (2 : ℕ)) x6 ∧ x6.size = x2.size ∧ x6.output < x1 + (2 : ℕ) + x6.size ∧ (∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 x10 : Bool), x6.eval (x7 ++ [x9, x10]) = x2.eval x7) ∧ ∀ x7 < x1, (∃ x9 ∈ x2.gates, x7 ∈ x9.inputs) → ∃ x10 ∈ x6.gates, x7 ∈ x10.inputs := by
  exact PEqualNP.Outside.L_meta_4229_aux.main
