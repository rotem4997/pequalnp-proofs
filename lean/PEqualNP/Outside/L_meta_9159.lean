import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9159
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem foldl_prefix (gs : List Gate) (w : List Bool) : ∃ t,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t,
      by rw [List.foldl_cons, ht, List.append_assoc]⟩

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := foldl_prefix C.gates x
  unfold Circuit.wires
  rw [ht, List.getD_append _ _ _ _ hi]

theorem agree (p q : ℕ) (hpq : q ≠ p) : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → q < w.length → w.getD q false = false →
    (∀ i, i ≠ p → w.getD i false = w'.getD i false) →
    (∀ g ∈ gs, p ∈ g.inputs → g.op = GateOp.and ∧ (g.inputs = [p, q] ∨ g.inputs = [q, p])) →
    ∀ i, i ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ _ h _ i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hlen hq hq0 hagree hgood i hi
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      by_cases hp : p ∈ g.inputs
      · obtain ⟨hop, hin⟩ := hgood g (List.mem_cons_self ..) hp
        have hq0' : w'.getD q false = false := by rw [← hagree q hpq]; exact hq0
        rw [hop]
        rcases hin with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, hq0, hq0', id, Bool.and_false, Bool.false_and, Bool.and_true]
      · congr 1
        apply List.map_congr_left
        intro j hj
        exact hagree j (fun h => hp (h ▸ hj))
    apply ih
    · simp [hlen]
    · simp; omega
    · rw [List.getD_append _ _ _ _ hq]; exact hq0
    · intro j hj
      rw [hv]
      by_cases hjl : j < w.length
      · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (by omega)]
        exact hagree j hj
      · rw [Nat.not_lt] at hjl
        rw [List.getD_append_right _ _ _ _ hjl, List.getD_append_right _ _ _ _ (by omega), hlen]
    · intro g' hg' hp; exact hgood g' (List.mem_cons_of_mem _ hg') hp
    · exact hi

theorem pair_agree (a b : List Bool) (ha : a.length = 9) (hb : b.length = 9)
    (h : ∀ i < 9, i ≠ 4 → a.getD i false = b.getD i false) :
    ∀ i, i ≠ 4 → a.getD i false = b.getD i false := by
  intro i hi
  by_cases h9 : i < 9
  · exact h i h9 hi
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem finish (C : Circuit) (q : ℕ) (hq4 : q ≠ 4)
    (hgood : ∀ g ∈ C.gates, 4 ∈ g.inputs → g.op = GateOp.and ∧ (g.inputs = [4, q] ∨ g.inputs = [q, 4]))
    (hout : C.output ≠ 4) (a b : Fin 9 → Bool) (hq : q < 9)
    (ha : (List.ofFn a).getD q false = false)
    (hab : ∀ i < 9, i ≠ 4 → (List.ofFn a).getD i false = (List.ofFn b).getD i false) :
    circuitFun 9 C a = circuitFun 9 C b := by
  have := agree 4 q hq4 C.gates (List.ofFn a) (List.ofFn b) (by simp) (by simpa using hq) ha
    (pair_agree _ _ (by simp) (by simp) hab) hgood C.output hout
  show (C.wires (List.ofFn a)).getD C.output false = (C.wires (List.ofFn b)).getD C.output false
  exact this

end PEqualNP.Outside.L_meta_9159

theorem PEqualNP.Outside.L_meta_9159 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), ∀ x3 < (9 : ℕ), x3 ≠ (4 : ℕ) → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x7 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x7).inputs → x7 = x2) → (x1.gates.get x2).inputs = [(4 : ℕ), x3] ∨ (x1.gates.get x2).inputs = [x3, (4 : ℕ)] → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x9 : Fin (9 : ℕ) → Bool) => x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) := by
  intro C x2 x3 hx3 hx34 hop huniq hin hfun
  have hgood : ∀ g ∈ C.gates, 4 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (g.inputs = [4, x3] ∨ g.inputs = [x3, 4]) := by
    intro g hg h4
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hg
    have hkx : k = x2 := huniq k (hk ▸ h4)
    rw [← hk, hkx]
    exact ⟨hop, hin⟩
  by_cases hout : C.output = 4
  · have h1 : PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => decide (i.val ≠ 4)) = false := by
      show (C.wires (List.ofFn (fun i : Fin 9 => decide (i.val ≠ 4)))).getD C.output false = false
      rw [hout, PEqualNP.Outside.L_meta_9159.wires_input C _ 4 (by simp)]
      decide
    rw [hfun] at h1
    revert h1
    decide
  · by_cases h0 : x3 = 0
    · subst h0
      have := PEqualNP.Outside.L_meta_9159.finish C 0 (by decide) hgood hout
        (fun i : Fin 9 => decide (i.val = 3)) (fun i : Fin 9 => decide (i.val = 3 ∨ i.val = 4))
        (by decide) (by decide) (by decide)
      rw [hfun] at this
      revert this
      decide
    · have hall : ∀ i < 9, i ≠ 0 →
          (List.ofFn (fun i : Fin 9 => decide (i.val = 0))).getD i false = false := by decide
      have := PEqualNP.Outside.L_meta_9159.finish C x3 hx34 hgood hout
        (fun i : Fin 9 => decide (i.val = 0)) (fun i : Fin 9 => decide (i.val = 0 ∨ i.val = 4))
        hx3 (hall x3 hx3 h0) (by decide)
      rw [hfun] at this
      revert this
      decide
