import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8873

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8873

theorem PEqualNP.Outside.L_meta_8873 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 : List ℕ) (x5 : ℕ),       have x6 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>         have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x8 ||| x9 else x8 &&& x9];       ((List.foldl x6 x4 x2.gates).getD x2.output (0 : ℕ)).testBit x5 = x2.eval (List.map (fun (x7 : ℕ) => x7.testBit x5) x4) := by
  intro n C hC l k stp
  obtain ⟨hop, _, hlen⟩ := hC
  let vl : List ℕ → PEqualNP.CircuitLowerBounds.Gate → ℕ := fun L g => if g.op.eval [true, false] = true then L.getD (g.inputs.getD 0 0) 0 ||| L.getD (g.inputs.getD 1 0) 0 else L.getD (g.inputs.getD 0 0) 0 &&& L.getD (g.inputs.getD 1 0) 0
  have se : ∀ L g, stp L g = L ++ [vl L g] := fun _ _ => rfl
  clear_value stp
  have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (List.foldl stp l gs).length = l.length + gs.length ∧ ∀ w, ((List.foldl stp l gs).getD w 0).testBit k = (PEqualNP.Outside.L_meta_8873.run gs (l.map fun z => z.testBit k)).getD w false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨by simp, fun w => ?_⟩
      show (l.getD w 0).testBit k = (l.map fun z => z.testBit k).getD w false
      by_cases hw : w < l.length
      · rw [List.getD_eq_getElem _ _ hw, List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_map]
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega), Nat.zero_testBit]
    | append_singleton gs g ih =>
      intro hg
      obtain ⟨ih1, ih2⟩ := ih fun g' hg' => hg g' (List.mem_append_left _ hg')
      obtain ⟨ho, hl⟩ := hg g (by simp)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl
      have l2 : (PEqualNP.Outside.L_meta_8873.run gs (l.map fun z => z.testBit k)).length = l.length + gs.length := by rw [PEqualNP.Outside.L_meta_8873.run_length, List.length_map]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, PEqualNP.Outside.L_meta_8873.run_snoc, se]
      refine ⟨by rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton, ih1]; omega, fun w => ?_⟩
      rcases Nat.lt_trichotomy w (l.length + gs.length) with h1 | h1 | h1
      · rw [PEqualNP.Outside.L_meta_8873.getD_ltz 0 _ _ _ (by omega), PEqualNP.Outside.L_meta_8873.getD_lt _ _ _ (by omega), ih2]
      · have e1 : w = (List.foldl stp l gs).length := by omega
        have e2 : w = (PEqualNP.Outside.L_meta_8873.run gs (l.map fun z => z.testBit k)).length := by omega
        conv_lhs => rw [e1, PEqualNP.Outside.L_meta_8873.getD_at' 0]
        conv_rhs => rw [e2, PEqualNP.Outside.L_meta_8873.getD_at]
        rw [hab]
        simp only [vl, hab, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ, ← ih2]
        rcases ho with ho | ho
        · rw [ho, if_neg (by decide), Nat.testBit_and]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        · rw [ho, if_pos (by decide), Nat.testBit_or]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · rw [List.getD_eq_default _ _ (by rw [List.length_append, ih1]; simp; omega), List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega), Nat.zero_testBit]
  exact (key C.gates fun g hg => ⟨hop g hg, hlen g hg⟩).2 C.output
