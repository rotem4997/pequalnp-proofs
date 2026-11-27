import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6808

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

end PEqualNP.Outside.L_meta_6808

theorem PEqualNP.Outside.L_meta_6808 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Fin x1 → Bool)), (∀ (x5 : Fin x1), x4 ↑x5 = {x6 : Fin x1 → Bool | x6 x5 = Bool.true}) → (∀ x6 < x2, ∃ (x8 : ℕ) (x9 : ℕ), Max.max x8 x9 < x1 + x6 ∧ x4 (x1 + x6) ∈ [x4 x8 ∪ x4 x9, x4 x8, ∅, x4 x8 ∩ x4 x9]) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.output = x3 ∧ x7.size = x2 ∧ PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ ∀ x8 < x1 + x2, ∀ (x10 : Fin x1 → Bool), (x7.wires (List.ofFn x10)).getD x8 Bool.false = Bool.true ↔ x10 ∈ x4 x8 := by
  intro n m o F hin hg
  classical
  choose a b hab h using hg
  let mk : (j : ℕ) → (hj : j < m) → PEqualNP.CircuitLowerBounds.Gate := fun j hj =>
    if F (n + j) = F (a j hj) ∪ F (b j hj) then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a j hj, b j hj]⟩
    else if F (n + j) = F (a j hj) then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a j hj]⟩
    else if F (n + j) = ∅ then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    else ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a j hj, b j hj]⟩
  let gs : List PEqualNP.CircuitLowerBounds.Gate := List.ofFn fun j : Fin m => mk j j.isLt
  have hl : gs.length = m := by simp [gs]
  have hget : ∀ j (hj : j < gs.length), gs[j] = mk j (by omega) := by
    intro j hj; simp [gs]
  have hmkin : ∀ j hj, ∀ i ∈ (mk j hj).inputs, i = a j hj ∨ i = b j hj := by
    intro j hj i hi
    simp only [mk] at hi
    split_ifs at hi <;> simp at hi <;> tauto
  refine ⟨⟨gs, o⟩, rfl, hl, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [hget j hj]
    simp only [mk]
    split_ifs <;> simp
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := List.getD_eq_getElem _ _ hj'
    rw [e, hget j hj'] at hi
    have h1 := hab j (by omega)
    rcases hmkin j _ i hi with rfl | rfl
    · exact lt_of_le_of_lt (le_max_left _ _) h1
    · exact lt_of_le_of_lt (le_max_right _ _) h1
  · intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x
      change (PEqualNP.Outside.L_meta_6808.run gs (List.ofFn x)).getD w false = true ↔ x ∈ F w
      by_cases h9 : w < n
      · rw [PEqualNP.Outside.L_meta_6808.run_input _ _ _ (by simpa using h9)]
        have := hin ⟨w, h9⟩
        simp only at this
        rw [this, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h9]
        rfl
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < m := by omega
        have hj' : j < gs.length := by omega
        have h1 := hab j hj
        have ha : a j hj < n + j := lt_of_le_of_lt (le_max_left _ _) h1
        have hb : b j hj < n + j := lt_of_le_of_lt (le_max_right _ _) h1
        have ia : (PEqualNP.Outside.L_meta_6808.run gs (List.ofFn x)).getD (a j hj) false = true ↔ x ∈ F (a j hj) := ih _ ha (by omega) x
        have ib : (PEqualNP.Outside.L_meta_6808.run gs (List.ofFn x)).getD (b j hj) false = true ↔ x ∈ F (b j hj) := ih _ hb (by omega) x
        have hr := PEqualNP.Outside.L_meta_6808.run_gate gs (List.ofFn x) j hj'
        rw [List.length_ofFn, hget j hj'] at hr
        rw [hr]
        simp only [mk]
        split_ifs with c1 c2 c3
        · simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true, ia, ib, c1, Set.mem_union]
        · simp only [List.map_cons, List.map_nil, if_pos ha, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, ia, c2]
        · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, c3]
        · have h4 : F (n + j) = F (a j hj) ∩ F (b j hj) := by
            have := h j hj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at this
            rcases this with h | h | h | h
            · exact absurd h c1
            · exact absurd h c2
            · exact absurd h c3
            · exact h
          simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true, ia, ib, h4, Set.mem_inter_iff]
