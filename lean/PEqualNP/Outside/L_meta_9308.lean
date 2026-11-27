import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9308

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




theorem one (n : ℕ) (p : Fin n × Fin n) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size + 2 ∧ ∀ x y : Fin n → Bool,
      D.eval (List.ofFn x ++ List.ofFn y) = (C.eval (List.ofFn x ++ List.ofFn y) || (x p.1 && y p.2)) := by
  have hm : ∀ (o : ℕ) (l : List ℕ), l.length ≤ 2 → PEqualNP.MetaComplexity.Monotone2 ⟨C.gates ++ [⟨.and, [p.1.val, n + p.2.val]⟩] ++ [⟨.or, l⟩], o⟩ := by
    intro o l hl g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact hC g hg
    · subst hg; simp
    · subst hg; simpa using hl
  have key : ∀ (x y : Fin n → Bool) (l : List ℕ), (∀ W : List Bool, W = run C.gates (List.ofFn x ++ List.ofFn y) → True) →
      Circuit.eval ⟨C.gates ++ [⟨.and, [p.1.val, n + p.2.val]⟩] ++ [⟨.or, l⟩], 2 * n + C.gates.length + 1⟩ (List.ofFn x ++ List.ofFn y) =
      (l.map fun i => (run C.gates (List.ofFn x ++ List.ofFn y) ++ [x p.1 && y p.2]).getD i false).any id := by
    intro x y l _
    show (run (C.gates ++ [⟨.and, [p.1.val, n + p.2.val]⟩] ++ [⟨.or, l⟩]) (List.ofFn x ++ List.ofFn y)).getD (2 * n + C.gates.length + 1) false = _
    have lX : (List.ofFn x ++ List.ofFn y).length = 2 * n := by rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega
    have lW : (run C.gates (List.ofFn x ++ List.ofFn y)).length = 2 * n + C.gates.length := by rw [run_length, lX]
    have a1 : (run C.gates (List.ofFn x ++ List.ofFn y)).getD p.1.val false = x p.1 := by
      have := p.1.isLt
      rw [run_input _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left]
    have a2 : (run C.gates (List.ofFn x ++ List.ofFn y)).getD (n + p.2.val) false = y p.2 := by
      have := p.2.isLt
      rw [run_input _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    rw [run_snoc, run_snoc]
    simp only [List.map_cons, List.map_nil, a1, a2, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
    have e : 2 * n + C.gates.length + 1 = (run C.gates (List.ofFn x ++ List.ofFn y) ++ [x p.1 && y p.2]).length := by
      rw [List.length_append, lW]; rfl
    rw [e, getD_at]
  by_cases ho : C.output < 2 * n + C.gates.length
  · refine ⟨_, hm (2 * n + C.gates.length + 1) [C.output, 2 * n + C.gates.length] (by simp), by simp [Circuit.size], fun x y => ?_⟩
    rw [key x y _ (fun _ _ => trivial)]
    have lW : (run C.gates (List.ofFn x ++ List.ofFn y)).length = 2 * n + C.gates.length := by
      rw [run_length, List.length_append, List.length_ofFn, List.length_ofFn]; omega
    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [getD_lt _ _ _ (by omega), ← lW, getD_at]
    rfl
  · refine ⟨_, hm (2 * n + C.gates.length + 1) [2 * n + C.gates.length] (by simp), by simp [Circuit.size], fun x y => ?_⟩
    rw [key x y _ (fun _ _ => trivial)]
    have lW : (run C.gates (List.ofFn x ++ List.ofFn y)).length = 2 * n + C.gates.length := by
      rw [run_length, List.length_append, List.length_ofFn, List.length_ofFn]; omega
    have z : C.eval (List.ofFn x ++ List.ofFn y) = false := by
      show (run C.gates (List.ofFn x ++ List.ofFn y)).getD C.output false = false
      exact List.getD_eq_default _ _ (by omega)
    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [← lW, getD_at, z, Bool.false_or]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9308

theorem PEqualNP.Outside.L_meta_9308 : ∀ (x1 : ℕ) (x2 : List (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.size + (2 : ℕ) * x2.length ∧ ∀ (x6 x7 : Fin x1 → Bool), x5.eval (List.ofFn x6 ++ List.ofFn x7) = (x3.eval (List.ofFn x6 ++ List.ofFn x7) || x2.any fun (x8 : Fin x1 × Fin x1) => x6 x8.1 && x7 x8.2) := by
  intro n l
  induction l with
  | nil => exact fun C hC => ⟨C, hC, by simp, fun x y => by simp⟩
  | cons p l ih =>
    intro C hC
    obtain ⟨D, hD, hs, he⟩ := PEqualNP.Outside.L_meta_9308.one n p C hC
    obtain ⟨D', hD', hs', he'⟩ := ih D hD
    refine ⟨D', hD', ?_, fun x y => ?_⟩
    · rw [hs', hs, List.length_cons]; omega
    · rw [he', he, List.any_cons, Bool.or_assoc]
