import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6151

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

end PEqualNP.Outside.L_meta_6151

theorem PEqualNP.Outside.L_meta_6151 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ x1.size + (5 : ℕ) ∧ ∀ (x4 : List Bool), x4.length = (70 : ℕ) → x3.eval x4 = (x1.eval x4 || x4.getD (25 : ℕ) Bool.false && (x4.getD (12 : ℕ) Bool.false || x4.getD (0 : ℕ) Bool.false || (x4.getD (2 : ℕ) Bool.false || x4.getD (8 : ℕ) Bool.false))) := by
  intro C hC
  let N := 70 + C.gates.length
  let t1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩
  let t2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩
  let t3 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [N, N + 1]⟩
  let t4 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, N + 2]⟩
  let o : ℕ := if C.output < N then C.output else N + 100
  let t5 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [o, N + 3]⟩
  let G := C.gates ++ [t1] ++ [t2] ++ [t3] ++ [t4] ++ [t5]
  refine ⟨⟨G, N + 4⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((((hg | rfl) | rfl) | rfl) | rfl) | rfl
    · exact hC g hg
    all_goals simp [t1, t2, t3, t4, t5]
  · change G.length ≤ C.gates.length + 5
    simp [G]
  · intro x hx
    have L0 : (PEqualNP.Outside.L_meta_6151.run C.gates x).length = N := by
      rw [PEqualNP.Outside.L_meta_6151.run_length, hx]
    have inp : ∀ i, i < 70 → (PEqualNP.Outside.L_meta_6151.run C.gates x).getD i false = x.getD i false := fun i hi =>
      PEqualNP.Outside.L_meta_6151.run_input _ _ _ (by omega)
    generalize hR : PEqualNP.Outside.L_meta_6151.run C.gates x = R at L0 inp
    change (PEqualNP.Outside.L_meta_6151.run G x).getD (N + 4) false = ((PEqualNP.Outside.L_meta_6151.run C.gates x).getD C.output false || _)
    simp only [G, PEqualNP.Outside.L_meta_6151.run_snoc, hR]
    have ho : ∀ S : List Bool, S.length ≤ 10 → (R ++ S).getD o false = R.getD C.output false := by
      intro S hS
      simp only [o]
      split_ifs with h
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have rl : ∀ (S : List Bool) (i : ℕ), i < 70 → (R ++ S).getD i false = x.getD i false := by
      intro S i hi
      rw [← inp i hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    have rr : ∀ (S : List Bool) (j : ℕ), (R ++ S).getD (N + j) false = S.getD j false := by
      intro S j
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      congr 2; omega
    have rr0 : ∀ (S : List Bool), (R ++ S).getD N false = S.getD 0 false := fun S => rr S 0
    simp only [List.append_assoc, t1, t2, t3, t4, t5, List.map_cons, List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval, rr, rr0]
    rw [ho _ (by simp)]
    simp only [rl _ 12 (by norm_num), rl _ 0 (by norm_num), rl _ 2 (by norm_num), rl _ 8 (by norm_num), rl _ 25 (by norm_num), inp 12 (by norm_num), inp 0 (by norm_num)]
    simp
