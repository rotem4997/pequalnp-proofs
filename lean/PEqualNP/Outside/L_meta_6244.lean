import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6244

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

end PEqualNP.Outside.L_meta_6244

theorem PEqualNP.Outside.L_meta_6244 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Fin x2.size), (∀ x5 < x2.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).inputs, x7 < x1 + x5) → (∀ (x6 : Fin x2.size), ↑x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 ↑x6).inputs → x6 = x4) → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 ↑x4).op = PEqualNP.CircuitLowerBounds.GateOp.or → ↑x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 ↑x4).inputs → x2.output ≠ ↑x3 → ∀ (x10 x11 : Fin x1 → Bool), (∀ (x12 : Fin x1), x12 ≠ x3 → x10 x12 = x11 x12) → x11 x3 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x10 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x11 → ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 ↑x4).inputs, (x2.wires (List.ofFn x10)).getD x15 Bool.false = Bool.false := by
  intro n C v a hC hread hop hva hout x y hxy hy hne w hw
  have gA : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := fun j hj => List.getD_eq_getElem _ _ hj
  have ha : (a : ℕ) < C.gates.length := a.isLt
  rw [gA _ ha] at hop hva hw
  have hx : x v = false := by
    by_contra h
    have hxv : x v = true := by simpa using h
    refine hne (congrArg _ ?_)
    funext i
    by_cases hi : i = v
    · rw [hi, hxv, hy]
    · exact hxy i hi
  by_contra hcon
  have hwt : (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn x)).getD w false = true := by
    exact Bool.eq_true_of_not_eq_false hcon
  have hlt : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j := by
    intro j hj i hi
    exact (hC j hj).2 i (by rw [gA j hj]; exact hi)
  have hops : ∀ j (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have := (hC j hj).1
    rwa [gA j hj] at this
  have inp : ∀ (z : Fin n → Bool) (i : ℕ) (hi : i < n), (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn z)).getD i false = z ⟨i, hi⟩ := by
    intro z i hi
    rw [PEqualNP.Outside.L_meta_6244.run_input _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
    rfl
  have hwv : w ≠ (v : ℕ) := by
    intro h
    rw [h, inp x v v.isLt] at hwt
    rw [show (⟨(v : ℕ), v.isLt⟩ : Fin n) = v from rfl, hx] at hwt
    cases hwt
  have key : ∀ i, i ≠ (v : ℕ) → (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn x)).getD i false = (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn y)).getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hiv
      by_cases hi : i < n
      · rw [inp x i hi, inp y i hi]
        exact hxy _ fun h => hiv (congrArg Fin.val h)
      · by_cases hi2 : i < n + C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hj : j < C.gates.length := by omega
          have rx := PEqualNP.Outside.L_meta_6244.run_gate C.gates (List.ofFn x) j hj
          have ry := PEqualNP.Outside.L_meta_6244.run_gate C.gates (List.ofFn y) j hj
          rw [List.length_ofFn] at rx ry
          by_cases hja : j = (a : ℕ)
          · subst hja
            have hwlt := hlt _ hj w hw
            rw [rx, ry, hop]
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map]
            have e1 : (C.gates[(a : ℕ)].inputs.any (id ∘ fun i => if i < n + (a : ℕ) then (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn x)).getD i false else false)) = true := by
              rw [List.any_eq_true]
              exact ⟨w, hw, by simp only [Function.comp, id, if_pos hwlt]; exact hwt⟩
            have e2 : (C.gates[(a : ℕ)].inputs.any (id ∘ fun i => if i < n + (a : ℕ) then (PEqualNP.Outside.L_meta_6244.run C.gates (List.ofFn y)).getD i false else false)) = true := by
              rw [List.any_eq_true]
              refine ⟨w, hw, ?_⟩
              simp only [Function.comp, id, if_pos hwlt]
              rw [← ih w (by omega) hwv]; exact hwt
            rw [e1, e2]
          · rw [rx, ry]
            congr 1
            refine List.map_congr_left fun q hq => ?_
            have hqlt := hlt j hj q hq
            rw [if_pos hqlt, if_pos hqlt]
            refine ih q hqlt fun hqv => hja ?_
            have := hread ⟨j, hj⟩ (by rw [gA j hj]; exact hqv ▸ hq)
            exact congrArg Fin.val this
        · rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6244.run_length]; simp; omega), List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6244.run_length]; simp; omega)]
  exact hne (key C.output hout)
