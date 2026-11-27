import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6174

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




def lp (gs : List Gate) (d : List (Bool × Bool)) : List (Bool × Bool) :=
  gs.foldl
    (fun w g =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      w ++ [match g.op with
        | GateOp.or  => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)]) d

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6174

theorem PEqualNP.Outside.L_meta_6174 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →     ∀ (x3 : Bool) (x4 : ℕ → Bool),       have x5 : Fin (14 : ℕ) := if x3 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ));       have x6 : ℕ := if x3 = Bool.true then (7 : ℕ) else (0 : ℕ);       have x7 : List Bool := x1.wires (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = x5));       (∀ x8 < (14 : ℕ), x4 x8 = Decidable.decide (x8 = x6)) →         (∀ x9 < x1.size,             have x11 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9;             have x12 : ℕ := PEqualNP.TopForm.opnd x1 x9 (0 : Fin (2 : ℕ));             have x13 : ℕ := PEqualNP.TopForm.opnd x1 x9 (1 : Fin (2 : ℕ));             (x11.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x9) = (x7.getD x12 Bool.false && x4 x13 || x4 x12 && x7.getD x13 Bool.false)) ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x9) = (x4 x12 || x4 x13))) →           x4 x1.output = Bool.false → PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x11 : ℕ) => if x3 = Bool.true then Decidable.decide ((7 : ℕ) ≤ x11) else !Decidable.decide ((7 : ℕ) ≤ x11)) (0 : ℕ) (7 : ℕ) = Bool.false := by
  intro C hC b f x5 x6 x7 hin hg hout
  have gA : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := fun j hj => List.getD_eq_getElem _ _ hj
  let L : ℕ → Bool := fun i => if b = true then decide (7 ≤ i) else !decide (7 ≤ i)
  let X : List Bool := List.ofFn fun i : Fin 14 => decide (i = x5)
  have hx7 : x7 = PEqualNP.Outside.L_meta_6174.run C.gates X := rfl
  have key : ∀ k, k ≤ C.gates.length → PEqualNP.Outside.L_meta_6174.lp (C.gates.take k) ((((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun (b, i) => if L i then (false, b) else (b, false)) =
      (List.range (14 + k)).map fun i => (x7.getD i false, f i) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : ∀ i, i < 14 → x7.getD i false = decide (i = (x5 : ℕ)) ∧ f i = decide (i = x6) := by
        intro i hi
        refine ⟨?_, hin i hi⟩
        rw [hx7, PEqualNP.Outside.L_meta_6174.run_input _ _ _ (by simpa [X] using hi)]
        simp only [X]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
        simp [Fin.ext_iff]
      have e2 : ((List.range (14 + 0)).map fun i => (x7.getD i false, f i)) = (List.range 14).map fun i => (decide (i = (x5 : ℕ)), decide (i = x6)) := by
        refine List.map_congr_left fun i hi => ?_
        rw [List.mem_range] at hi
        rw [(e i hi).1, (e i hi).2]
      rw [e2]
      simp only [List.take_zero, PEqualNP.Outside.L_meta_6174.lp, List.foldl_nil]
      cases b <;> decide
    | succ k ih =>
      intro hk
      have hk' : k < C.gates.length := by omega
      rw [List.take_succ_eq_append_getElem hk', PEqualNP.Outside.L_meta_6174.lp, List.foldl_append]
      have ih' := ih (by omega)
      simp only [PEqualNP.Outside.L_meta_6174.lp] at ih'
      rw [ih', show 14 + (k + 1) = (14 + k) + 1 by omega, List.range_succ, List.map_append]
      simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
      congr 1
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 (hC.2.2 _ (List.getElem_mem hk'))
      have h3 := hC.2.1 k hk'
      rw [gA k hk', hpq] at h3
      have hp := h3 p (by simp)
      have hq := h3 q (by simp)
      have hgk := hg k hk'
      simp only [gA k hk', PEqualNP.TopForm.opnd, hpq] at hgk
      have rg := PEqualNP.Outside.L_meta_6174.run_gate C.gates X k hk'
      have hX : X.length = 14 := by simp [X]
      rw [hX, hpq] at rg
      simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, ← hx7] at rg
      have gd : ∀ i, i < 14 + k → ((List.range (14 + k)).map fun i => (x7.getD i false, f i)).getD i (false, false) = (x7.getD i false, f i) := by
        intro i hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
        rfl
      simp only [hpq, List.map_cons, List.map_nil, gd p hp, gd q hq]
      rcases hC.1 _ (List.getElem_mem hk') with hop | hop
      · have hf : f (14 + k) = (x7.getD p false && f q || f p && x7.getD q false) := hgk.1 hop
        rw [hop] at rg
        rw [hop, rg, hf]
        simp only [List.foldl_cons, List.foldl_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id]
        cases x7.getD p false <;> cases x7.getD q false <;> cases f p <;> cases f q <;> rfl
      · have hf : f (14 + k) = (f p || f q) := hgk.2 hop
        rw [hop] at rg
        rw [hop, rg, hf]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have h := key C.gates.length le_rfl
  rw [List.take_length] at h
  unfold PEqualNP.ReadK.lineSingle PEqualNP.ReadK.linearParts
  change ((PEqualNP.Outside.L_meta_6174.lp C.gates ((((List.range 14).map fun i => i == 0 || i == 7).zipIdx).map fun (b, i) => if L i then (false, b) else (b, false))).getD C.output (false, false)).2 = false
  rw [h]
  by_cases ho : C.output < 14 + C.gates.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ho]
    exact hout
  · rw [List.getD_eq_default _ _ (by simp; omega)]
