import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9115

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




def fx (m i : ℕ) : Fin (m + 1) := ⟨min i m, by omega⟩

def nf (m : ℕ) (g : Gate) : Fin (m + 1) ⊕ Bool × Fin (m + 1) × Fin (m + 1) :=
  match g.op, g.inputs with
  | .and, [] => .inl (fx m m)
  | .and, [a] => .inr (false, fx m a, fx m a)
  | .and, a :: b :: _ => .inr (false, fx m a, fx m b)
  | .or, [] => .inr (true, fx m m, fx m m)
  | .or, [a] => .inr (true, fx m a, fx m a)
  | .or, a :: b :: _ => .inr (true, fx m a, fx m b)
  | _, [] => .inl (fx m m)
  | _, a :: _ => .inl (fx m a)

def gt (m : ℕ) (s : Fin (m + 1) ⊕ Bool × Fin (m + 1) × Fin (m + 1)) : Gate :=
  Sum.elim (fun x7 : Fin (m + 1) => ({ op := GateOp.not, inputs := [↑x7] } : Gate))
    (fun x7 : Bool × Fin (m + 1) × Fin (m + 1) => ({ op := Bool.rec GateOp.and GateOp.or x7.1, inputs := [↑x7.2.1, ↑x7.2.2] } : Gate)) s

theorem fxv (w : List Bool) (i : ℕ) : w.getD (fx w.length i : Fin (w.length + 1)).val false = w.getD i false := by
  show w.getD (min i w.length) false = _
  rcases Nat.le_total i w.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.getD_eq_default _ _ le_rfl, List.getD_eq_default _ _ h]

theorem fxv0 (w : List Bool) : w.getD (fx w.length w.length : Fin (w.length + 1)).val false = false := by
  rw [fxv, List.getD_eq_default _ _ le_rfl]

theorem one (w : List Bool) (m : ℕ) (hm : w.length = m) (g : Gate) (h : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    (gt m (nf m g)).op.eval ((gt m (nf m g)).inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hm
  obtain ⟨op, l⟩ := g
  simp only at h hl
  rcases h with h | h | h <;> subst h <;> rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    first
    | (simp at hl; done)
    | (simp only [nf, gt, Sum.elim_inl, Sum.elim_inr, List.map_cons, List.map_nil, fxv, fxv0, GateOp.eval]
       try simp)

theorem main (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (x : List Bool) (hx : x.length = n) :
    run (List.ofFn fun j : Fin gs.length => gt (n + j) (nf (n + j) gs[j])) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have ih := ih fun g' hg' => hgs g' (by simp [hg'])
    have e : (List.ofFn fun j : Fin (gs ++ [g]).length => gt (n + j) (nf (n + j) (gs ++ [g])[j])) =
        (List.ofFn fun j : Fin gs.length => gt (n + j) (nf (n + j) gs[j])) ++ [gt (n + gs.length) (nf (n + gs.length) g)] := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        rw [List.getElem_ofFn]
        simp only [List.length_ofFn, List.length_append, List.length_singleton] at h1
        rcases Nat.lt_or_ge i gs.length with h | h
        · rw [List.getElem_append_left (by simpa using h), List.getElem_ofFn]
          simp [h]
        · have : i = gs.length := by omega
          subst this
          simp
    rw [e, run_snoc, run_snoc, ih]
    congr 2
    exact one _ _ (by rw [run_length, hx]) g (hgs g (by simp)).1 (hgs g (by simp)).2

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9115

theorem PEqualNP.Outside.L_meta_9115 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     ∃ (x4 : (x4 : Fin x2.size) → Fin (x1 + ↑x4 + (1 : ℕ)) ⊕ Bool × Fin (x1 + ↑x4 + (1 : ℕ)) × Fin (x1 + ↑x4 + (1 : ℕ))) (x5 : Fin (x1 + x2.size + (1 : ℕ))),       have x6 : List PEqualNP.CircuitLowerBounds.Gate := List.ofFn fun (x6 : Fin x2.size) => Sum.elim (fun (x7 : Fin (x1 + ↑x6 + (1 : ℕ))) => { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x7] : PEqualNP.CircuitLowerBounds.Gate }) (fun (x7 : Bool × Fin (x1 + ↑x6 + (1 : ℕ)) × Fin (x1 + ↑x6 + (1 : ℕ))) => { op := Bool.rec PEqualNP.CircuitLowerBounds.GateOp.and PEqualNP.CircuitLowerBounds.GateOp.or x7.1, inputs := [↑x7.2.1, ↑x7.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (x4 x6);       ∀ (x7 : List Bool), x7.length = x1 → x2.eval x7 = { gates := x6, output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit }.eval x7 := by
  intro n C hC
  refine ⟨fun j => PEqualNP.Outside.L_meta_9115.nf (n + j) C.gates[j], PEqualNP.Outside.L_meta_9115.fx (n + C.size) C.output, ?_⟩
  intro gs x hx
  have hgs : gs = List.ofFn fun j : Fin C.gates.length => PEqualNP.Outside.L_meta_9115.gt (n + j) (PEqualNP.Outside.L_meta_9115.nf (n + j) C.gates[j]) := rfl
  have hm := PEqualNP.Outside.L_meta_9115.main n C.gates (fun g hg => ⟨by simpa using (hC g hg).1, (hC g hg).2⟩) x hx
  show (PEqualNP.Outside.L_meta_9115.run C.gates x).getD C.output false = (PEqualNP.Outside.L_meta_9115.run gs x).getD (PEqualNP.Outside.L_meta_9115.fx (n + C.size) C.output).val false
  rw [hgs, hm]
  have hl : (PEqualNP.Outside.L_meta_9115.run C.gates x).length = n + C.size := by rw [PEqualNP.Outside.L_meta_9115.run_length, hx]; rfl
  rw [← hl, PEqualNP.Outside.L_meta_9115.fxv]
