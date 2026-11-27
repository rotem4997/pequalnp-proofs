import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_276

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [if_pos rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [if_neg h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, if_pos hi]

private lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, if_neg (lt_irrefl _), if_pos rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [if_pos hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, if_pos hi]
      · rw [if_neg hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

private lemma main_proof (n j a b : ℕ) (C : Circuit) (g : Gate)
    (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    (g.op = GateOp.or →
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧
    (g.op = GateOp.and →
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hg
  have hwire : ∀ x : List Bool, x.length = n →
      (C.wires x).getD (n + j) false =
        g.op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
    intro x hx
    have h := runWires_getD_gate C.gates x j hj
    have hrun : runWires C.gates x = C.wires x := rfl
    rw [hrun, hx, hget, hin] at h
    simpa [ha, hb] using h
  constructor
  · intro hor
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hwire _ (List.length_ofFn), hor]
    simp [GateOp.eval]
  · intro hand
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    rw [hwire _ (List.length_ofFn), hand]
    simp [GateOp.eval]

end PEqualNP.Outside.L_meta_276

theorem PEqualNP.Outside.L_meta_276 :
    ∀ (n j a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.inputs = [a, b] → a < n + j → b < n + j → (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  intro n j a b C g hg hin ha hb
  exact PEqualNP.Outside.L_meta_276.main_proof n j a b C g hg hin ha hb
