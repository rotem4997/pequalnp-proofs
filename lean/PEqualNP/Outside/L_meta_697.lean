import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_697_aux

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem or_val (C : Circuit) (x : List Bool) (t a b : ℕ)
    (hgate : C.gates[t]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < x.length + t)
    (hb : b < x.length + t) :
    (C.wires x).getD (x.length + t) false
      = ((C.wires x).getD a false || (C.wires x).getD b false) := by
  have ht : t < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgate
    exact absurd hgate (by simp)
  have hG : C.gates[t] = ⟨GateOp.or, [a, b]⟩ := by
    rw [List.getElem?_eq_getElem ht] at hgate
    exact Option.some.inj hgate
  have hlen : ((C.gates.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  rw [wires_eq, foldl_step_getD_gate _ _ _ ht, hG,
    foldl_take_getD C.gates x t a (by rw [hlen]; exact ha),
    foldl_take_getD C.gates x t b (by rw [hlen]; exact hb)]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_697_aux

open PEqualNP.Outside.L_meta_697_aux PEqualNP.CircuitLowerBounds PEqualNP.LowMerge in
theorem PEqualNP.Outside.L_meta_697 :
    ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), (∀ (p p' : Fin P) (w w' : Fin L), p ≠ p' → w ≠ w' → ¬ (inc p w = true ∧ inc p w' = true ∧ inc p' w = true ∧ inc p' w' = true)) → (∀ (x : Fin P → Bool) (y y' : Fin L → Bool), (C.wires (List.ofFn x ++ List.ofFn y)).getD g false = (C.wires (List.ofFn x ++ List.ofFn y')).getD g false) → ∀ (w w' : Fin L), PEqualNP.LowMerge.IsLowMerge P L inc C g w → PEqualNP.LowMerge.IsLowMerge P L inc C g w' → w = w' := by
  intro P L inc C g H1 H2 w w' hm hm'
  obtain ⟨hg, a, ha, b, hb, hgate, hlow, hab, hba⟩ := hm
  obtain ⟨_, _, _, _, _, _, hlow', _, _⟩ := hm'
  obtain ⟨p1, hp1a, hp1b⟩ := Finset.not_subset.mp hab
  obtain ⟨p2, hp2b, hp2a⟩ := Finset.not_subset.mp hba
  simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp1a hp1b hp2b hp2a
  have hne : p1 ≠ p2 := by
    rintro rfl
    exact hp2a hp1a
  have hlenI : ∀ (p : Fin P) (v : Fin L), (pointLineInput P L p v).length = P + L := by
    intro p v
    simp [pointLineInput, restrictInput]
  have hgv : ∀ (p : Fin P) (v : Fin L), wireVal C (pointLineInput P L p v) g
      = (wireVal C (pointLineInput P L p v) a || wireVal C (pointLineInput P L p v) b) := by
    intro p v
    have h := or_val C (pointLineInput P L p v) (g - (P + L)) a b hgate
      (by rw [hlenI]; omega) (by rw [hlenI]; omega)
    rw [hlenI, Nat.add_sub_cancel' hg] at h
    exact h
  have hsame : ∀ p : Fin P, wireVal C (pointLineInput P L p w) g
      = wireVal C (pointLineInput P L p w') g := by
    intro p
    exact H2 (fun q => decide (q = p)) (fun v => decide (v = w)) (fun v => decide (v = w'))
  have hinc : ∀ (p : Fin P) (v : Fin L), IsLow P L inc C g v →
      wireVal C (pointLineInput P L p v) g = true → inc p v = true := by
    intro p v hl hv
    have h := hl (fun q => decide (q = p)) hv
    simp only [lineSum, decide_eq_true_eq] at h
    obtain ⟨q, hq, hqp⟩ := h
    subst hqp
    exact hq
  have g1 : wireVal C (pointLineInput P L p1 w) g = true := by
    rw [hgv, hp1a, Bool.true_or]
  have g2 : wireVal C (pointLineInput P L p2 w) g = true := by
    rw [hgv, hp2b, Bool.or_true]
  have i1 := hinc p1 w hlow g1
  have i2 := hinc p2 w hlow g2
  have i1' := hinc p1 w' hlow' (by rw [← hsame p1]; exact g1)
  have i2' := hinc p2 w' hlow' (by rw [← hsame p2]; exact g2)
  by_contra hw
  exact H1 p1 p2 w w' hne hw ⟨i1, i1', i2, i2'⟩
