import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11159

open PEqualNP.CircuitLowerBounds

theorem getD_snoc (l : List Bool) (v : Bool) (k : ℕ) :
    (l ++ [v]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem getD_ofFn (n : ℕ) (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem zeroAux (n : ℕ) (lv : ℕ → ℕ) : ∀ (gs : List Gate) (m : ℕ) (l : List Bool),
    l.length = n + m → (∀ k, l.getD k false = true → lv k = 0) →
    (∀ (i : ℕ) (g : Gate), gs[i]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ (g.op = GateOp.and → lv (n + m + i) ≤ lv a + lv b) ∧
        (g.op = GateOp.or → lv (n + m + i) ≤ min (lv a) (lv b))) →
    ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD
      k false = true → lv k = 0 := by
  intro gs
  induction gs with
  | nil => intro m l _ hl _ k hk; exact hl k hk
  | cons g gs ih =>
    intro m l hlen hl hyp k hk
    rw [List.foldl_cons] at hk
    refine ih (m + 1) _ (by simp [hlen]; omega) ?_ ?_ k hk
    · intro k' hk'
      rw [getD_snoc] at hk'
      obtain ⟨hop, a, b, hin, hand, hor⟩ := hyp 0 g rfl
      split_ifs at hk' with h1 h2
      · exact hl k' hk'
      · have hk2 : k' = n + m + 0 := by omega
        rw [hk2]
        rw [hin] at hk'
        rcases hop with hop | hop
        · rw [hop] at hk'
          simp [GateOp.eval] at hk'
          have := hand hop
          have e1 := hl a hk'.1
          have e2 := hl b hk'.2
          omega
        · rw [hop] at hk'
          simp [GateOp.eval] at hk'
          have := hor hop
          rcases hk' with hk' | hk'
          · have e1 := hl a hk'
            omega
          · have e2 := hl b hk'
            omega
    · intro i g' hg'
      have h := hyp (i + 1) g' (by simpa using hg')
      have e : n + (m + 1) + i = n + m + (i + 1) := by omega
      rw [e]
      exact h

def val (n : ℕ) (G : List Gate) (w : List Bool) (x5 : Fin n → Bool) : ℕ → Bool
  | k =>
    if h : k < n then x5 ⟨k, h⟩ else
    match G[k - n]? with
    | none => false
    | some g =>
      if ha : g.inputs.getD 0 0 < k then
        if hb : g.inputs.getD 1 0 < k then
          match g.op with
          | GateOp.and =>
            (w.getD (g.inputs.getD 0 0) false && val n G w x5 (g.inputs.getD 1 0)) ||
              (val n G w x5 (g.inputs.getD 0 0) && w.getD (g.inputs.getD 1 0) false)
          | _ => (val n G w x5 (g.inputs.getD 0 0) || val n G w x5 (g.inputs.getD 1 0))
        else false
      else false
termination_by k => k

end PEqualNP.Outside.L_meta_11159

theorem PEqualNP.Outside.L_meta_11159 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < x1 + x3 ∧ x7 < x1 + x3) →     ∀ (x4 x5 : Fin x1 → Bool) (x6 : ℕ → ℕ),       (∀ (x7 : Fin x1), x4 x7 = Bool.true → x6 ↑x7 = (0 : ℕ)) →         (∀ (x8 : Fin x1), x5 x8 = Bool.true → x6 ↑x8 ≤ (1 : ℕ)) →           (∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 x12 : ℕ), x2.gates[x9]? = Option.some x10 → x10.inputs = [x11, x12] → (x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x9) ≤ x6 x11 + x6 x12) ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x9) ≤ Min.min (x6 x11) (x6 x12))) →             ∃ (x10 : ℕ → Bool),               (∀ (x11 : Fin x1), x10 ↑x11 = x5 x11) ∧                 (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate) (x13 x14 : ℕ),                     x2.gates[x11]? = Option.some x12 →                       x12.inputs = [x13, x14] →                         have x17 : List Bool := x2.wires (List.ofFn x4);                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x11) = (x17.getD x13 Bool.false && x10 x14 || x10 x13 && x17.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x11) = (x10 x13 || x10 x14))) ∧                   ∀ (x11 : ℕ), x10 x11 = Bool.true → x6 x11 ≤ (1 : ℕ) := by
  intro n C hC x4 x5 lv h4 h5 hg
  have W0 : ∀ k, (C.wires (List.ofFn x4)).getD k false = true → lv k = 0 := by
    refine PEqualNP.Outside.L_meta_11159.zeroAux n lv C.gates 0 (List.ofFn x4) (by simp) ?_ ?_
    · intro k hk
      rw [PEqualNP.Outside.L_meta_11159.getD_ofFn] at hk
      split_ifs at hk with h
      · exact h4 ⟨k, h⟩ hk
    · intro i g h
      obtain ⟨hop, a, b, hin, _, _, _⟩ := hC i g h
      refine ⟨hop, a, b, hin, ?_⟩
      simpa using hg i g a b h hin
  refine ⟨PEqualNP.Outside.L_meta_11159.val n C.gates (C.wires (List.ofFn x4)) x5, ?_, ?_, ?_⟩
  · intro k
    rw [PEqualNP.Outside.L_meta_11159.val]
    simp [k.isLt]
  · intro i g a b hgi hin
    dsimp only
    obtain ⟨hop, a', b', hin', _, ha, hb⟩ := hC i g hgi
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have e : n + i - n = i := by omega
    rw [PEqualNP.Outside.L_meta_11159.val]
    simp only [show ¬ (n + i < n) by omega, dite_false, e, hgi, hin]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ha, hb, dite_true]
    rcases hop with hop | hop
    · simp [hop]
    · simp [hop]
  · intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rw [PEqualNP.Outside.L_meta_11159.val] at hk
      split_ifs at hk with h
      · exact h5 ⟨k, h⟩ hk
      · split at hk
        · exact absurd hk (by simp)
        · rename_i g hgk
          obtain ⟨hop, a, b, hin, _, ha', hb'⟩ := hC (k - n) g hgk
          obtain ⟨hand, hor⟩ := hg (k - n) g a b hgk hin
          have e : n + (k - n) = k := by omega
          rw [e] at hand hor
          simp only [hin, List.getD_cons_zero, List.getD_cons_succ] at hk
          split_ifs at hk with hA hB
          rcases hop with hop | hop
          · have := hand hop
            simp only [hop, Bool.or_eq_true, Bool.and_eq_true] at hk
            rcases hk with ⟨w1, v1⟩ | ⟨v1, w1⟩
            · have := W0 a w1
              have := ih b hB v1
              omega
            · have := W0 b w1
              have := ih a hA v1
              omega
          · have := hor hop
            simp only [hop, Bool.or_eq_true] at hk
            rcases hk with v1 | v1
            · have := ih a hA v1
              omega
            · have := ih b hB v1
              omega
