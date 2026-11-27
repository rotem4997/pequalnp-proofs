import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5823

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

def sh (n k i : ℕ) : ℕ := if i < n then i else i + k

def shGate (n k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n k)⟩

lemma shift_inv (n k : ℕ) : ∀ (gs : List Gate) (u w : List Bool), n ≤ u.length →
    w.length = u.length + k → (∀ i, w.getD (sh n k i) false = u.getD i false) →
    ∀ i, (wiresFrom (gs.map (shGate n k)) w).getD (sh n k i) false =
      (wiresFrom gs u).getD i false := by
  intro gs
  induction gs with
  | nil => intro u w _ _ h; simpa [wiresFrom] using h
  | cons g gs ih =>
    intro u w hn hl h
    have hb : g.op.eval ((g.inputs.map (sh n k)).map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => u.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    have e1 : wiresFrom ((g :: gs).map (shGate n k)) w =
        wiresFrom (gs.map (shGate n k)) (w ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) := by
      show wiresFrom (gs.map (shGate n k))
        (w ++ [(shGate n k g).op.eval ((shGate n k g).inputs.map fun i => w.getD i false)]) = _
      simp only [shGate]
      rw [hb]
    have e2 : wiresFrom (g :: gs) u =
        wiresFrom gs (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) := rfl
    rw [e1, e2]
    apply ih
    · simp; omega
    · simp; omega
    · intro i
      rcases Nat.lt_trichotomy i u.length with hi | hi | hi
      · have h1 : sh n k i < w.length := by unfold sh; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ hi]
        exact h i
      · have h1 : sh n k i = w.length := by unfold sh; split_ifs <;> omega
        rw [h1, hi]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]
      · have h1 : w.length + 1 ≤ sh n k i := by unfold sh; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma main (N : ℕ) (C2 C3 : Circuit) (xs : List Bool) (hxs : xs.length = N)
    (ho2 : C2.output < N + C2.gates.length) (ho3 : C3.output < N + C3.gates.length) :
    (wiresFrom (C2.gates ++ C3.gates.map (shGate N C2.gates.length) ++
      [⟨GateOp.or, [C2.output, sh N C2.gates.length C3.output]⟩]) xs).getD
        (N + C2.gates.length + C3.gates.length) false =
      ((wiresFrom C2.gates xs).getD C2.output false ||
        (wiresFrom C3.gates xs).getD C3.output false) := by
  rw [wiresFrom_append, wiresFrom_append]
  have hW2l : (wiresFrom C2.gates xs).length = N + C2.gates.length := by
    rw [length_wiresFrom, hxs]
  have hW3l : (wiresFrom (C3.gates.map (shGate N C2.gates.length)) (wiresFrom C2.gates xs)).length =
      N + C2.gates.length + C3.gates.length := by
    rw [length_wiresFrom, hW2l, List.length_map]
  have hA : (wiresFrom (C3.gates.map (shGate N C2.gates.length)) (wiresFrom C2.gates xs)).getD
      C2.output false = (wiresFrom C2.gates xs).getD C2.output false :=
    getD_wiresFrom_lt _ _ _ (by rw [hW2l]; exact ho2)
  have hinv : ∀ i, (wiresFrom C2.gates xs).getD (sh N C2.gates.length i) false = xs.getD i false := by
    intro i
    unfold sh
    split_ifs with hi
    · exact getD_wiresFrom_lt _ _ _ (by omega)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have hB := shift_inv N C2.gates.length C3.gates xs (wiresFrom C2.gates xs) (by omega)
    (by omega) hinv C3.output
  generalize (wiresFrom (C3.gates.map (shGate N C2.gates.length)) (wiresFrom C2.gates xs)) = W3
    at hW3l hA hB
  have e : wiresFrom [⟨GateOp.or, [C2.output, sh N C2.gates.length C3.output]⟩] W3 =
      W3 ++ [W3.getD C2.output false || W3.getD (sh N C2.gates.length C3.output) false] := by
    simp [wiresFrom, GateOp.eval]
  rw [e, hA, hB, ← hW3l]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

end PEqualNP.Outside.L_meta_5823

theorem PEqualNP.Outside.L_meta_5823 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.output < x1 + x1 + x2.size → x3.output < x1 + x1 + x3.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.output < x1 + x1 + x8.size ∧ x8.size ≤ x2.size + x3.size + (1 : ℕ) ∧ ∀ (x9 x10 : Fin x1 → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = (x2.eval (List.ofFn x9 ++ List.ofFn x10) || x3.eval (List.ofFn x9 ++ List.ofFn x10)) := by
  intro n C2 C3 h2 h3 ho2 ho3
  have hs2 : C2.size = C2.gates.length := rfl
  have hs3 : C3.size = C3.gates.length := rfl
  rw [hs2] at ho2
  rw [hs3] at ho3
  refine ⟨⟨C2.gates ++ C3.gates.map (PEqualNP.Outside.L_meta_5823.shGate (n + n) C2.gates.length) ++
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or,
        [C2.output, PEqualNP.Outside.L_meta_5823.sh (n + n) C2.gates.length C3.output]⟩],
      n + n + C2.gates.length + C3.gates.length⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
    · exact h2 g hg
    · simpa [PEqualNP.Outside.L_meta_5823.shGate] using h3 g' hg'
    · simp
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map,
      List.length_singleton]
    omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map,
      List.length_singleton]
    omega
  · intro x y
    exact PEqualNP.Outside.L_meta_5823.main (n + n) C2 C3 (List.ofFn x ++ List.ofFn y)
      (by simp) ho2 ho3
