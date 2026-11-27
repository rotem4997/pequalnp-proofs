import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18779

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stp_ext : ∀ (gs : List Gate) (w : List Bool), ∃ r, gs.foldl stp w = w ++ r := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr⟩ := ih (stp w g)
    exact ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: r, by rw [List.foldl_cons, hr]; simp [stp]⟩

end PEqualNP.Outside.L_meta_18779

open PEqualNP.Outside.L_meta_18779 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18779 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C ho hm hs hf
  exfalso
  let o : Fin 42 := ⟨C.output, ho⟩
  let e : Fin 42 → Bool := fun i => decide (i = o)
  have hev : C.eval (List.ofFn e) = true := by
    unfold Circuit.eval Circuit.wires
    obtain ⟨r, hr⟩ := stp_ext C.gates (List.ofFn e)
    change (C.gates.foldl stp (List.ofFn e)).getD C.output false = true
    rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ho)]
    simp only [List.getElem?_ofFn, ho, dite_true, Option.getD_some, e]
    exact decide_eq_true rfl
  obtain ⟨a, b, ⟨ha, hb, _⟩, hea, heb⟩ := (hf e).mp hev
  simp only [e, decide_eq_true_eq] at hea heb
  subst hea
  have : (b : ℕ) = (o : ℕ) := by rw [heb]
  omega
