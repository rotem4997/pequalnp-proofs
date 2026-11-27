import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18755
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

def step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

lemma appended (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false = if i = a.length then v else a.getD i false := by
  by_cases h : i < a.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, Nat.ne_of_lt h]
  · by_cases he : i = a.length
    · subst i
      simp [List.getD_eq_getElem?_getD, List.getElem?_append]
    · have hp : 0 < i - a.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, he, List.getElem?_eq_none_iff.mpr (by omega : a.length ≤ i), List.getElem?_eq_none_iff.mpr (by change 1 ≤ i - a.length; omega : [v].length ≤ i - a.length)]

lemma oldWire (gs : List Gate) (a : List Bool) (i : ℕ) (h : i < a.length) :
    (gs.foldl step a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step,appended,if_neg (Nat.ne_of_lt h)]
end PEqualNP.Outside.L_meta_18755
open PEqualNP.Outside.L_meta_18755
theorem PEqualNP.Outside.L_meta_18755 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) := by
  intro C ho _ _ correct
  exfalso
  let z : Fin 42 := ⟨C.output,ho⟩
  let y (i : Fin 42) := decide (i=z)
  have hit : C.eval (List.ofFn y) = true := by
    change (C.gates.foldl step (List.ofFn y)).getD C.output false = true
    rw [oldWire _ _ _ (by simpa only [List.length_ofFn] using ho)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos ho,Option.getD_some,y,z,decide_true]
  obtain ⟨i,j,⟨hi,hj,_⟩,h1,h2⟩ := (correct y).mp hit
  have e1 : i=z := of_decide_eq_true h1
  have e2 : j=z := of_decide_eq_true h2
  rw [e1] at hi
  rw [e2] at hj
  omega
