import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3596

open PEqualNP.CircuitLowerBounds

private theorem read_prefix (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun k => s.getD k false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    · simp [List.getD, List.getElem?_append_left, hi]
    · simp only [List.length_append, List.length_singleton]
      omega

end PEqualNP.Outside.L_meta_3596

theorem PEqualNP.Outside.L_meta_3596 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n incidence decInc C hq hn hlines hmeet hmono hout htop haccept hsound
  let o : Fin (n + n) := ⟨C.output, hout⟩
  let x : Fin (n + n) → Bool := fun w => decide (w = o)
  have hx (w : Fin (n + n)) (h : x w = true) : w = o := of_decide_eq_true h
  have hsub : Subsingleton { l : Fin n // x (Fin.natAdd n l) = true } := by
    constructor
    intro l k
    apply Subtype.ext
    apply Fin.ext
    have he : Fin.natAdd n l.val = Fin.natAdd n k.val :=
      (hx _ l.property).trans (hx _ k.property).symm
    have eqVal := congrArg Fin.val he
    simp only [Fin.val_natAdd] at eqVal
    omega
  have hcard₁ : Fintype.card { l : Fin n // x (Fin.natAdd n l) = true } ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hcard : Fintype.card { l : Fin n // x (Fin.natAdd n l) = true } ≤ q := by omega
  have hfree : ¬ ∃ p l : Fin n, incidence p l ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true := by
    rintro ⟨p, l, _, hp, hl⟩
    have he : Fin.castAdd n p = Fin.natAdd n l := (hx _ hp).trans (hx _ hl).symm
    have eqVal := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at eqVal
    omega
  have hf := hsound x hcard hfree
  have ht : PEqualNP.MetaComplexity.circuitFun (n + n) C x = true := by
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
      PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [PEqualNP.Outside.L_meta_3596.read_prefix]
    · simp [hout, x, o]
    · simpa using hout
  exact Bool.noConfusion (hf.symm.trans ht)
