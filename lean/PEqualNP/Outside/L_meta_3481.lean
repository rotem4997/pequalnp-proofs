import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3481

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl stepF w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (stepF w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [stepF]

theorem getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepF x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := pre gs x
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (gs.foldl stepF x).getD i false = false := by
  obtain ⟨t, ht, hl⟩ := pre gs x
  rw [ht]
  apply List.getD_eq_default
  simp
  omega

theorem eval_lt (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval
  rw [wires_eq]
  exact getD_lt _ _ _ h

theorem eval_ge (C : Circuit) (x : List Bool) (h : x.length + C.size ≤ C.output) :
    C.eval x = false := by
  unfold Circuit.eval
  rw [wires_eq]
  exact getD_ge _ _ _ h

theorem ofFn_getD (n : ℕ) (f : Fin n → Bool) (o : ℕ) (ho : o < n) :
    (List.ofFn f).getD o false = f ⟨o, ho⟩ := by
  rw [List.getD_eq_getElem?_getD]
  simp [ho]

end PEqualNP.Outside.L_meta_3481

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 hnb _ _ hS _ _ hout hiff
  rcases hout with ho | ho
  · exfalso
    have h := (hiff ⟨x4.output, ho⟩ ⟨x4.output, ho⟩).1 (by
      rw [PEqualNP.Outside.L_meta_3481.eval_lt _ _ (by simpa using ho),
        PEqualNP.Outside.L_meta_3481.ofFn_getD _ _ _ ho]
      simp)
    exact x3.irrefl h
  · by_cases hx : x1 = 0
    · subst hx
      obtain ⟨S, _, hc⟩ := hS
      have : S = ∅ := Finset.eq_empty_of_isEmpty S
      subst this
      simp at hc
      omega
    · exfalso
      obtain ⟨w, hw⟩ := hnb ⟨0, Nat.pos_of_ne_zero hx⟩
      have h := (hiff ⟨0, Nat.pos_of_ne_zero hx⟩ w).2 hw
      rw [PEqualNP.Outside.L_meta_3481.eval_ge _ _ (by simpa using ho)] at h
      exact Bool.false_ne_true h
