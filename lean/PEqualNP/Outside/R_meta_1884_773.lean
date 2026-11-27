import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1884_773
    (relabel : ∀ (n : ℕ) (σ : Fin n → Fin n) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (b : Bool),
        D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ σ) ++ [b]))
    (normalize : ∀ (n : ℕ) (i : Fin n) (f : Bool → Bool) (C : Circuit),
      FanInTwo C → C.output ≠ n →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ ∀ x : Fin n → Bool,
        D.eval (List.ofFn x ++ [!x i]) = C.eval (List.ofFn x ++ [f (x i)]))
    (lower : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ f model budget
  let target := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) ≠ target x
  by_contra noWitness
  obtain ⟨D, modelD, sizeD, evalD⟩ := relabel 10 σ C model
  have computes (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = target x := by
    rw [evalD]
    by_contra different
    exact noWitness ⟨x, different⟩
  by_cases direct : D.output = 10
  · have reads (gs : List Gate) (w : List Bool) (h : 10 < w.length) :
        (Circuit.mk gs 10).eval w = w.getD 10 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        let next := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        change (Circuit.mk gs 10).eval next = w.getD 10 false
        rw [ih next (by simp [next]; omega)]
        exact List.getD_append _ _ _ _ h
    have wire (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = f (x 0) := by
      change (Circuit.mk D.gates D.output).eval _ = _
      rw [direct, reads D.gates _ (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    let zero : Fin 10 → Bool := fun _ => false
    let edge : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have noEdge : target zero = false := by decide
    have hasEdge : target edge = true := by decide
    have b₀ := (wire zero).symm.trans (computes zero)
    have b₁ := (wire edge).symm.trans (computes edge)
    rw [noEdge] at b₀
    rw [hasEdge] at b₁
    change f false = false at b₀
    change f false = true at b₁
    exact Bool.false_ne_true (b₀.symm.trans b₁)
  · obtain ⟨E, modelE, sizeE, evalE⟩ := normalize 10 0 f D modelD direct
    obtain ⟨x, different⟩ := lower E modelE (sizeE.trans (sizeD ▸ budget))
    exact different ((evalE x).trans (computes x))
