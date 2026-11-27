import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_582_773
    (search :
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let target := fun x : Fin 14 → Bool => decide
        (∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true)
      let rank := fun (a b c d : ℕ) =>
        (15 * min a b + max a b) * 225 + (15 * min c d + max c d)
      let rename := fun (σ : Equiv.Perm (Fin 14)) (i : Fin 15) =>
        if i.val < 14 then (σ (Fin.ofNat 14 i.val)).val else 14
      ∃ (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) (D : Circuit),
        a < b ∧ c < d ∧
        (op₁ = GateOp.and ∨ op₁ = GateOp.or) ∧ (op₂ = GateOp.and ∨ op₂ = GateOp.or) ∧
        (∀ σ : Equiv.Perm (Fin 14), (∀ x, target (x ∘ σ) = target x) →
          rank a.val b.val c.val d.val ≤ rank (σ a).val (σ b).val (rename σ c) (rename σ d)) ∧
        Monotone2 D ∧ D.size ≤ 24 ∧
        ∀ x : Fin 14 → Bool,
          let w := List.ofFn x ++ [op₁.eval [x a,x b]]
          D.eval (w ++ [op₂.eval [w.getD c.val false,w.getD d.val false]]) = target x)
    (prepend : ∀ (n k : ℕ) (a b : Fin n) (c d : Fin (n + 1)) (op₁ op₂ : GateOp),
      (op₁ = GateOp.and ∨ op₁ = GateOp.or) → (op₂ = GateOp.and ∨ op₂ = GateOp.or) →
      ∀ D : Circuit, Monotone2 D → D.size ≤ k →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 2 ∧ ∀ x : Fin n → Bool,
        let w := List.ofFn x ++ [op₁.eval [x a,x b]]
        C.eval (List.ofFn x) = D.eval (w ++ [op₂.eval [w.getD c.val false,w.getD d.val false]])) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨a, b, c, d, op₁, op₂, D, _, _, kind₁, kind₂, _, mono, size, computes⟩ := search
  obtain ⟨C, model, budget, eval⟩ := prepend 14 24 a b c d op₁ op₂ kind₁ kind₂ D mono size
  refine ⟨C, model, budget, ?_⟩
  intro x
  rw [eval x, computes x]
  simp only [decide_eq_true_eq]
