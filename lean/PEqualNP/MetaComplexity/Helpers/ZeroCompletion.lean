import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.MetaComplexity.L019

/-!
# Completing a table through a small language

Helper for `L-meta-024`. If a language with small circuits answers, on inputs `i ++ c` with
`i` of length `n`, whether a partial table reads `some true` at the position coded by `i`, then
the completion of the table by `false` has a small circuit: take the circuit of the language at
length `n + c.length` and hardwire the last inputs to `c`.
-/

namespace PEqualNP.MetaComplexity.Helpers

/-- The binary value of the list `List.ofFn x`, least significant bit first, is
`tableIndex x`. -/
theorem foldr_ofFn_eq_tableIndex : ∀ (n : ℕ) (x : Fin n → Bool),
    List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 (List.ofFn x)
      = tableIndex x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [List.ofFn_zero]
    simp [tableIndex]
  | succ n ih =>
    intro x
    rw [List.ofFn_succ, List.foldr_cons, ih]
    unfold tableIndex
    rw [Fin.sum_univ_succ, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Fin.val_succ, pow_succ]
    split_ifs <;> simp [mul_comm]

theorem zero_completion (B : Language Bool) (p : Polynomial ℕ) (n : ℕ) (T : List (Option Bool))
    (c : List Bool) (hB : B ∈ PEqualNP.CircuitLowerBounds.SIZE (fun m : ℕ => p.eval m))
    (hT : ∀ i : List Bool, i.length = n → (i ++ c ∈ B ↔
      T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i)
        none = some true)) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (T.getD (tableIndex x) none = some true))
      (p.eval (n + c.length) + 1) := by
  obtain ⟨F, hF, hsz⟩ := (PEqualNP.MetaComplexity.L019 _ B).1 hB (n + c.length)
  have h := hardwire n c.length F c.get _ hsz
  have e : (fun y : Fin n → Bool => F (Fin.append y c.get))
      = fun x : Fin n → Bool => decide (T.getD (tableIndex x) none = some true) := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hF, List.ofFn_fin_append, List.ofFn_get,
      hT _ (List.length_ofFn), foldr_ofFn_eq_tableIndex]
  rw [← e]
  exact h

end PEqualNP.MetaComplexity.Helpers
