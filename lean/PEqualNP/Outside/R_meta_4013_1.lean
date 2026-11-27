import Mathlib
import PEqualNP.Defs

-- Input substitution, bounded wire normalization, and the finite Petersen obstruction.
theorem PEqualNP.Outside.R_meta_4013_1
    (hsubst : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin n → Fin n),
      PEqualNP.MetaComplexity.FanInTwo C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin n → Bool) (suffix : List Bool),
          D.eval (List.ofFn x ++ suffix) = C.eval (List.ofFn (x ∘ p) ++ suffix)))
    (hbounded : (∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ k →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ k ∧
        D.output ≤ n + k ∧
        (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + k) ∧
        ∀ x : List Bool, x.length = n → D.eval x = C.eval x))
    (hfinite : (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      C.output ≤ 29 → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 29) →
      ∃ x6 : Fin 10 → Bool,
        C.eval (List.ofFn x6 ++ [x6 0 || x6 2]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p hC hsize _
  obtain ⟨D, hD, hDsize, hDeval⟩ := hsubst 10 C p hC
  obtain ⟨E, hE, hEsize, hEout, hEinputs, hEeval⟩ :=
    hbounded 11 18 D hD (by simpa only [hDsize] using hsize)
  obtain ⟨x, hx⟩ := hfinite E hE hEsize hEout hEinputs
  refine ⟨x, ?_⟩
  intro heq
  apply hx
  calc
    E.eval (List.ofFn x ++ [x 0 || x 2]) =
        D.eval (List.ofFn x ++ [x 0 || x 2]) := hEeval _ (by simp)
    _ = C.eval (List.ofFn (x ∘ p) ++ [x 0 || x 2]) := hDeval x _
    _ = _ := heq
