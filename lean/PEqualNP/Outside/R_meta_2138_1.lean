import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2138_1
    (h_0 : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 12 ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x ++ [!(x 0)]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)))
    (h_1 : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 12 ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x ++ [!(x 1)]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)))
    (orbit : ∀ i : Fin 8, ∃ σ : Fin 8 → Fin 8, (σ i = 0 ∨ σ i = 1) ∧
      ∀ y : Fin 8 → Bool, (let x : Fin 9 → Bool := Fin.insertNth (6 : Fin 9) false (y ∘ σ); (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) =
        (let x := y; (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)))
    (h_project : ∀ (f : (Fin 9 → Bool) → Bool),
      (f (fun j => decide (j = 1)) ≠ f (fun j => decide (j = 1 ∨ j = 6))) →
      (f (Fin.insertNth (6 : Fin 9) false (fun _ => false)) ≠
      f (Fin.insertNth (6 : Fin 9) false (fun _ => true))) → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ g ∈ C.gates[1]?.toList, 9 ∈ g.inputs) → PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = f →
    ∃ i : Fin 8, ∀ σ : Fin 8 → Fin 8, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size+3 ≤ C.size ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y ++ [!(y (σ i))]) =
        f (Fin.insertNth (6 : Fin 9) false (y ∘ σ))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x2 ∈ x1.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x2.inputs) → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C second fan first computes
  by_contra! small
  obtain ⟨i,p⟩ := h_project _ (by decide) (by decide) C second fan first computes
  obtain ⟨σ,orbit_i,rows⟩ := orbit i
  obtain ⟨D,ok,cost,ev⟩ := p σ
  have sz : D.size ≤ 12 := by omega
  rcases orbit_i with e | e
  · exact h_0 ⟨D,ok,sz,fun y => by simpa only [e] using (ev y).trans (rows y)⟩
  · exact h_1 ⟨D,ok,sz,fun y => by simpa only [e] using (ev y).trans (rows y)⟩
