import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4013_7
    (subst : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Fin x1), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x2.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : List Bool), x5.eval (List.ofFn x6 ++ x7) = x2.eval (List.ofFn (x6 ∘ x3) ++ x7))
    (fixZero : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Bool), ∀ (x5 : Fin (10 : ℕ) → Bool), x5 (0 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) = x4) ∨ ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => (List.ofFn x2).getD x6 (1 : Fin (10 : ℕ)) == (0 : Fin (10 : ℕ))) x1.gates).length ≤ x1.size ∧ ∀ (x5 : Fin (10 : ℕ) → Bool), x5 (0 : Fin (10 : ℕ)) = Bool.false → x4.eval ((List.ofFn fun (x7 : Fin (9 : ℕ)) => x5 ([(2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))].getD ↑x7 (0 : Fin (10 : ℕ)))) ++ [Bool.false]) = x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]))
    (base : ∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))))
    (fewReaders : ∀ (C : Circuit) (s : Fin 10 → Fin 10), FanInTwo C → C.size ≤ 18 →
      Function.Surjective s →
      (List.filter (fun g : Gate => (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).any fun i => (List.ofFn s).getD i 1 == 0) C.gates).length ≤ 2 →
      (List.filter (fun g : Gate => (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).any fun i => (List.ofFn s).getD i 1 == 2) C.gates).length ≤ 2 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ s) ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ hfan hsize hsurj

  let pet : (Fin 10 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

  let readers : (Fin 10 → Fin 10) → Fin 10 → ℕ := fun τ v =>
    (List.filter (fun g : Gate => (if g.op.eval [false] = true then List.take 1 g.inputs
      else g.inputs).any fun i => (List.ofFn τ).getD i 1 == v) C.gates).length

  have elim : ∀ τ : Fin 10 → Fin 10, 3 ≤ readers τ 0 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ τ) ++ [x 0 || x 2]) ≠ pet x := by
    intro τ hr
    simp only [readers] at hr
    rcases fixZero C τ hfan with ⟨c, hc⟩ | ⟨E, hE, hEsize, hEeval⟩
    ·
      cases c
      · exact ⟨fun i => i == 1 || i == 2, fun h => absurd ((hc _ rfl).symm.trans h) (by decide)⟩
      · exact ⟨fun _ => false, fun h => absurd ((hc _ rfl).symm.trans h) (by decide)⟩
    · obtain ⟨F, hF, hFsize, hFeval⟩ :=
        subst 10 E (fun j => ([2, 3, 8, 6, 1, 7, 4, 5, 9, 0] : List (Fin 10)).getD j.val 0) hE
      obtain ⟨x, hx0, hx⟩ := base 0 F false hF (show F.size + 0 ≤ 15 by omega)
      refine ⟨x, fun h => hx ?_⟩
      calc F.eval (List.ofFn x) = F.eval (List.ofFn x ++ []) := by rw [List.append_nil]
        _ = E.eval ((List.ofFn fun j : Fin 9 =>
              x (([2, 3, 8, 6, 1, 7, 4, 5, 9] : List (Fin 10)).getD j.val 0)) ++ [x 0]) :=
            hFeval x []
        _ = C.eval (List.ofFn (x ∘ τ) ++ [x 0 || x 2]) := by rw [← hEeval x hx0, hx0]
        _ = _ := h

  let α : Fin 10 → Fin 10 := ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8]
  have hα : ∀ v : Fin 10, (α v == 0) = (v == 2) := by decide
  have hread : readers (α ∘ σ) 0 = readers σ 2 := by
    refine congrArg List.length (List.filter_congr fun g _ => ?_)
    refine congrArg (List.any _) (funext fun i => ?_)
    rw [← hα, ← List.map_ofFn]
    exact congrArg (· == 0) (List.getD_map (List.ofFn σ) 1 α)
  by_cases h0 : readers σ 0 ≤ 2
  · by_cases h2 : readers σ 2 ≤ 2
    · exact fewReaders C σ hfan hsize hsurj h0 h2
    · obtain ⟨x, hx⟩ := elim (α ∘ σ) (by omega)
      have hPET : pet (x ∘ α) = pet x := by
        simp only [pet, α, Function.comp_apply, Matrix.cons_val]
        ac_rfl
      refine ⟨x ∘ α, fun h => hx ?_⟩
      rw [Bool.or_comm (x 0)]
      exact h.trans hPET
  · exact elim σ (by omega)
