import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3612_509
    (normalize : ∀ C : Circuit, C.size ≤ 13 → FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 23 ∧
        (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 23) ∧
        ∀ xs : List Bool, xs.length = 10 → D.eval xs = C.eval xs)
    (bounded :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ (j : Fin 9) (D : Circuit), j ≠ 0 → j ≠ 6 → FanInTwo D → D.size ≤ 13 →
        D.output ≤ 23 → (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 23) →
        ∃ x, D.eval ((X x).set j.val (!(x j))) ≠ F x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 ≠ (0 : Fin (9 : ℕ)) → x3 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x9 : Fin (9 : ℕ) → Bool), x4.eval ((x2 x9).set ↑x3 !x9 x3) ≠ x1 x9 := by
  dsimp only
  intro j C hj0 hj6 hC hsize
  obtain ⟨D, hD, hDsize, hout, hins, heval⟩ := normalize C hsize hC
  obtain ⟨x, hx⟩ := bounded j D hj0 hj6 hD (hDsize ▸ hsize) hout hins
  exact ⟨x, fun h => hx ((heval _ (by simp)).trans h)⟩
