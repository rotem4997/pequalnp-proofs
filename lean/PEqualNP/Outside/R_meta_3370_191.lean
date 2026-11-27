import Mathlib.Data.List.GetD
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3370_191
    (freeze : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      PEqualNP.MetaComplexity.HasCircuitSize 10
        (fun y => C.eval (List.ofFn (Fin.init y) ++ [false, y 9])) 13)
    (lower :
      have F : (Fin 9 → Bool) → Bool := fun x => ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7),
        (6,8), (8,5)] : List (Fin 9 × Fin 9)).any fun p => x p.1 && x p.2;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x, C.eval (List.ofFn x) = F x) → 15 ≤ C.size)
    (tight :
      have F : (Fin 9 → Bool) → Bool := fun x => ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7),
        (6,8), (8,5)] : List (Fin 9 × Fin 9)).any fun p => x p.1 && x p.2;
      ∀ (a : Fin 9), a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 6 →
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
          (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4 || x a]) = F x) →
          (∀ g : PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.FanInTwo ⟨[g], 0⟩ →
            ∃ x : Fin 9 → Bool,
              D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map
                fun i => (List.ofFn x).getD i false)]) ≠ F x) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  let Circuit := PEqualNP.CircuitLowerBounds.Circuit
  let FanInTwo := PEqualNP.MetaComplexity.FanInTwo
  let F (x : Fin 9 → Bool) : Bool := ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7),
        (6,8), (8,5)] : List (Fin 9 × Fin 9)).any fun p => x p.1 && x p.2
  have ofSnoc (x : Fin 9 → Bool) (b : Bool) :
      List.ofFn (Fin.snoc x b) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  change ∀ (a : Fin 9), a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 6 →
    ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x a]) = F x) → False
  intro a ha C hC hsize main
  obtain ⟨D, hD, hDsize, hval⟩ := freeze C hC hsize
  have appendValue (x : Fin 9 → Bool) (b : Bool) :
      D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn x ++ [false, b]) := by
    let y : Fin 10 → Bool := Fin.snoc x b
    have hs : List.ofFn y = List.ofFn x ++ [b] := ofSnoc x b
    rw [← hs, hval]
    have init : Fin.init y = x := by apply Fin.init_snoc
    have last : y 9 = b := by apply Fin.snoc_last
    change C.eval (List.ofFn (Fin.init y) ++ [false, y 9]) = _
    rw [init, last]
  apply tight a ha D hD hDsize
  · intro x
    rw [appendValue]
    exact main x
  · intro g hg
    by_contra! eq
    let Q : Circuit := ⟨g :: D.gates, D.output⟩
    have hQ : FanInTwo Q := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hg _ (by simp)
      · exact hD _ hw
    have val (x : Fin 9 → Bool) : Q.eval (List.ofFn x) = F x := by
      change D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map
        fun i => (List.ofFn x).getD i false)]) = _
      exact eq x
    have minimum := lower Q hQ val
    have counted : Q.size = D.size + 1 := by rfl
    omega
