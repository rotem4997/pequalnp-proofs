import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3634_328
    (represent : ∀ C : Circuit, FanInTwo C → C.size = 13 →
      ∃ (p : Fin 13 → Fin 3 × Fin 3 × Fin 25 × Fin 25) (o : Fin 25),
      let decode : (Fin 3 × Fin 3 × Fin 25 × Fin 25) → Gate := fun w => ⟨if w.1 = 0 then .and else if w.1 = 1 then .or else .not,
        [w.2.2.1.val, w.2.2.2.val].take w.2.1.val⟩
      let D : Circuit := ⟨List.ofFn (fun i => decode (p i)), o.val⟩
      ∀ xs : List Bool, xs.length = 11 → D.eval xs = C.eval xs)
    (mismatch : ∀ S : Finset (Fin 9), S.card = 2 → Disjoint S {0,4} →
      ∀ (p : Fin 13 → Fin 3 × Fin 3 × Fin 25 × Fin 25) (o : Fin 25),
      let decode : (Fin 3 × Fin 3 × Fin 25 × Fin 25) → Gate := fun w => ⟨if w.1 = 0 then .and else if w.1 = 1 then .or else .not,
        [w.2.2.1.val, w.2.2.2.val].take w.2.1.val⟩
      let D : Circuit := ⟨List.ofFn (fun i => decode (p i)), o.val⟩
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ v ∈ S, x v = true)]) ≠
        [1,12,23,34,40,5,16,27,38,57,68,85].any fun k : ℕ =>
          x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro C S hfan hcard _ hdis hsize hcompute
  obtain ⟨p, o, hp⟩ := represent C hfan hsize
  obtain ⟨x, hx⟩ := mismatch S hcard hdis p o
  apply hx
  exact (hp _ (by simp)).trans (hcompute x)
