import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Relabel the nine primary inputs while carrying the two auxiliary inputs unchanged.
-- Reflection and commutativity reduce the forty-two ordered pairs to twelve representatives.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2834_631
    (transport : ∀ (σ : Fin 9 → Fin 9) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin 9 → Bool) (u v : Bool),
          D.eval (List.ofFn x ++ [u,v]) = C.eval (List.ofFn (x ∘ σ) ++ [u,v]))
    (representatives : ∀ (i j : Fin 9), 10 * i.val + j.val ∈ ([12,13,15,16,17,18,23,26,27,28,36,67] : List ℕ) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) = (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  intro i j C hi0 hi4 hj0 hj4 hij fan size eval
  let r : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let f := fun x : Fin 9 → Bool =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  have table : (fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5) = f := by decide +kernel
  have invariant : ∀ x : Fin 9 → Bool, f (x ∘ r) = f x := by decide +kernel
  let allowed := fun a b : Fin 9 => 10 * a.val + b.val ∈ ([12,13,15,16,17,18,23,26,27,28,36,67] : List ℕ)
  have cover : ∀ a b : Fin 9, a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
      allowed a b ∨ allowed b a ∨ allowed (r a) (r b) ∨ allowed (r b) (r a) := by
    decide +kernel
  have direct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x :=
    fun x => (eval x).trans (congrFun table x)
  rcases cover i j hi0 hi4 hj0 hj4 hij with h | h | reflected
  · exact representatives i j h C fan size direct
  · apply representatives j i h C fan size
    intro x
    rw [Bool.or_comm (x j) (x i)]
    exact direct x
  · obtain ⟨D, dfan, dsize, deval⟩ := transport r C fan
    have reflEval : ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, x (r i) || x (r j)]) = f x := by
      intro x
      exact (deval x _ _).trans ((direct (x ∘ r)).trans (invariant x))
    rcases reflected with h | h
    · exact representatives (r i) (r j) h D dfan (dsize.trans_le size) reflEval
    · apply representatives (r j) (r i) h D dfan (dsize.trans_le size)
      intro x
      rw [Bool.or_comm (x (r j)) (x (r i))]
      exact reflEval x
