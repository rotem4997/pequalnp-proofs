import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A first OR supplies an extra input. An incident AND can be separated at the output.
-- The incident-AND case leaves the other twenty positive pairs on fourteen inputs.
-- Only minimal true and maximal false assignments enter the three tail bounds.
theorem PEqualNP.Outside.R_meta_971_2
    (firstGate :
      let edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let tailOK := fun (T : Circuit) (j : Fin 14) =>
        ∀ x : Fin 14 → Bool, T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) = true ↔ hit x
      let withoutEdge := fun T : Circuit =>
        (∀ x : Fin 14 → Bool, (x 0 = false ∨ x 7 = false) →
          (T.eval (List.ofFn x) = true ↔ hit x)) ∧
        T.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
        ∃ T : Circuit, Monotone2 T ∧
          ((T.size + 2 ≤ C.size ∧ withoutEdge T) ∨
          (T.size + 1 ≤ C.size ∧ (tailOK T 1 ∨ tailOK T 7 ∨ tailOK T 9))))
    (edgeAnd :
      let edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let boundary := fun x : Fin 14 → Bool =>
        (hit x ∧ ∀ i, x i = true → ¬hit (Function.update x i false)) ∨
        (¬hit x ∧ ∀ i, x i = false → hit (Function.update x i true))
      ∀ T : Circuit, Monotone2 T →
        (∀ x : Fin 14 → Bool, boundary x → (x 0 = false ∨ x 7 = false) →
          (T.eval (List.ofFn x) = true ↔ hit x)) →
        T.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false → 25 ≤ T.size)
    (sameSideOr :
      let edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let boundary := fun x : Fin 14 → Bool =>
        (hit x ∧ ∀ i, x i = true → ¬hit (Function.update x i false)) ∨
        (¬hit x ∧ ∀ i, x i = false → hit (Function.update x i true))
      ∀ T : Circuit, Monotone2 T →
        (∀ x : Fin 14 → Bool, boundary x →
          (T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 1]]) = true ↔ hit x)) → 26 ≤ T.size)
    (crossOr :
      let edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let hit := fun x : Fin 14 → Bool => ∃ u v : Fin 14,
        (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
      let boundary := fun x : Fin 14 → Bool =>
        (hit x ∧ ∀ i, x i = true → ¬hit (Function.update x i false)) ∨
        (¬hit x ∧ ∀ i, x i = false → hit (Function.update x i true))
      ∀ (T : Circuit) (j : Fin 14), (j = 7 ∨ j = 9) → Monotone2 T →
        (∀ x : Fin 14 → Bool, boundary x →
          (T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) = true ↔ hit x)) → 26 ≤ T.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro C hm hcorrect
  obtain ⟨T, ht, ⟨hsize, htail, he⟩ | ⟨hsize, hsame | hincident | hnonincident⟩⟩ :=
    firstGate C hm hcorrect
  · have hlower := edgeAnd T ht (fun x _ h => htail x h) he
    exact (Nat.succ_le_succ (Nat.succ_le_succ hlower)).trans hsize
  · exact (Nat.succ_le_succ (sameSideOr T ht (fun x _ => hsame x))).trans hsize
  · exact (Nat.succ_le_succ (crossOr T 7 (Or.inl rfl) ht (fun x _ => hincident x))).trans hsize
  · exact (Nat.succ_le_succ (crossOr T 9 (Or.inr rfl) ht (fun x _ => hnonincident x))).trans hsize
