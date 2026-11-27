import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4201_731
    (h_normal :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 42 → Bool,
          C.eval (List.ofFn x) = true ↔
            ∃ u v : Fin 42,
              (u.val < 21 ∧ 21 ≤ v.val ∧
                (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
              x u = true ∧ x v = true) →
        ∃ F : Finset (Finset (Fin 21) × Finset (Fin 21)),
          (∀ p ∈ F, p.1.Nonempty ∧ p.2.Nonempty ∧
            ∀ u ∈ p.1, ∀ v ∈ p.2,
              (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          (∀ u v : Fin 21,
            (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) →
            ∃ p ∈ F, u ∈ p.1 ∧ v ∈ p.2) ∧
          F.sum (fun p : Finset (Fin 21) × Finset (Fin 21) =>
            p.1.card + p.2.card - 1) ≤
            C.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
              PEqualNP.CircuitLowerBounds.GateOp.casesOn
                g.op false true false (fun _ => false) false) + 1)
    (h_count :
      ∀ F : Finset (Finset (Fin 21) × Finset (Fin 21)),
        (∀ p ∈ F, p.1.Nonempty ∧ p.2.Nonempty ∧
          ∀ u ∈ p.1, ∀ v ∈ p.2,
            (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) →
        (∀ u v : Fin 21,
          (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) →
          ∃ p ∈ F, u ∈ p.1 ∧ v ∈ p.2) →
        105 ≤ F.sum (fun p : Finset (Fin 21) × Finset (Fin 21) =>
          p.1.card + p.2.card - 1)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x1.gates := by
  intro C hmono hcomputes
  obtain ⟨F, hblocks, hcovers, hcost⟩ := h_normal C hmono hcomputes
  have hbound := h_count F hblocks hcovers
  exact Nat.lt_succ_iff.mp
    (lt_of_lt_of_le (by decide : 104 < 105) (hbound.trans hcost))
