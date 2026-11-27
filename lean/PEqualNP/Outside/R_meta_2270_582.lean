import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Restrict an adjacent pair, then test all wire equalities on the restricted inputs.
-- Redirected wires must be earlier or missing, so all certified gates can be removed together.
theorem PEqualNP.Outside.R_meta_2270_582
    (eraseAliases : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
      FanInTwo C → (∀ j ∈ S, j < C.size) →
      (∀ j ∈ S, ∃ p : ℕ, (p < n + j ∨ n + C.size ≤ p) ∧
        ∀ x : Fin n → Bool,
          let w := C.wires (List.ofFn (Function.update (Function.update x u false) v false))
          w.getD (n + j) false = w.getD p false) →
      HasCircuitSize n
        (fun x => C.eval (List.ofFn (Function.update (Function.update x u false) v false)))
        (C.size - S.card))
    (sparse :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool),
        ¬x2.Colorable (2 : ℕ) →
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔
          (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨
          ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
        ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 →
            (∀ (C : Circuit), FanInTwo C → C.size ≤ x11 →
              (∀ x : Fin x1 → Bool, C.eval (List.ofFn x) = x4 x) →
              ∀ u v : Fin x1, x2.Adj u v →
              ∀ S : Finset ℕ, (∀ j ∈ S, j < C.size) →
              (∀ j ∈ S, ∃ p : ℕ, (p < x1 + j ∨ x1 + C.size ≤ p) ∧
                ∀ x : Fin x1 → Bool,
                  let w := C.wires (List.ofFn (Function.update (Function.update x u false) v false))
                  w.getD (x1 + j) false = w.getD p false) →
              S.card < 7) →
          ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧
          ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1
              (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool),
      ¬x2.Colorable (2 : ℕ) →
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔
        (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨
        ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 →
        ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧
        ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧
          PEqualNP.MetaComplexity.HasCircuitSize x1
            (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hColor hCub hGirth hIso hEdge hSpec s hSize
  let big (C : Circuit) (u v : Fin n) (S : Finset ℕ) : Prop :=
    FanInTwo C ∧ C.size ≤ s ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) ∧
      G.Adj u v ∧ 7 ≤ S.card ∧ (∀ j ∈ S, j < C.size) ∧
      ∀ j ∈ S, ∃ p : ℕ, (p < n + j ∨ n + C.size ≤ p) ∧
        ∀ x : Fin n → Bool,
          let w := C.wires (List.ofFn (Function.update (Function.update x u false) v false))
          w.getD (n + j) false = w.getD p false
  by_cases hCase : ∃ C u v S, big C u v S
  · obtain ⟨C, u, v, S, hFan, hBound, hEval, huv, hCard, hRange, hAlias⟩ := hCase
    obtain ⟨D, hDFan, hDBound, hDEval⟩ := eraseAliases n C u v S hFan hRange hAlias
    have hCardBound : S.card ≤ C.size := by
      simpa using Finset.card_le_card (show S ⊆ Finset.range C.size from
        fun j hj => Finset.mem_range.mpr (hRange j hj))
    refine ⟨u, v, hIso u v huv, hIso v u huv.symm, huv, C.size - S.card, by omega,
      D, hDFan, hDBound, fun x => (hDEval x).trans (hEval _)⟩
  · refine sparse n G A f hColor hCub hGirth hIso hEdge hSpec s hSize ?_
    intro C hFan hBound hEval u v huv S hRange hAlias
    by_contra! hCard
    exact hCase ⟨C, u, v, S, hFan, hBound, hEval, huv, hCard, hRange, hAlias⟩
