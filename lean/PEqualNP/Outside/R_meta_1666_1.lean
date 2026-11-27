import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1666_1
    (normalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) →
    C.size ≤ 15 → (∃ x : Fin 9 → Bool, C.eval (List.ofFn x) = true) →
    (∀ i : Fin 9, C.eval (List.ofFn (fun k : Fin 9 => decide (k = i))) = false) →
    ∃ gates : List PEqualNP.CircuitLowerBounds.Gate, gates.length = 15 ∧
      gates.head? = some ⟨.not, [4]⟩ ∧ (∀ j : Fin gates.length,
        (∃ a b : ℕ, a ≤ b ∧ b ≤ 9 + j.val ∧
          (gates.get j = ⟨.and, [a,b]⟩ ∨ gates.get j = ⟨.or, [a,b]⟩)) ∨
        (∃ a : ℕ, a ≤ 9 + j.val ∧ gates.get j = ⟨.not, [a]⟩)) ∧
      ∀ x : Fin 9 → Bool, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates,23⟩ (List.ofFn x)) = C.eval (List.ofFn x))
    (exclude : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate, gates.length = 15 →
    gates.head? = some ⟨.not, [4]⟩ → (∀ j : Fin gates.length,
        (∃ a b : ℕ, a ≤ b ∧ b ≤ 9 + j.val ∧
          (gates.get j = ⟨.and, [a,b]⟩ ∨ gates.get j = ⟨.or, [a,b]⟩)) ∨
        (∃ a : ℕ, a ≤ 9 + j.val ∧ gates.get j = ⟨.not, [a]⟩)) →
    ∃ x : Fin 9 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates,23⟩ (List.ofFn x) ≠
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hfun
  by_contra! hsmall
  have value (x : Fin 9 → Bool) : C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x := congrFun hfun x
  have hp : ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) = true := by
    refine ⟨fun i => decide (i = 0 ∨ i = 1), ?_⟩
    rw [value]
    decide
  have hs (i : Fin 9) : C.eval (List.ofFn (fun k : Fin 9 => decide (k = i))) = false := by
    rw [value]
    fin_cases i <;> decide
  obtain ⟨gs, hlen, hhead, hform, heq⟩ := normalize C hfan hfirst (by omega) hp hs
  obtain ⟨x, hx⟩ := exclude gs hlen hhead hform
  exact hx ((heq x).trans (value x))
