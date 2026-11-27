import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_3014_1
    (core : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.size ≤ 14 ∧
      ∀ y : Fin 10 → Bool, C.eval (List.ofFn y) = true ↔
        ∃ p l : Fin 10, (p.val, l.val) ∈ ([(0,6), (0,7), (1,6), (1,8), (2,7), (2,9), (3,6), (3,9), (4,8), (4,9), (5,7), (5,8)] : List (ℕ × ℕ)) ∧
          y p = true ∧ y l = true)
    (extend : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        2 ≤ D.size ∧ D.size ≤ C.size + 12 ∧
        ∀ x : Fin 14 → Bool,
          D.eval (List.ofFn x) =
            (C.eval (List.ofFn (fun i : Fin 10 =>
                x (([0, 1, 2, 3, 5, 6, 7, 8, 9, 12] : List (Fin 14)).getD i.val 0))) ||
              decide (∃ p l : Fin 14, (p.val, l.val) ∈ ([(0,10), (1,13), (2,13), (3,11), (4,10), (4,11), (4,13), (5,10), (6,11)] : List (ℕ × ℕ)) ∧
                x p = true ∧ x l = true))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  obtain ⟨C, hcModel, hcDistinct, hcSize, hcEval⟩ := core
  obtain ⟨D, hdModel, hdDistinct, hdMin, hdSize, hdEval⟩ := extend C hcModel hcDistinct
  let embed (i : Fin 10) : Fin 14 := ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12] : List (Fin 14)).getD i.val 0
  let inverse (i : Fin 14) : Fin 10 := ([0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 0, 0, 9, 0] : List (Fin 10)).getD i.val 0
  let selected : List ℕ := [7, 8, 9, 12]
  let pairs : List (ℕ × ℕ) := [(0,6), (0,7), (1,6), (1,8), (2,7), (2,9), (3,6), (3,9), (4,8), (4,9), (5,7), (5,8)]
  let rest : List (ℕ × ℕ) := [(0,10), (1,13), (2,13), (3,11), (4,10), (4,11), (4,13), (5,10), (6,11)]
  let full : List (ℕ × ℕ) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
  have forward : ∀ p l : Fin 10, (p.val, l.val) ∈ pairs →
      ((embed p).val, (embed l).val) ∈ full := by decide +kernel
  have outside : ∀ p l : Fin 14, ((p.val, l.val) ∈ rest) ↔
      ((p.val, l.val) ∈ full ∧ l.val ∉ selected) := by decide +kernel
  have backward : ∀ p l : Fin 14, (p.val, l.val) ∈ full ∧ l.val ∈ selected →
      embed (inverse p) = p ∧ embed (inverse l) = l ∧ ((inverse p).val, (inverse l).val) ∈ pairs := by
    decide +kernel
  have eval (x : Fin 14 → Bool) : D.eval (List.ofFn x) =
      decide (∃ p l : Fin 14, (p.val, l.val) ∈ full ∧ x p = true ∧ x l = true) := by
    have hCoreX := hcEval (fun i => x (embed i))
    apply Bool.eq_iff_iff.mpr
    rw [hdEval x, Bool.or_eq_true_iff, hCoreX, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro (⟨p, l, hpl, hp, hl⟩ | ⟨p, l, hpl, hp, hl⟩)
      · exact ⟨embed p, embed l, forward p l hpl, hp, hl⟩
      · exact ⟨p, l, ((outside p l).mp hpl).1, hp, hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      by_cases h : l.val ∈ selected
      · obtain ⟨hp', hl', hPair⟩ := backward p l ⟨hpl, h⟩
        exact Or.inl ⟨inverse p, inverse l, hPair, by simpa only [hp'] using hp,
          by simpa only [hl'] using hl⟩
      · exact Or.inr ⟨p, l, (outside p l).mpr ⟨hpl, h⟩, hp, hl⟩
  refine ⟨D, hdModel, hdDistinct, hdMin, by omega, ?_, ?_⟩
  · intro x hx _
    exact (eval x).trans hx
  · intro x hx _
    exact (eval x).trans hx
