import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3014_2
    (search :
      ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        2 ≤ C.size ∧ C.size ≤ 26 ∧
        (∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val)) = true) ∧
        (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), C.eval (List.ofFn (fun i : Fin 14 => m.testBit i.val)) = false))
    (positive :
      let f (x : Fin 14 → Bool) : Prop :=
        ∃ p l : Fin 14, (14 * p.val + l.val) ∈ ([7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] : List ℕ) ∧
          x p = true ∧ x l = true
      ∀ x : Fin 14 → Bool, f x → (∀ y ≤ x, f y → y = x) →
        ∃ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), (fun i : Fin 14 => m.testBit i.val) = x)
    (negative :
      let f (x : Fin 14 → Bool) : Prop :=
        ∃ p l : Fin 14, (14 * p.val + l.val) ∈ ([7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] : List ℕ) ∧
          x p = true ∧ x l = true
      ∀ x : Fin 14 → Bool, ¬ f x → (∀ y, x ≤ y → ¬ f y → y = x) →
        ∃ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), (fun i : Fin 14 => m.testBit i.val) = x) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  have hedges : ∀ p l : Fin 14, ((p.val, l.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))) ↔
    (14 * p.val + l.val) ∈ ([7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] : List ℕ) := by
    decide +kernel
  obtain ⟨C, hmodel, hnodup, hmin, hmax, hp, hn⟩ := search
  dsimp only
  refine ⟨C, hmodel, hnodup, hmin, hmax, ?_, ?_⟩
  · intro x hx hminimal
    simp only [decide_eq_true_eq, hedges] at hx hminimal
    obtain ⟨m, hm, hrow⟩ := positive x hx hminimal
    rw [← hrow]
    exact hp m hm
  · intro x hx hmaximal
    simp only [decide_eq_false_iff_not, hedges] at hx hmaximal
    obtain ⟨m, hm, hrow⟩ := negative x hx hmaximal
    rw [← hrow]
    exact hn m hm
