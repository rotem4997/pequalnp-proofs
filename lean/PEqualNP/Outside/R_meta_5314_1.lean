import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5314_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (10 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       ∀ (x4 : Fin (5 : ℕ) → ℕ),         ∀ x5 ∈ [(2147483648 : ℕ), (2155905024 : ℕ), (2290122880 : ℕ), (2290649216 : ℕ), (2827520136 : ℕ), (2829625344 : ℕ), (2829625480 : ℕ), (2860548224 : ℕ), (2863179944 : ℕ), (2863311528 : ℕ), (3937053354 : ℕ), (3941263872 : ℕ)],           have x7 : ℕ → Bool → Bool := fun (x7 : ℕ) (x8 : Bool) => x5.testBit (BitVec.ofBoolListLE (List.ofFn fun (x9 : Fin (5 : ℕ)) => (Bool.true :: x1.wires ((List.ofFn fun (x10 : Fin (9 : ℕ)) => x7.testBit ↑x10) ++ [x8])).getD (x4 x9) Bool.false)).toNat;           have x8 : ℕ → Bool := fun (x8 : ℕ) => x7 x8 (x8.testBit (0 : ℕ) || x8.testBit (3 : ℕ));           ∀ x9 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], ∀ x11 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x7 x9 Bool.false = Bool.false → x7 x11 Bool.true = Bool.true → (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x8 x15 = Bool.true) → ¬∀ x16 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x8 x16 = Bool.false)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (10 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       ∀ (x4 : Fin (5 : ℕ) → ℕ),         ∀ x5 ∈ [(3941264042 : ℕ), (4008372970 : ℕ), (4008636128 : ℕ), (4008636138 : ℕ), (4169697416 : ℕ), (4177066120 : ℕ), (4277071598 : ℕ), (4278124202 : ℕ), (4278124270 : ℕ), (4293585642 : ℕ), (4294901502 : ℕ), (4294967294 : ℕ)],           have x7 : ℕ → Bool → Bool := fun (x7 : ℕ) (x8 : Bool) => x5.testBit (BitVec.ofBoolListLE (List.ofFn fun (x9 : Fin (5 : ℕ)) => (Bool.true :: x1.wires ((List.ofFn fun (x10 : Fin (9 : ℕ)) => x7.testBit ↑x10) ++ [x8])).getD (x4 x9) Bool.false)).toNat;           have x8 : ℕ → Bool := fun (x8 : ℕ) => x7 x8 (x8.testBit (0 : ℕ) || x8.testBit (3 : ℕ));           ∀ x9 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], ∀ x11 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x7 x9 Bool.false = Bool.false → x7 x11 Bool.true = Bool.true → (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x8 x15 = Bool.true) → ¬∀ x16 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x8 x16 = Bool.false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (10 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       ∀ (x4 : Fin (5 : ℕ) → ℕ),         ∀ x5 ∈ [(2147483648 : ℕ), (2155905024 : ℕ), (2290122880 : ℕ), (2290649216 : ℕ), (2827520136 : ℕ), (2829625344 : ℕ), (2829625480 : ℕ), (2860548224 : ℕ), (2863179944 : ℕ), (2863311528 : ℕ), (3937053354 : ℕ), (3941263872 : ℕ), (3941264042 : ℕ), (4008372970 : ℕ), (4008636128 : ℕ), (4008636138 : ℕ), (4169697416 : ℕ), (4177066120 : ℕ), (4277071598 : ℕ), (4278124202 : ℕ), (4278124270 : ℕ), (4293585642 : ℕ), (4294901502 : ℕ), (4294967294 : ℕ)],           have x7 : ℕ → Bool → Bool := fun (x7 : ℕ) (x8 : Bool) => x5.testBit (BitVec.ofBoolListLE (List.ofFn fun (x9 : Fin (5 : ℕ)) => (Bool.true :: x1.wires ((List.ofFn fun (x10 : Fin (9 : ℕ)) => x7.testBit ↑x10) ++ [x8])).getD (x4 x9) Bool.false)).toNat;           have x8 : ℕ → Bool := fun (x8 : ℕ) => x7 x8 (x8.testBit (0 : ℕ) || x8.testBit (3 : ℕ));           ∀ x9 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], ∀ x11 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x7 x9 Bool.false = Bool.false → x7 x11 Bool.true = Bool.true → (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x8 x15 = Bool.true) → ¬∀ x16 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x8 x16 = Bool.false := by
  intro x1 hp1 hp2 x4 x5 hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h1 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
  · exact h2 x1 hp1 hp2 x4 x5 (by simp [h])
