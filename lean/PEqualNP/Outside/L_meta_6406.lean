import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6406

lemma fin : ∀ n < 1024,
    (∃ m ∈ [(65 : ℕ), (66 : ℕ), (72 : ℕ), (129 : ℕ), (132 : ℕ), (160 : ℕ), (258 : ℕ), (272 : ℕ), (288 : ℕ), (516 : ℕ), (520 : ℕ), (528 : ℕ)], m &&& n = m) ∨
    (∃ M ∈ [(63 : ℕ), (116 : ℕ), (154 : ℕ), (208 : ℕ), (269 : ℕ), (324 : ℕ), (392 : ℕ), (547 : ℕ), (608 : ℕ), (642 : ℕ), (769 : ℕ), (960 : ℕ)], n &&& M = n) := by
  decide +kernel

end PEqualNP.Outside.L_meta_6406

theorem PEqualNP.Outside.L_meta_6406 : ∀ (x1 : Fin (10 : ℕ) → Bool), (∃ x2 ∈ [(65 : ℕ), (66 : ℕ), (72 : ℕ), (129 : ℕ), (132 : ℕ), (160 : ℕ), (258 : ℕ), (272 : ℕ), (288 : ℕ), (516 : ℕ), (520 : ℕ), (528 : ℕ)], ∀ (x3 : Fin (10 : ℕ)), x2.testBit ↑x3 = Bool.true → x1 x3 = Bool.true) ∨ ∃ x2 ∈ [(63 : ℕ), (116 : ℕ), (154 : ℕ), (208 : ℕ), (269 : ℕ), (324 : ℕ), (392 : ℕ), (547 : ℕ), (608 : ℕ), (642 : ℕ), (769 : ℕ), (960 : ℕ)], ∀ (x3 : Fin (10 : ℕ)), x1 x3 = Bool.true → x2.testBit ↑x3 = Bool.true := by
  intro x
  have hlt : Nat.ofBits x < 1024 := by
    have := Nat.ofBits_lt_two_pow x
    simpa using this
  rcases PEqualNP.Outside.L_meta_6406.fin (Nat.ofBits x) hlt with ⟨m, hm, h⟩ | ⟨M, hM, h⟩
  · refine Or.inl ⟨m, hm, fun i hi => ?_⟩
    have h1 : (m &&& Nat.ofBits x).testBit i = m.testBit i := by rw [h]
    rw [Nat.testBit_and, hi, Bool.true_and, Nat.testBit_ofBits_lt _ _ i.isLt] at h1
    exact h1
  · refine Or.inr ⟨M, hM, fun i hi => ?_⟩
    have h1 : (Nat.ofBits x &&& M).testBit i = (Nat.ofBits x).testBit i := by rw [h]
    rw [Nat.testBit_and, Nat.testBit_ofBits_lt _ _ i.isLt] at h1
    have h2 : x ⟨i.val, i.isLt⟩ = true := hi
    rw [h2, Bool.true_and] at h1
    exact h1
