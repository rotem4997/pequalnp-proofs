import PEqualNP.Defs
import PEqualNP.Library.Helpers.RRDistinguisher
import PEqualNP.Library.Helpers.RRAssembly
import Mathlib.Tactic

/-!
# Razborov-Rudich links with fan-in-two distinguishers

The prefix-reading circuit built from the circuit simulation keeps the fan-in-two AND, OR and
NOT gates of the simulating circuit, so the distinguisher in the assembly may be required to
have fan-in two.
-/

namespace PEqualNP.Library.Helpers.RRFanInTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.RRDistinguisher PEqualNP.Library.Helpers.RRAssembly

theorem fanInTwo_shift (M N : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    FanInTwo (shiftCircuit M N C) := by
  intro g hg
  simp only [shiftCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hC g0 hg0
  exact ⟨h1, by simpa using h2⟩

theorem linkA2 : (∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3)) → ∀ Q : Language Bool, Q ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ m N : ℕ, 2 ^ m ≤ N → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ c * 2 ^ (d * m) ∧ ∀ T : List Bool, T.length = N → (D.eval T = true ↔ T.take (2 ^ m) ∈ Q) := by
  intro H Q hQ
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 Q).1 hQ
  obtain ⟨c', hc'⟩ := H _ Q hk
  refine ⟨c' * (k + 3) ^ 3, 3 * (k + 1), fun m N hN => ?_⟩
  obtain ⟨C, hgates, hsize, hdec⟩ := hc' (2 ^ m)
  refine ⟨shiftCircuit (2 ^ m) N C, fanInTwo_shift _ _ C hgates, ?_, fun T hT => ?_⟩
  · have hs : (shiftCircuit (2 ^ m) N C).size = C.size := by
      simp [shiftCircuit, Circuit.size]
    rw [hs]
    calc C.size ≤ c' * ((2 ^ m) ^ k + k + 2 ^ m + 1) ^ 3 := hsize
      _ ≤ c' * ((k + 3) ^ 3 * 2 ^ (3 * (k + 1) * m)) := Nat.mul_le_mul_left _ (arith k m)
      _ = c' * (k + 3) ^ 3 * 2 ^ (3 * (k + 1) * m) := by ring
  · rw [eval_shift (2 ^ m) N C T hN hT]
    exact hdec _ (by simp [hT, hN])

theorem linkC2 : (∀ Q : Language Bool, Q ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ m N : ℕ, 2 ^ m ≤ N → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ c * 2 ^ (d * m) ∧ ∀ T : List Bool, T.length = N → (D.eval T = true ↔ T.take (2 ^ m) ∈ Q)) → (∀ F : Language Bool, F ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ n m : ℕ, m ≤ n → ∀ s : List Bool, s.length = n → ∃ f : (Fin m → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize m f (c * (n + 1) ^ d) ∧ ∀ x : Fin m → Bool, (f x = true ↔ s ++ (List.range n).map (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j) ∈ F)) → (∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) → ¬ ∃ Q : Language Bool, PEqualNP.MetaComplexity.Large Q ∧ Q ∈ PEqualNP.Library.P ∧ ∀ k : ℕ, PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k + k) := by
  intro hA hB ⟨F, k, hk, hF, n₀, hPRF⟩ ⟨Q, ⟨cL, hL⟩, hQ, hU⟩
  obtain ⟨cA, dA, hAQ⟩ := hA Q hQ
  obtain ⟨cB, dB, hBF⟩ := hB F hF
  obtain ⟨n₁, hn₁⟩ := hU (dB + 1)
  set R := k * (dA + cL + 2) with hRdef
  set M := n₁ + n₀ + cA + cL + cB * (R + 1) ^ dB + 1 with hMdef
  set n := R * M with hndef
  have hRpos : 0 < R := Nat.mul_pos hk (by omega)
  have hMn : M ≤ n := Nat.le_mul_of_pos_left M hRpos
  have hn0 : n₀ ≤ n := le_trans (by omega) hMn
  have hnk : n / k = (dA + cL + 2) * M := by
    rw [hndef, hRdef, mul_assoc, Nat.mul_div_cancel_left _ hk]
  have hpow : 2 ^ M ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hMn
  obtain ⟨D, hDfan, hDsize, hD⟩ := hAQ M (2 ^ n) hpow
  have hDs : D.size ≤ 2 ^ (n / k) := by
    rw [hnk]
    calc D.size ≤ cA * 2 ^ (dA * M) := hDsize
      _ ≤ 2 ^ M * 2 ^ (dA * M) :=
          Nat.mul_le_mul_right _ (le_of_lt (lt_of_le_of_lt (by omega) M.lt_two_pow_self))
      _ = 2 ^ ((1 + dA) * M) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ ((dA + cL + 2) * M) := Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ (by omega))
  have h := hPRF n hn0 D hDfan hDs
  have hbound : cB * (n + 1) ^ dB ≤ M ^ (dB + 1) + (dB + 1) := by
    have h1 : n + 1 ≤ (R + 1) * M := by
      have : (R + 1) * M = R * M + M := by ring
      omega
    calc cB * (n + 1) ^ dB ≤ cB * ((R + 1) * M) ^ dB :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = cB * (R + 1) ^ dB * M ^ dB := by rw [mul_pow, mul_assoc]
      _ ≤ M * M ^ dB := Nat.mul_le_mul_right _ (by omega)
      _ = M ^ (dB + 1) := by rw [pow_succ, mul_comm]
      _ ≤ M ^ (dB + 1) + (dB + 1) := Nat.le_add_right _ _
  have hS : ∀ s : List Bool, ¬ (s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧
      (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔
        s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true) := by
    rintro s ⟨hs, T, hT, hTF, hDT⟩
    have hQT := (hD T hT).1 hDT
    have hUlen : (T.take (2 ^ M)).length = 2 ^ M := by
      rw [List.length_take, hT]; exact min_eq_left hpow
    obtain ⟨f, hf, hfx⟩ := hBF n M hMn s hs
    have hfeq : f = tableFun M (T.take (2 ^ M)) := by
      funext x
      have hx : tableIndex x < 2 ^ M := tableIndex_lt' x
      have hx' : tableIndex x < 2 ^ n := lt_of_lt_of_le hx hpow
      have hget : (T.take (2 ^ M)).getD (tableIndex x) false = T.getD (tableIndex x) false := by
        simp [List.getD_eq_getElem?_getD, hx]
      unfold tableFun
      rw [hget]
      exact Bool.eq_iff_iff.mpr ((hfx x).trans (hTF _ hx').symm)
    apply hn₁ M (by omega) _ hUlen hQT
    rw [← hfeq]
    obtain ⟨C, hC1, hC2, hC3⟩ := hf
    exact ⟨C, hC1, le_trans hC2 hbound, hC3⟩
  simp only [hS, Set.ofPred_false, Set.ncard_empty] at h
  have hcount := count_lb Q (fun T => D.eval T = true) (2 ^ M) (2 ^ n) hpow hD
  have hLM := hL M
  set r := {T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard with hr
  set a := {T : List Bool | T.length = 2 ^ M ∧ T ∈ Q}.ncard with ha
  have h2 : (r : ℤ) * 2 ^ (n / k) * 2 ^ n < 2 ^ (2 ^ n) * 2 ^ n := by
    rw [Nat.cast_zero, zero_mul, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at h
    linarith
  have h3 : (r : ℤ) * 2 ^ (n / k) < 2 ^ (2 ^ n) :=
    lt_of_mul_lt_mul_right h2 (by positivity)
  have h4 : r * 2 ^ (n / k) < 2 ^ (2 ^ n) := by exact_mod_cast h3
  have hcL : cL * (M + 1) ≤ n / k := by
    rw [hnk]; nlinarith [Nat.zero_le (dA * M), (by omega : cL ≤ M)]
  have h5 : 2 ^ (2 ^ n) ≤ r * 2 ^ (n / k) := by
    calc 2 ^ (2 ^ n) = 2 ^ (2 ^ M) * 2 ^ (2 ^ n - 2 ^ M) := by
          rw [← pow_add, Nat.add_sub_cancel' hpow]
      _ ≤ 2 ^ (cL * (M + 1)) * a * 2 ^ (2 ^ n - 2 ^ M) := Nat.mul_le_mul_right _ hLM
      _ = 2 ^ (cL * (M + 1)) * (a * 2 ^ (2 ^ n - 2 ^ M)) := by rw [mul_assoc]
      _ ≤ 2 ^ (cL * (M + 1)) * r := Nat.mul_le_mul_left _ hcount
      _ ≤ 2 ^ (n / k) * r := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos hcL)
      _ = r * 2 ^ (n / k) := mul_comm _ _
  omega


end PEqualNP.Library.Helpers.RRFanInTwo
