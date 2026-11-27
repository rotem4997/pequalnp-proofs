import PEqualNP.Defs
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Assembly of the Razborov-Rudich argument

From a circuit simulation of polynomial-time languages on truth-table prefixes (`hA`) and
small circuits for the seeded function tables of a polynomial-time language (`hB`), a
pseudorandom function family rules out natural properties that are large, in P, and useful
against every polynomial (Razborov-Rudich 1997, Theorem 4.1).
-/

namespace PEqualNP.Library.Helpers.RRAssembly

open PEqualNP.MetaComplexity

theorem tableIndex_lt' {m : ℕ} (x : Fin m → Bool) : tableIndex x < 2 ^ m := by
  have key : ∀ m : ℕ, ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega
  unfold tableIndex
  calc ∑ i : Fin m, (if x i = true then 2 ^ (i : ℕ) else 0) ≤ ∑ i : Fin m, 2 ^ (i : ℕ) :=
        Finset.sum_le_sum fun i _ => by split <;> simp
    _ < 2 ^ m := by rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) m]; exact key m

theorem ncard_length_eq (L : ℕ) : {l : List Bool | l.length = L}.ncard = 2 ^ L := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card (List.Vector Bool L) = _
  simp

theorem count_lb (Q : Set (List Bool)) (P : List Bool → Prop) (L N : ℕ) (hLN : L ≤ N)
    (hP : ∀ T : List Bool, T.length = N → (P T ↔ T.take L ∈ Q)) :
    {U : List Bool | U.length = L ∧ U ∈ Q}.ncard * 2 ^ (N - L) ≤
      {T : List Bool | T.length = N ∧ P T}.ncard := by
  rw [← ncard_length_eq (N - L), ← Set.ncard_prod]
  have inj : Set.InjOn (fun p : List Bool × List Bool => p.1 ++ p.2)
      ({U : List Bool | U.length = L ∧ U ∈ Q} ×ˢ {l : List Bool | l.length = N - L}) := by
    rintro ⟨U, V⟩ ⟨⟨hU, _⟩, _⟩ ⟨U', V'⟩ ⟨⟨hU', _⟩, _⟩ h
    have := List.append_inj h (hU.trans hU'.symm)
    exact Prod.ext this.1 this.2
  rw [← inj.ncard_image]
  apply Set.ncard_le_ncard _ ((List.finite_length_eq Bool N).subset
    (t := {T : List Bool | T.length = N ∧ P T}) fun _ hT => hT.1)
  rintro _ ⟨⟨U, V⟩, ⟨⟨hU, hUQ⟩, hV⟩, rfl⟩
  have hV' : V.length = N - L := hV
  have hlen : (U ++ V).length = N := by simp [hU, hV']; omega
  refine ⟨hlen, (hP _ hlen).2 ?_⟩
  rw [List.take_left' hU]
  exact hUQ

theorem linkC :
(∀ Q : Language Bool, Q ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ m N : ℕ, 2 ^ m ≤ N → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ c * 2 ^ (d * m) ∧ ∀ T : List Bool, T.length = N → (D.eval T = true ↔ T.take (2 ^ m) ∈ Q)) → (∀ F : Language Bool, F ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ n m : ℕ, m ≤ n → ∀ s : List Bool, s.length = n → ∃ f : (Fin m → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize m f (c * (n + 1) ^ d) ∧ ∀ x : Fin m → Bool, (f x = true ↔ s ++ (List.range n).map (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j) ∈ F)) → (∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) → ¬ ∃ Q : Language Bool, PEqualNP.MetaComplexity.Large Q ∧ Q ∈ PEqualNP.Library.P ∧ ∀ k : ℕ, PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k + k)
 := by
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
  obtain ⟨D, hDsize, hD⟩ := hAQ M (2 ^ n) hpow
  have hDs : D.size ≤ 2 ^ (n / k) := by
    rw [hnk]
    calc D.size ≤ cA * 2 ^ (dA * M) := hDsize
      _ ≤ 2 ^ M * 2 ^ (dA * M) :=
          Nat.mul_le_mul_right _ (le_of_lt (lt_of_le_of_lt (by omega) M.lt_two_pow_self))
      _ = 2 ^ ((1 + dA) * M) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ ((dA + cL + 2) * M) := Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ (by omega))
  have h := hPRF n hn0 D hDs
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

end PEqualNP.Library.Helpers.RRAssembly
