import PEqualNP.MetaComplexity.Helpers.LocalCore
import PEqualNP.MetaComplexity.Helpers.Coding
import PEqualNP.MetaComplexity.Helpers.LocalFormat

/-!
# The finite form of the local reduction chain

Helper for `L-meta-032`. If the table on the all-false input has a consistent circuit of size
`B`, the size field there is below `B`, and the bound of the core lemma becomes an inequality in
`n`, `q`, `M`, `B` alone.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalFinite

open PEqualNP.MetaComplexity

/-- The finite form. -/
theorem finite : ∀ (n q M B : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → (∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f B) → 2 * q * (Nat.log 2 M + 2) < n → 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * (B * (B * ((3 * ((Nat.log 2 M + B + 1) * (Nat.log 2 M + B + 1))) ^ (B - 1) * (Nat.log 2 M + B)))) := by
  intro n q M B w hq hloc hlen hcor hsim hn
  obtain ⟨n', s, T, hz, hT, hno, hb⟩ :=
    LocalCore.core_of Coding.parity_cover LocalFormat.formed_of_odd n q M w hq hloc hlen hcor hn
  obtain ⟨f, hc, C, hf, hs, he⟩ := hsim n' s T hz hT
  have hsB : s + 1 ≤ B := by
    by_contra h
    exact hno ⟨f, hc, C, hf, by omega, he⟩
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have hsk : s ≤ k := by omega
  refine hb.trans (Nat.mul_le_mul_left _ ?_)
  rw [Nat.add_sub_cancel]
  have hbase : 3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))
      ≤ 3 * ((Nat.log 2 M + (k + 1) + 1) * (Nat.log 2 M + (k + 1) + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hpos : 0 < 3 * ((Nat.log 2 M + (k + 1) + 1) * (Nat.log 2 M + (k + 1) + 1)) := by
    positivity
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul
    ((Nat.pow_le_pow_left hbase s).trans (Nat.pow_le_pow_right hpos hsk)) (by omega)))

end PEqualNP.MetaComplexity.Helpers.LocalFinite
