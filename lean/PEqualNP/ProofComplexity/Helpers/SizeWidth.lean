import PEqualNP.ProofComplexity.Helpers.SizeWidth1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Short resolution refutations give narrow ones: the choice of parameters

With `n` variables and a refutation of `S ≥ 2` lines, take the fatness threshold `d` and the
exponent `b` both equal to `t = ⌊√(2 n ln S)⌋ + 1`. Then `S (1 - t / 2n) ^ t < 1`, so the
counting induction `main` of `SizeWidth1` gives width `k + 2 t ≤ k + 8 √(n ln S)`.
-/

namespace PEqualNP.ProofComplexity.Helpers.SizeWidth

open PEqualNP.ProofComplexity

theorem params (N S : ℕ) (hN : 1 ≤ N) (hS : 2 ≤ S) :
    ∃ t : ℕ, S * (2 * N - t) ^ t < (2 * N) ^ t ∧
      (2 * t : ℝ) ≤ 8 * Real.sqrt ((N : ℝ) * Real.log (S : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hSpos : (0 : ℝ) < S := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog : (0.69 : ℝ) < Real.log S :=
    lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hSr)
  set x : ℝ := (N : ℝ) * Real.log (S : ℝ) with hx
  have hx69 : (0.69 : ℝ) < x := by rw [hx]; nlinarith
  have hx0 : 0 ≤ x := by linarith
  set s : ℝ := Real.sqrt x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hshalf : (1 : ℝ) ≤ 2 * s := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  set r : ℝ := Real.sqrt (2 * x) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
  have hrs : r ≤ 2 * s := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  refine ⟨⌊r⌋₊ + 1, ?_, ?_⟩
  · set t : ℕ := ⌊r⌋₊ + 1 with ht
    have htr : r < (t : ℝ) := by
      rw [ht]; push_cast; exact Nat.lt_floor_add_one r
    have ht2 : 2 * x < (t : ℝ) ^ 2 := by nlinarith
    have ht1 : 1 ≤ t := by omega
    by_cases hle : 2 * N ≤ t
    · have h0 : 2 * N - t = 0 := by omega
      rw [h0, zero_pow (by omega), mul_zero]
      exact Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
    · push_neg at hle
      have hle' : t ≤ 2 * N := hle.le
      have hMpos : (0 : ℝ) < 2 * (N : ℝ) := by linarith
      have hreal : (S : ℝ) * (2 * (N : ℝ) - t) ^ t < (2 * (N : ℝ)) ^ t := by
        have htM : (t : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hle'
        have h1 : 2 * (N : ℝ) - t ≤ 2 * (N : ℝ) * Real.exp (-((t : ℝ) / (2 * (N : ℝ)))) := by
          have := Real.add_one_le_exp (-((t : ℝ) / (2 * (N : ℝ))))
          have h2 : 2 * (N : ℝ) * (-((t : ℝ) / (2 * (N : ℝ))) + 1) = 2 * (N : ℝ) - t := by
            field_simp
            ring
          rw [← h2]
          exact mul_le_mul_of_nonneg_left this hMpos.le
        have h3 : (2 * (N : ℝ) - t) ^ t ≤
            (2 * (N : ℝ)) ^ t * Real.exp (-((t : ℝ) / (2 * (N : ℝ)))) ^ t := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by linarith) h1 t
        have h4 : Real.exp (-((t : ℝ) / (2 * (N : ℝ)))) ^ t < (S : ℝ)⁻¹ := by
          rw [← Real.exp_nat_mul, ← Real.exp_log hSpos, ← Real.exp_neg, Real.exp_lt_exp]
          have h5 : Real.log S < (t : ℝ) * ((t : ℝ) / (2 * (N : ℝ))) := by
            rw [← mul_div_assoc, lt_div_iff₀ hMpos]
            have : Real.log (S : ℝ) * (2 * (N : ℝ)) = 2 * x := by rw [hx]; ring
            rw [this]
            nlinarith
          linarith
        have hMt : (0 : ℝ) < (2 * (N : ℝ)) ^ t := pow_pos hMpos t
        calc (S : ℝ) * (2 * (N : ℝ) - t) ^ t
            ≤ (S : ℝ) * ((2 * (N : ℝ)) ^ t * Real.exp (-((t : ℝ) / (2 * (N : ℝ)))) ^ t) :=
              mul_le_mul_of_nonneg_left h3 hSpos.le
          _ < (S : ℝ) * ((2 * (N : ℝ)) ^ t * (S : ℝ)⁻¹) :=
              mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h4 hMt) hSpos
          _ = (2 * (N : ℝ)) ^ t := by field_simp
      have hcast : ((S * (2 * N - t) ^ t : ℕ) : ℝ) < (((2 * N) ^ t : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hle']
        exact hreal
      exact_mod_cast hcast
  · have hfl : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
    push_cast
    linarith

/-- Ben-Sasson and Wigderson: a resolution refutation of `S` lines of a formula with clauses
of at most `k` literals over `n` variables gives one of width `k + 8 √(n ln S)`. -/
theorem bsw : ∃ c : ℝ, ∀ (V : Type) [DecidableEq V] [Fintype V] (F : Set (Clause V))
    (π : List (Clause V)) (k : ℕ), IsRefutation F π → (∀ C ∈ F, C.card ≤ k) →
    ∃ π' : List (Clause V), IsRefutation F π' ∧ ∀ C ∈ π',
      (C.card : ℝ) ≤ (k : ℝ) + c * Real.sqrt ((Fintype.card V : ℝ) * Real.log (π.length : ℝ)) := by
  refine ⟨8, ?_⟩
  intro V _ _ F π k hπ hk
  have hnn : ∀ y : ℝ, (0 : ℝ) ≤ (k : ℝ) + 8 * Real.sqrt y := fun y =>
    add_nonneg (Nat.cast_nonneg k) (mul_nonneg (by norm_num) (Real.sqrt_nonneg y))
  by_cases hN : Fintype.card V = 0
  · -- no variables: every clause is empty
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 hN
    refine ⟨π, hπ, ?_⟩
    intro C _
    rw [Finset.eq_empty_of_isEmpty C]
    simpa using hnn _
  by_cases hS : π.length < 2
  · -- one line: it is the empty clause
    refine ⟨π, hπ, ?_⟩
    intro C hC
    have hlen : π.length = 1 := by
      have := List.length_pos_of_mem hπ.2
      omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
    have ha : (∅ : Clause V) = a := by simpa using hπ.2
    have hCa : C = a := by simpa using hC
    rw [hCa, ← ha]
    simpa using hnn _
  · push_neg at hS
    obtain ⟨t, ht1, ht2⟩ := params (Fintype.card V) π.length (Nat.pos_of_ne_zero hN) hS
    have hcard : (Finset.univ : Finset (Literal V)).card ≤ 2 * Fintype.card V := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]; omega
    have hfat : fat t π * (2 * Fintype.card V - t) ^ t < (2 * Fintype.card V) ^ t :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (fat_le_length t π)) ht1
    have hder := main (2 * Fintype.card V) t k (2 * Fintype.card V) Finset.univ F π t hcard
      hcard hk (SDer.of_derivation hπ.1) hπ.2 (fun C _ => Finset.subset_univ C) hfat
    obtain ⟨π', hπ', hemp', hw⟩ := hder.toList
    refine ⟨π', ⟨hπ', hemp'⟩, ?_⟩
    intro C hC
    have h1 : ((C.card : ℕ) : ℝ) ≤ ((t + t + k : ℕ) : ℝ) := by exact_mod_cast hw C hC
    push_cast at h1
    linarith

end PEqualNP.ProofComplexity.Helpers.SizeWidth
