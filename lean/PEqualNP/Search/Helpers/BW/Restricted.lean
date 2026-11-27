import PEqualNP.Search.Helpers.BW.Bridge
import PEqualNP.Search.Helpers.RectConv

/-!
# Helpers: restricted resolution over linear equations for bit pigeonhole (L-lib-091)

Lines of width at most `4 l` with coefficients at most `2 ^ l` convert to rectangle dags with
a blowup of `2 ^ O(l ^ 2)`, which the Beame-Whitmeyer bound still beats.
-/

namespace PEqualNP.Search.Helpers.BW

/-- The conversion blowup is at most `2 ^ (9 + 36 l (l + 1))`. -/
theorem blowup_le (l : ℕ) :
    (8 * (2 * ((2 ^ l + 1) * l) * 2 ^ l + 1) ^ (4 * l)) ^ 3 ≤ 2 ^ (9 + 36 * l * (l + 1)) := by
  have h1 : 2 ^ l + 1 ≤ 2 ^ (l + 1) := by
    have := Nat.one_le_two_pow (n := l); rw [pow_succ]; omega
  have h2 : l ≤ 2 ^ l := (Nat.lt_two_pow_self).le
  have hX : 2 * ((2 ^ l + 1) * l) * 2 ^ l + 1 ≤ 2 ^ (3 * l + 3) := by
    have : 2 * ((2 ^ l + 1) * l) * 2 ^ l ≤ 2 * (2 ^ (l + 1) * 2 ^ l) * 2 ^ l := by
      gcongr
    have e : 2 ^ (3 * l + 3) = 2 * (2 * (2 ^ (l + 1) * 2 ^ l) * 2 ^ l) := by
      rw [← pow_add, ← pow_succ', ← pow_add, ← pow_succ']; congr 1; ring
    have : 1 ≤ 2 * (2 ^ (l + 1) * 2 ^ l) * 2 ^ l :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  calc (8 * (2 * ((2 ^ l + 1) * l) * 2 ^ l + 1) ^ (4 * l)) ^ 3
      ≤ (2 ^ 3 * (2 ^ (3 * l + 3)) ^ (4 * l)) ^ 3 := by gcongr; norm_num
    _ = 2 ^ (9 + 36 * l * (l + 1)) := by
      rw [← pow_mul, ← pow_add, ← pow_mul]; congr 1; ring

/-- Some `s` makes `p (2 ^ l)` times the blowup, at `l = 4 s + 4`, smaller than the
Beame-Whitmeyer bound. -/
theorem exists_eval_blowup_lt (p : Polynomial ℕ) : ∃ s : ℕ,
    p.eval (2 ^ (4 * s + 4)) *
      (8 * (2 * ((2 ^ (4 * s + 4) + 1) * (4 * s + 4)) * 2 ^ (4 * s + 4) + 1) ^
        (4 * (4 * s + 4))) ^ 3 < 2 ^ (2 ^ (s - 1) - 1) := by
  set d := p.natDegree
  set C := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i
  set A := 6000 + d + C
  set k := 4 * A
  refine ⟨k + 1, ?_⟩
  set l := 4 * (k + 1) + 4 with hl
  have hA : 1 ≤ A := by omega
  have h2A := two_mul_le_two_pow hA
  have hk4 : 2 ^ k = (2 ^ A) ^ 4 := by rw [← pow_mul, mul_comm]
  have hpow : (2 * A) ^ 4 ≤ 2 ^ k := by rw [hk4]; gcongr
  have hk1 : 12 ≤ k := by omega
  have hl12 : l ≤ 12 * k := by omega
  have hll : l * (l + 1) ≤ 156 * (k * k) := by
    have : l + 1 ≤ 13 * k := by omega
    calc l * (l + 1) ≤ (12 * k) * (13 * k) := Nat.mul_le_mul hl12 this
      _ = 156 * (k * k) := by ring
  have hld : l * d ≤ 12 * k * d := Nat.mul_le_mul_right _ hl12
  have hAk : 5616 * (k * k) + 12 * k * d + C + 10 ≤ A * (k * k) := by
    have e : A * (k * k) = 6000 * (k * k) + d * (k * k) + C * (k * k) := by
      simp only [A]; ring
    have : 12 * k * d ≤ d * (k * k) := by
      calc 12 * k * d = d * (12 * k) := by ring
        _ ≤ d * (k * k) := by gcongr
    have : C ≤ C * (k * k) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
    have : 10 ≤ 384 * (k * k) := by nlinarith
    omega
  have hAk2 : A * (k * k) + 1 < 2 ^ k := by
    have e1 : A * (k * k) = 16 * (A * A * A) := by simp only [k]; ring
    have e2 : (2 * A) ^ 4 = 16 * (A * A * A) * A := by ring
    have : 16 * (A * A * A) * 2 ≤ 16 * (A * A * A) * A := by
      have : 2 ≤ A := by omega
      gcongr
    have : 1 ≤ 16 * (A * A * A) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hexp : C + l * d + (9 + 36 * l * (l + 1)) < 2 ^ (k + 1 - 1) - 1 := by
    simp only [Nat.add_sub_cancel]
    have : 36 * l * (l + 1) = 36 * (l * (l + 1)) := by ring
    omega
  calc p.eval (2 ^ l) * (8 * (2 * ((2 ^ l + 1) * l) * 2 ^ l + 1) ^ (4 * l)) ^ 3
      ≤ (C * (2 ^ l) ^ d) * 2 ^ (9 + 36 * l * (l + 1)) :=
        Nat.mul_le_mul (eval_le_sum_mul p (Nat.one_le_two_pow)) (blowup_le l)
    _ ≤ (2 ^ C * 2 ^ (l * d)) * 2 ^ (9 + 36 * l * (l + 1)) := by
        rw [← pow_mul]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le)
    _ = 2 ^ (C + l * d + (9 + 36 * l * (l + 1))) := by rw [pow_add, pow_add]; ring_nf
    _ < 2 ^ (2 ^ (k + 1 - 1) - 1) := Nat.pow_lt_pow_right (by norm_num) hexp

/-- FINAL: restricted refutations of bit pigeonhole are superpolynomial. -/
theorem restricted_superpoly : ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ l + 1) × Fin l)),
      PEqualNP.Search.IsResLinQRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
      (∀ L ∈ π, L.length ≤ 4 * l ∧ ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ 2 ^ l) →
      p.eval (2 ^ l) < π.length := by
  intro p
  obtain ⟨s, hs⟩ := exists_eval_blowup_lt p
  refine ⟨4 * s + 4, fun π hπ hb => ?_⟩
  obtain ⟨ρ, hρ, hρlen⟩ := PEqualNP.Search.Helpers.resLinQ_to_rectDag
    (fun v : Fin (2 ^ (4 * s + 4) + 1) × Fin (4 * s + 4) => decide (2 * v.2.val < 4 * s + 4))
    _ π (2 ^ (4 * s + 4)) (4 * (4 * s + 4)) hπ hb
  obtain ⟨σ, hσ, hlen⟩ := rectDag_to_adag s hρ
  have hlow := adag_lower' s σ hσ
  simp only [Fintype.card_prod, Fintype.card_fin] at hρlen
  by_contra hcon
  rw [Nat.not_lt] at hcon
  have := Nat.mul_le_mul_right
    ((8 * (2 * ((2 ^ (4 * s + 4) + 1) * (4 * s + 4)) * 2 ^ (4 * s + 4) + 1) ^
        (4 * (4 * s + 4))) ^ 3) hcon
  omega

end PEqualNP.Search.Helpers.BW
