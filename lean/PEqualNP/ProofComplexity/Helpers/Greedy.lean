import PEqualNP.ProofComplexity.Helpers.Matching
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Helpers: the greedy argument for Haken's theorem

A refutation of the pigeonhole formula is fixed. For a partial matching `ρ` the clauses of
the refutation that avoid `ρ` and are still wide on the free pigeons and free holes are the
surviving clauses. A free pair that lies in the monotone image of a constant fraction of the
surviving clauses is added to the matching; each such step multiplies the number of surviving
clauses by at most `73 / 81`. After `(n + 1) / 3` steps a surviving clause still exists by the
wide clause lemma, so the refutation has at least `(81 / 73) ^ ((n + 1) / 3)` clauses.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

open Classical in
/-- The clauses of `π` that avoid the matching `ρ` and are wide relative to it. -/
noncomputable def surv {n : ℕ} (π : List (Clause (PVar n))) (w : ℕ) (ρ : Finset (PVar n)) :
    Finset (Clause (PVar n)) :=
  π.toFinset.filter (fun C => (∀ p ∈ ρ, p ∉ mono C) ∧ w ≤ 9 * (monoFree ρ C).card)

theorem mem_surv {n : ℕ} {π : List (Clause (PVar n))} {w : ℕ} {ρ : Finset (PVar n)}
    {C : Clause (PVar n)} :
    C ∈ surv π w ρ ↔ C ∈ π ∧ (∀ p ∈ ρ, p ∉ mono C) ∧ w ≤ 9 * (monoFree ρ C).card := by
  classical
  simp only [surv, Finset.mem_filter, List.mem_toFinset]

theorem surv_card_le {n : ℕ} (π : List (Clause (PVar n))) (w : ℕ) (ρ : Finset (PVar n)) :
    (surv π w ρ).card ≤ π.length := by
  classical
  exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le π)

theorem surv_nonempty {n : ℕ} {π : List (Clause (PVar n))} {w : ℕ} {ρ : Finset (PVar n)}
    (hρ : Valid ρ) (hf : 2 ≤ (freeP ρ).card) (hπ : IsRefutation (PHP (n + 1) n) π)
    (hw : w ≤ 2 * (freeP ρ).card ^ 2) : (surv π w ρ).Nonempty := by
  obtain ⟨C, hC, h1, h2⟩ := exists_wide hρ hf hπ
  exact ⟨C, mem_surv.mpr ⟨hC, h1, hw.trans h2⟩⟩

theorem monoFree_insert_subset {n : ℕ} (ρ : Finset (PVar n)) (i : Fin (n + 1)) (j : Fin n)
    (C : Clause (PVar n)) : monoFree (insert (i, j) ρ) C ⊆ monoFree ρ C := by
  intro q hq
  obtain ⟨hq1, hq2, hq3⟩ := Finset.mem_filter.mp hq
  rw [freeP_insert] at hq2
  exact Finset.mem_filter.mpr
    ⟨hq1, Finset.mem_of_mem_erase hq2, freeH_insert_subset ρ (i, j) hq3⟩

theorem surv_insert_subset {n : ℕ} (π : List (Clause (PVar n))) (w : ℕ) (ρ : Finset (PVar n))
    (i : Fin (n + 1)) (j : Fin n) :
    surv π w (insert (i, j) ρ) ⊆ (surv π w ρ).filter (fun C => ¬ (i, j) ∈ mono C) := by
  intro C hC
  obtain ⟨h1, h2, h3⟩ := mem_surv.mp hC
  refine Finset.mem_filter.mpr ⟨mem_surv.mpr ⟨h1, ?_, ?_⟩, h2 _ (Finset.mem_insert_self _ _)⟩
  · exact fun p hp => h2 p (Finset.mem_insert_of_mem hp)
  · exact h3.trans (Nat.mul_le_mul_left 9 (Finset.card_le_card (monoFree_insert_subset ρ i j C)))

/-- Double counting of the pairs (clause, free pair in its monotone image). -/
theorem sum_monoFree {n : ℕ} (L : Finset (Clause (PVar n))) (ρ : Finset (PVar n)) :
    ∑ C ∈ L, (monoFree ρ C).card
      = ∑ p ∈ freeP ρ ×ˢ freeH ρ, (L.filter (fun C => p ∈ mono C)).card := by
  have h1 : ∀ C : Clause (PVar n), (monoFree ρ C).card
      = ∑ p ∈ freeP ρ ×ˢ freeH ρ, if p ∈ mono C then 1 else 0 := by
    intro C
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp only [monoFree, Finset.mem_filter, Finset.mem_product]
    tauto
  simp_rw [h1, Finset.card_filter]
  exact Finset.sum_comm

/-- One greedy step: some free pair kills at least an `8 / 81` fraction of the surviving
clauses. -/
theorem greedy_step {n w : ℕ} {π : List (Clause (PVar n))} {ρ : Finset (PVar n)}
    (hne : (surv π w ρ).Nonempty) (hw : 8 * (n + 1) ^ 2 ≤ 9 * w) :
    ∃ i ∈ freeP ρ, ∃ j ∈ freeH ρ,
      81 * (surv π w (insert (i, j) ρ)).card ≤ 73 * (surv π w ρ).card := by
  have hwpos : 0 < w := by
    have : 0 < (n + 1) ^ 2 := by positivity
    omega
  obtain ⟨C0, hC0⟩ := hne
  have hPne : (freeP ρ ×ˢ freeH ρ).Nonempty := by
    have h3 := (mem_surv.mp hC0).2.2
    have hpos : 0 < (monoFree ρ C0).card := by omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
    obtain ⟨-, hq2, hq3⟩ := Finset.mem_filter.mp hq
    exact ⟨q, Finset.mem_product.mpr ⟨hq2, hq3⟩⟩
  obtain ⟨p, hpP, hmax⟩ := Finset.exists_max_image (freeP ρ ×ˢ freeH ρ)
    (fun p => ((surv π w ρ).filter (fun C => p ∈ mono C)).card) hPne
  obtain ⟨i, j⟩ := p
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hpP
  refine ⟨i, hi, j, hj, ?_⟩
  have hsum : ∑ C ∈ surv π w ρ, (monoFree ρ C).card
      ≤ (freeP ρ ×ˢ freeH ρ).card * ((surv π w ρ).filter (fun C => (i, j) ∈ mono C)).card := by
    rw [sum_monoFree]
    have := Finset.sum_le_card_nsmul (freeP ρ ×ˢ freeH ρ)
      (fun p => ((surv π w ρ).filter (fun C => p ∈ mono C)).card) _ hmax
    simpa [smul_eq_mul] using this
  have hlow : (surv π w ρ).card * w ≤ 9 * ∑ C ∈ surv π w ρ, (monoFree ρ C).card := by
    rw [Finset.mul_sum]
    have := Finset.card_nsmul_le_sum (surv π w ρ) (fun C => 9 * (monoFree ρ C).card) w
      (fun C hC => (mem_surv.mp hC).2.2)
    simpa [smul_eq_mul] using this
  have hP : (freeP ρ ×ˢ freeH ρ).card ≤ (n + 1) ^ 2 := by
    rw [Finset.card_product]
    have h1 : (freeP ρ).card ≤ n + 1 := by
      simpa using Finset.card_le_univ (freeP ρ)
    have h2 : (freeH ρ).card ≤ n + 1 := by
      have : (freeH ρ).card ≤ n := by simpa using Finset.card_le_univ (freeH ρ)
      omega
    rw [pow_two]
    exact Nat.mul_le_mul h1 h2
  have hsub := Finset.card_le_card (surv_insert_subset π w ρ i j)
  have hsplit := Finset.card_filter_add_card_filter_not (s := surv π w ρ)
    (fun C => (i, j) ∈ mono C)
  generalize ((surv π w ρ).filter (fun C => (i, j) ∈ mono C)).card = c at hsum hsplit
  generalize ((surv π w ρ).filter (fun C => ¬ (i, j) ∈ mono C)).card = c' at hsub hsplit
  generalize (surv π w (insert (i, j) ρ)).card = l' at hsub ⊢
  generalize (surv π w ρ).card = l at hsum hlow hsplit ⊢
  generalize ∑ C ∈ surv π w ρ, (monoFree ρ C).card = S at hsum hlow
  generalize (freeP ρ ×ˢ freeH ρ).card = P at hsum hP
  have hM : 0 < (n + 1) ^ 2 := by positivity
  generalize (n + 1) ^ 2 = M at hw hP hM
  have h8 : 8 * l ≤ 81 * c := by
    have e1 : M * (8 * l) ≤ M * (81 * c) := by
      calc M * (8 * l) = l * (8 * M) := by ring
        _ ≤ l * (9 * w) := Nat.mul_le_mul_left l hw
        _ = 9 * (l * w) := by ring
        _ ≤ 9 * (9 * S) := Nat.mul_le_mul_left 9 hlow
        _ ≤ 9 * (9 * (P * c)) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left 9 hsum)
        _ ≤ 9 * (9 * (M * c)) :=
          Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left 9 (Nat.mul_le_mul_right c hP))
        _ = M * (81 * c) := by ring
    exact Nat.le_of_mul_le_mul_left e1 hM
  omega

/-- The greedy induction: after `d` steps there is a valid matching with `n + 1 - d` free
pigeons and at most a `(73 / 81) ^ d` fraction of the clauses surviving. -/
theorem greedy {n : ℕ} (hn : 1 ≤ n) {π : List (Clause (PVar n))}
    (hπ : IsRefutation (PHP (n + 1) n) π) :
    ∀ d, d ≤ (n + 1) / 3 → ∃ ρ : Finset (PVar n), Valid ρ ∧ (freeP ρ).card = n + 1 - d ∧
      81 ^ d * (surv π (2 * (n + 1 - (n + 1) / 3) ^ 2) ρ).card ≤ 73 ^ d * π.length := by
  have hw : 8 * (n + 1) ^ 2 ≤ 9 * (2 * (n + 1 - (n + 1) / 3) ^ 2) := by
    have h1 : 2 * (n + 1) ≤ 3 * (n + 1 - (n + 1) / 3) := by omega
    have h2 := Nat.pow_le_pow_left h1 2
    rw [mul_pow, mul_pow] at h2
    omega
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨∅, valid_empty, ?_, ?_⟩
    · rw [freeP_empty, Finset.card_univ, Fintype.card_fin]; rfl
    · simpa using surv_card_le π _ ∅
  | succ d ih =>
    intro hd
    obtain ⟨ρ, hρ, hcard, hbound⟩ := ih (by omega)
    have hne : (surv π (2 * (n + 1 - (n + 1) / 3) ^ 2) ρ).Nonempty := by
      refine surv_nonempty hρ (by omega) hπ ?_
      rw [hcard]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)
    obtain ⟨i, hi, j, hj, hstep⟩ := greedy_step hne hw
    refine ⟨insert (i, j) ρ, valid_insert hρ hi hj, ?_, ?_⟩
    · rw [freeP_insert, Finset.card_erase_of_mem hi, hcard]; omega
    · calc 81 ^ (d + 1) * (surv π _ (insert (i, j) ρ)).card
          = 81 ^ d * (81 * (surv π _ (insert (i, j) ρ)).card) := by ring
        _ ≤ 81 ^ d * (73 * (surv π _ ρ).card) := Nat.mul_le_mul_left _ hstep
        _ = 73 * (81 ^ d * (surv π _ ρ).card) := by ring
        _ ≤ 73 * (73 ^ d * π.length) := Nat.mul_le_mul_left 73 hbound
        _ = 73 ^ (d + 1) * π.length := by ring

/-- The size bound in natural numbers. -/
theorem greedy_bound {n : ℕ} (hn : 1 ≤ n) {π : List (Clause (PVar n))}
    (hπ : IsRefutation (PHP (n + 1) n) π) :
    81 ^ ((n + 1) / 3) ≤ 73 ^ ((n + 1) / 3) * π.length := by
  obtain ⟨ρ, hρ, hcard, hbound⟩ := greedy hn hπ ((n + 1) / 3) le_rfl
  have hne : (surv π (2 * (n + 1 - (n + 1) / 3) ^ 2) ρ).Nonempty := by
    refine surv_nonempty hρ (by omega) hπ ?_
    rw [hcard]
  have hpos : 1 ≤ (surv π (2 * (n + 1 - (n + 1) / 3) ^ 2) ρ).card := Finset.card_pos.mpr hne
  calc 81 ^ ((n + 1) / 3) = 81 ^ ((n + 1) / 3) * 1 := (mul_one _).symm
    _ ≤ 81 ^ ((n + 1) / 3) * (surv π (2 * (n + 1 - (n + 1) / 3) ^ 2) ρ).card :=
      Nat.mul_le_mul_left _ hpos
    _ ≤ _ := hbound

/-- With at least one hole, a refutation of the pigeonhole formula has at least two lines. -/
theorem two_le_length {n : ℕ} (hn : 1 ≤ n) {π : List (Clause (PVar n))}
    (hπ : IsRefutation (PHP (n + 1) n) π) : 2 ≤ π.length := by
  obtain ⟨hd, he⟩ := hπ
  match π, hd, he with
  | [], _, he => simp at he
  | [C], hd, he =>
    have hC0 : C = ∅ := (List.mem_singleton.mp he).symm
    subst hC0
    cases hd with
    | ax _ hC =>
      rcases hC with ⟨i, hi⟩ | ⟨i, i', j, _, h⟩
      · have hmem : ((i, (⟨0, hn⟩ : Fin n)), true) ∈ (∅ : Clause (PVar n)) := by
          rw [hi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        simp at hmem
      · have hmem : ((i, j), false) ∈ (∅ : Clause (PVar n)) := by
          rw [h]; simp
        simp at hmem
    | res _ hC _ _ => simp at hC
  | _ :: _ :: _, _, _ => simp

/-- The size bound in the form used for the real exponent. -/
theorem two_pow_le {n : ℕ} {π : List (Clause (PVar n))}
    (hπ : IsRefutation (PHP (n + 1) n) π) : 2 ^ n ≤ π.length ^ 42 := by
  have h1 : 1 ≤ π.length := List.length_pos_of_mem hπ.2
  rcases Nat.lt_or_ge n 2 with h | h
  · have hcase : n = 0 ∨ n = 1 := by omega
    rcases hcase with rfl | rfl
    · simpa using Nat.one_le_pow 42 _ h1
    · have h2 := two_le_length le_rfl hπ
      calc 2 ^ 1 = 2 := by norm_num
        _ ≤ π.length := h2
        _ ≤ π.length ^ 42 := Nat.le_self_pow (by norm_num) _
  · have hD := greedy_bound (by omega) hπ
    have h6 : n ≤ 6 * ((n + 1) / 3) := by omega
    generalize (n + 1) / 3 = D at hD h6
    have h7 : 73 ^ (7 * D) * 2 ^ D ≤ 73 ^ (7 * D) * π.length ^ 7 := by
      calc 73 ^ (7 * D) * 2 ^ D = (2 * 73 ^ 7) ^ D := by rw [mul_pow, ← pow_mul, mul_comm]
        _ ≤ (81 ^ 7) ^ D := Nat.pow_le_pow_left (by norm_num) D
        _ = (81 ^ D) ^ 7 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (73 ^ D * π.length) ^ 7 := Nat.pow_le_pow_left hD 7
        _ = 73 ^ (7 * D) * π.length ^ 7 := by rw [mul_pow, ← pow_mul, mul_comm D 7]
    have h8 : 2 ^ D ≤ π.length ^ 7 := Nat.le_of_mul_le_mul_left h7 (by positivity)
    calc 2 ^ n ≤ 2 ^ (6 * D) := Nat.pow_le_pow_right (by norm_num) h6
      _ = (2 ^ D) ^ 6 := by rw [← pow_mul, mul_comm]
      _ ≤ (π.length ^ 7) ^ 6 := Nat.pow_le_pow_left h8 6
      _ = π.length ^ 42 := by rw [← pow_mul]

/-- Taking forty-second roots. -/
theorem real_bound {n l : ℕ} (h : 2 ^ n ≤ l ^ 42) :
    (2 : ℝ) ^ ((1 / 42 : ℝ) * (n : ℝ)) ≤ (l : ℝ) := by
  have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hcast : (2 : ℝ) ^ n ≤ (l : ℝ) ^ 42 := by exact_mod_cast h
  have e : (1 / 42 : ℝ) = (((42 : ℕ) : ℝ))⁻¹ := by norm_num
  calc (2 : ℝ) ^ ((1 / 42 : ℝ) * (n : ℝ))
      = ((2 : ℝ) ^ (n : ℝ)) ^ (1 / 42 : ℝ) := by
        rw [mul_comm, Real.rpow_mul (by norm_num)]
    _ = ((2 : ℝ) ^ n) ^ (1 / 42 : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ ((l : ℝ) ^ 42) ^ (1 / 42 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hcast (by norm_num)
    _ = (l : ℝ) := by rw [e]; exact Real.pow_rpow_inv_natCast hl (by norm_num)

end PEqualNP.ProofComplexity.Helpers
