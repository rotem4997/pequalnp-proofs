import PEqualNP.MetaComplexity.Helpers.LocalCoreWf
import PEqualNP.MetaComplexity.Helpers.LocalHardPatch

/-!
# Hard tables from local reductions of parity

Corollaries of `LocalCoreWf.core_wf` (`L-meta-036`).

* `translate`: the conclusion of `core_wf` holds at every input of even weight, not only at
  the all-false input. Apply `core_wf` to the map `x ↦ w (x xor z)`.
* `size_bound`, `size_bound_even`, `linear_bound`: the counting inequality solved for the size
  bound `s`, in closed form: `(n - 3 q) / (4 q) < (2 s + 3) (log2 M + 3) + log2 q`.

The patching lemma (partial circuit size is Lipschitz in the number of changed entries) is in
`LocalHardPatch`; it uses no locality.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalHard

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- Pointwise exclusive or with an input of even weight keeps the parity of the weight. -/
theorem xor_parity {n : ℕ} (x z : Fin n → Bool)
    (hz : (Finset.univ.filter fun i : Fin n => z i = true).card % 2 = 0) :
    (Finset.univ.filter fun i : Fin n => xor (x i) (z i) = true).card % 2
      = (Finset.univ.filter fun i : Fin n => x i = true).card % 2 := by
  classical
  have hA := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i : Fin n => x i = true) (fun i : Fin n => z i = true)
  have hB := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i : Fin n => z i = true) (fun i : Fin n => x i = true)
  have hC := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i : Fin n => xor (x i) (z i) = true) (fun i : Fin n => x i = true)
  have e1 : ((Finset.univ.filter fun i : Fin n => xor (x i) (z i) = true).filter
      fun i : Fin n => x i = true)
      = ((Finset.univ.filter fun i : Fin n => x i = true).filter fun i : Fin n => ¬ z i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> cases z i <;> simp
  have e2 : ((Finset.univ.filter fun i : Fin n => xor (x i) (z i) = true).filter
      fun i : Fin n => ¬ x i = true)
      = ((Finset.univ.filter fun i : Fin n => z i = true).filter fun i : Fin n => ¬ x i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> cases z i <;> simp
  have e3 : ((Finset.univ.filter fun i : Fin n => x i = true).filter fun i : Fin n => z i = true)
      = ((Finset.univ.filter fun i : Fin n => z i = true).filter fun i : Fin n => x i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> cases z i <;> simp
  rw [e1, e2] at hC
  rw [e3] at hA
  omega

/-- Translation: the conclusion of `core_wf` at every input of even weight. -/
theorem translate : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ z : Fin n → Bool, (Finset.univ.filter fun i : Fin n => z i = true).card % 2 = 0 → ∀ (n' s : ℕ) (T : List (Option Bool)), w z = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧ 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1)))) := by
  intro n q M w hq hloc hlen hcor hn z hz n' s T hw hT
  refine LocalCoreWf.core_wf n q M (fun x => w (fun i => xor (x i) (z i))) hq ?_ (fun x => hlen _)
    ?_ hn n' s T ?_ hT
  · intro j x
    obtain ⟨S, c, h⟩ := hloc j (fun i => xor (x i) (z i))
    refine ⟨S, c, fun y hy => h _ (fun i hi => ?_)⟩
    show xor (y i) (z i) = xor (x i) (z i)
    rw [hy i hi]
  · intro x
    rw [← hcor (fun i => xor (x i) (z i)), xor_parity x z hz]
  · show w (fun i => xor false (z i)) = _
    simp only [Bool.false_xor]
    exact hw

/-- The arithmetic behind the readable bound. -/
theorem solve (D q L s : ℕ) (hs : s + 3 < 2 ^ (L + 1))
    (h : 2 ^ D ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((L + s + 2) * (L + s + 2))) ^ s * (L + s + 1))))) :
    D < (2 * s + 3) * (L + 3) + Nat.log 2 q := by
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  have hq2 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have p1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have p2 : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by ring
  have a1 : s + 1 ≤ 2 ^ (L + 1) := by omega
  have a2 : L + s + 2 ≤ 2 ^ (L + 2) := by omega
  have a3 : L + s + 1 ≤ 2 ^ (L + 2) := by omega
  have a4 : 3 * ((L + s + 2) * (L + s + 2)) ≤ 2 ^ (2 * L + 6) := by
    have := Nat.mul_le_mul a2 a2
    have e : (2 : ℕ) ^ (2 * L + 6) = 4 * (2 ^ (L + 2) * 2 ^ (L + 2)) := by ring
    rw [e]
    omega
  have a5 : 8 * q < 2 ^ (Nat.log 2 q + 4) := by
    have e : (2 : ℕ) ^ (Nat.log 2 q + 4) = 8 * 2 ^ (Nat.log 2 q + 1) := by ring
    rw [e]
    omega
  have b1 : (s + 1) * ((s + 1) * ((3 * ((L + s + 2) * (L + s + 2))) ^ s * (L + s + 1)))
      ≤ 2 ^ (L + 1) * (2 ^ (L + 1) * ((2 ^ (2 * L + 6)) ^ s * 2 ^ (L + 2))) :=
    Nat.mul_le_mul a1 (Nat.mul_le_mul a1 (Nat.mul_le_mul (Nat.pow_le_pow_left a4 s) a3))
  have b2 : 8 * q * ((s + 1) * ((s + 1) * ((3 * ((L + s + 2) * (L + s + 2))) ^ s * (L + s + 1))))
      < 2 ^ (Nat.log 2 q + 4) * (2 ^ (L + 1) * (2 ^ (L + 1) * ((2 ^ (2 * L + 6)) ^ s * 2 ^ (L + 2)))) :=
    Nat.mul_lt_mul_of_lt_of_le a5 b1 (by positivity)
  have e : 2 ^ (Nat.log 2 q + 4) * (2 ^ (L + 1) * (2 ^ (L + 1) * ((2 ^ (2 * L + 6)) ^ s * 2 ^ (L + 2))))
      = 2 ^ (Nat.log 2 q + 4 + ((L + 1) + ((L + 1) + ((2 * L + 6) * s + (L + 2))))) := by
    rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  rw [e] at b2
  have hD := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h b2)
  have r1 : (2 * s + 3) * (L + 3) = 2 * (L * s) + 6 * s + 3 * L + 9 := by ring
  have r2 : (2 * L + 6) * s = 2 * (L * s) + 6 * s := by ring
  omega

/-- The readable size bound at every input of even weight. -/
theorem size_bound_even : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ z : Fin n → Bool, (Finset.univ.filter fun i : Fin n => z i = true).card % 2 = 0 → ∀ (n' s : ℕ) (T : List (Option Bool)), w z = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧ (n - 3 * q) / (4 * q) < (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  intro n q M w hq hloc hlen hcor hn z hz n' s T hw hT
  obtain ⟨h1, h2⟩ := translate n q M w hq hloc hlen hcor hn z hz n' s T hw hT
  refine ⟨h1, solve _ q (Nat.log 2 M) s ?_ h2⟩
  have hl := hlen z
  rw [hw] at hl
  simp only [List.length_append, List.length_replicate, List.length_cons, LocalCore.length_enc,
    hT] at hl
  have hp : 0 < 2 ^ n' := by positivity
  have hM : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  omega

/-- The readable size bound, in the form of `L-meta-036`: at the all-false input. -/
theorem size_bound : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (n - 3 * q) / (4 * q) < (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  intro n q M w hq hloc hlen hcor hn n' s T hw hT
  exact (size_bound_even n q M w hq hloc hlen hcor hn (fun _ => false) (by simp) n' s T hw hT).2

/-- The same bound with the division cleared: a lower bound on `s` linear in `n / q`. -/
theorem linear_bound : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ z : Fin n → Bool, (Finset.univ.filter fun i : Fin n => z i = true).card % 2 = 0 → ∀ (n' s : ℕ) (T : List (Option Bool)), w z = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → n < 4 * q * ((2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q) + 3 * q := by
  intro n q M w hq hloc hlen hcor hn z hz n' s T hw hT
  have h := (size_bound_even n q M w hq hloc hlen hcor hn z hz n' s T hw hT).2
  obtain ⟨K, hK⟩ : ∃ K, K = (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := ⟨_, rfl⟩
  rw [← hK] at h ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * q := ⟨_, rfl⟩
  rw [← hQ] at h ⊢
  have h2 : n - 3 * q < K * Q := (Nat.div_lt_iff_lt_mul (by omega : 0 < Q)).mp h
  rw [Nat.mul_comm K Q] at h2
  omega

end PEqualNP.MetaComplexity.Helpers.LocalHard
