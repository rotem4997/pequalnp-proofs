import Mathlib

/-!
# Small integer weights for linear threshold functions

Every linear threshold function on `s` Boolean inputs is realized by integer weights whose
absolute values sum to at most `(s + 2) ^ (s + 2)` (Muroga, Toda, Takasu 1961, with a cruder
bound than theirs).

Route: the strict separation conditions form a feasible system `R z ≥ 1` in the `s + 1`
unknowns (weights and threshold), with all coefficients in `{0, 1, -1}`.  Starting from any
rational solution we slide along directions orthogonal to the constraints that are already
tight, each time making one more linearly independent constraint tight (either a row of the
system or a coordinate equation `z j = 0`), until `s + 1` linearly independent tight constraints
are collected.  The solution is then the unique solution of a nonsingular square system with
coefficients in `{0, 1, -1}`, and Cramer's rule together with the Leibniz bound on determinants
turns it into an integer solution with entries of absolute value at most `(s + 1)!`.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Matrix

/-- One sliding step: if some constraint is not orthogonal to the direction `v`, we can move
along `v` to make one such constraint tight, without violating any inequality that held. -/
theorem weightBound_step {n : ℕ} {C : Type*} [Fintype C] (a : C → Fin n → ℚ) (β : C → ℚ)
    (z v : Fin n → ℚ) (c0 : C) (hc0 : a c0 ⬝ᵥ v ≠ 0) :
    ∃ (t : ℚ) (c : C), a c ⬝ᵥ v ≠ 0 ∧ a c ⬝ᵥ (z + t • v) = β c ∧
      ∀ c', β c' ≤ a c' ⬝ᵥ z → β c' ≤ a c' ⬝ᵥ (z + t • v) := by
  classical
  set T : C → ℚ := fun c => (β c - a c ⬝ᵥ z) / (a c ⬝ᵥ v) with hT
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun c => a c ⬝ᵥ v ≠ 0) (fun c => |T c|) ⟨c0, by simp [hc0]⟩
  have hcv : a c ⬝ᵥ v ≠ 0 := by simpa using hc
  refine ⟨T c, c, hcv, ?_, ?_⟩
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hT]
    rw [div_mul_cancel₀ _ hcv]
    ring
  · intro c' hc'
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases h0 : a c' ⬝ᵥ v = 0
    · rw [h0]
      simpa using hc'
    · have h1 : |T c| ≤ |T c'| := hmin c' (by simp [h0])
      have h2 : |T c'| * |a c' ⬝ᵥ v| = a c' ⬝ᵥ z - β c' := by
        rw [← abs_mul]
        simp only [hT]
        rw [div_mul_cancel₀ _ h0, abs_sub_comm, abs_of_nonneg (by linarith)]
      have h3 : |T c * (a c' ⬝ᵥ v)| ≤ a c' ⬝ᵥ z - β c' := by
        rw [abs_mul, ← h2]
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have := (abs_le.mp h3).1
      linarith

/-- Collecting `k ≤ n` linearly independent tight constraints while staying feasible. -/
theorem weightBound_basis {n : ℕ} {C : Type*} [Fintype C] (a : C → Fin n → ℚ) (β : C → ℚ)
    (hspan : ∀ v : Fin n → ℚ, v ≠ 0 → ∃ c, a c ⬝ᵥ v ≠ 0)
    (P : C → Prop) (z0 : Fin n → ℚ) (hz0 : ∀ c, P c → β c ≤ a c ⬝ᵥ z0) (k : ℕ) (hk : k ≤ n) :
    ∃ (z : Fin n → ℚ) (ι : Fin k → C), (∀ c, P c → β c ≤ a c ⬝ᵥ z) ∧
      LinearIndependent ℚ (fun i => a (ι i)) ∧ ∀ i, a (ι i) ⬝ᵥ z = β (ι i) := by
  classical
  induction k with
  | zero => exact ⟨z0, Fin.elim0, hz0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨z, ι, hz, hli, htight⟩ := ih (by omega)
    set p := Submodule.span ℚ (Set.range fun i => a (ι i)) with hp
    have hlt : p < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have h1 := finrank_span_eq_card hli
      rw [← hp, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
      omega
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top p hlt
    set v : Fin n → ℚ := fun j => f (fun j' => if j = j' then 1 else 0) with hv
    have hfv : ∀ x, f x = x ⬝ᵥ v := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp [dotProduct, hv]
    have hv0 : v ≠ 0 := by
      intro h
      exact hf0 (LinearMap.ext fun x => by rw [hfv, h]; simp)
    have hker : ∀ i, a (ι i) ⬝ᵥ v = 0 := by
      intro i
      rw [← hfv]
      exact LinearMap.mem_ker.mp (hf (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨c0, hc0⟩ := hspan v hv0
    obtain ⟨t, c, hcv, htc, hfeas⟩ := weightBound_step a β z v c0 hc0
    refine ⟨z + t • v, Fin.cons c ι, fun c' h => hfeas c' (hz c' h), ?_, ?_⟩
    · have hcons : (fun i => a ((Fin.cons c ι : Fin (k + 1) → C) i)) =
          Fin.cons (a c) (fun i => a (ι i)) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [hcons, linearIndependent_finCons]
      refine ⟨hli, fun hmem => hcv ?_⟩
      rw [← hfv]
      exact LinearMap.mem_ker.mp (hf hmem)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using htc
      · simp only [Fin.cons_succ]
        rw [dotProduct_add, dotProduct_smul, hker, htight]
        simp

/-- A feasible system `R z ≥ 1` with coefficients in `{0, 1, -1}` and `n` unknowns has an
integer solution with entries of absolute value at most `n!`. -/
theorem weightBound_integer {n : ℕ} {m : Type*} [Fintype m] (R : m → Fin n → ℤ)
    (hR : ∀ i j, |R i j| ≤ 1) (z0 : Fin n → ℚ)
    (hz0 : ∀ i, (1 : ℚ) ≤ ∑ j, (R i j : ℚ) * z0 j) :
    ∃ N : Fin n → ℤ, (∀ j, |N j| ≤ (n.factorial : ℤ)) ∧ ∀ i, 1 ≤ ∑ j, R i j * N j := by
  classical
  let aZ : m ⊕ Fin n → Fin n → ℤ := Sum.elim R (fun j => Pi.single j 1)
  let βZ : m ⊕ Fin n → ℤ := Sum.elim (fun _ => 1) (fun _ => 0)
  let a : m ⊕ Fin n → Fin n → ℚ := fun c j => (aZ c j : ℚ)
  let β : m ⊕ Fin n → ℚ := fun c => (βZ c : ℚ)
  have haZ : ∀ c j, |aZ c j| ≤ 1 := by
    rintro (i | j) j'
    · exact hR i j'
    · simp only [aZ, Sum.elim_inr, Pi.single_apply]
      split_ifs <;> simp
  have hβZ : ∀ c, |βZ c| ≤ 1 := by
    rintro (i | j) <;> simp [βZ]
  have hspan : ∀ v : Fin n → ℚ, v ≠ 0 → ∃ c, a c ⬝ᵥ v ≠ 0 := by
    intro v hv
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    refine ⟨Sum.inr j, ?_⟩
    simpa [a, aZ, dotProduct, Pi.single_apply] using hj
  obtain ⟨z, ι, hz, hli, htight⟩ := weightBound_basis a β hspan (fun c => c.isLeft = true) z0
    (by
      rintro (i | j) h
      · simpa [a, aZ, β, βZ, dotProduct] using hz0 i
      · simp at h) n le_rfl
  let MZ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i => aZ (ι i)
  let bZ : Fin n → ℤ := fun i => βZ (ι i)
  let M : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i => a (ι i)
  have hMmap : M = MZ.map (Int.castRingHom ℚ) := by
    ext i j
    simp [M, MZ, a]
  have hMunit : IsUnit M := by
    rw [← Matrix.linearIndependent_row_iff_isUnit]
    exact hli
  have hdetM : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hMunit).ne_zero
  have hdet : M.det = ((MZ.det : ℤ) : ℚ) := by
    rw [hMmap]
    exact ((Int.castRingHom ℚ).map_det MZ).symm
  set d : ℤ := MZ.det with hd
  have hd0 : d ≠ 0 := by
    intro h
    apply hdetM
    rw [hdet, h]
    simp
  set z' : Fin n → ℤ := Matrix.cramer MZ bZ with hz'
  have hcr : MZ *ᵥ z' = d • bZ := Matrix.mulVec_cramer MZ bZ
  have hMz : M *ᵥ z = fun i => (bZ i : ℚ) := funext fun i => htight i
  have hcast : M *ᵥ (fun j => (z' j : ℚ)) = M *ᵥ ((d : ℚ) • z) := by
    rw [Matrix.mulVec_smul, hMz]
    funext i
    have h := congrFun hcr i
    have h' : ((MZ *ᵥ z') i : ℚ) = ((d • bZ) i : ℚ) := by rw [h]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h' ⊢
    push_cast at h'
    simpa [M, MZ, a] using h'
  have hzz : (fun j => (z' j : ℚ)) = (d : ℚ) • z :=
    Matrix.mulVec_injective_of_isUnit hMunit hcast
  have hsign : |d.sign| = 1 := by
    rcases lt_trichotomy d 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · exact absurd h hd0
    · simp [Int.sign_eq_one_of_pos h]
  refine ⟨fun j => d.sign * z' j, ?_, ?_⟩
  · intro j
    rw [abs_mul, hsign, one_mul, hz', Matrix.cramer_apply]
    have h := Matrix.det_le (A := MZ.updateCol j bZ) (abv := AbsoluteValue.abs) (x := 1)
      (by
        intro i j'
        rw [Matrix.updateCol_apply]
        split_ifs
        · exact hβZ _
        · exact haZ _ _)
    simpa using h
  · intro i
    have h2 : (1 : ℚ) ≤ ∑ j, (R i j : ℚ) * z j := by
      simpa [a, aZ, β, βZ, dotProduct] using hz (Sum.inl i) rfl
    have h3 : ((∑ j, R i j * (d.sign * z' j) : ℤ) : ℚ) = |(d : ℚ)| * ∑ j, (R i j : ℚ) * z j := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h4 : (z' j : ℚ) = (d : ℚ) * z j := by
        simpa using congrFun hzz j
      have h5 : ((d.sign : ℤ) : ℚ) * (d : ℚ) = |(d : ℚ)| := by
        exact_mod_cast Int.sign_mul_self_eq_abs d
      rw [h4, ← h5]
      ring
    have h6 : (1 : ℚ) ≤ |(d : ℚ)| := by
      exact_mod_cast Int.one_le_abs hd0
    have h7 : (1 : ℚ) ≤ ((∑ j, R i j * (d.sign * z' j) : ℤ) : ℚ) := by
      rw [h3]
      nlinarith
    exact_mod_cast h7

/-- Every linear threshold function on `s` Boolean inputs is realized by integer weights
whose absolute values sum to at most `(s + 2) ^ (s + 2)`. -/
theorem threshold_small_weights (s : ℕ) (c : Fin s → ℤ) (t0 : ℤ) :
    ∃ (c' : Fin s → ℤ) (t0' : ℤ), (∑ j : Fin s, |c' j| ≤ ((s : ℤ) + 2) ^ (s + 2)) ∧
      ∀ g : Fin s → Bool, (t0 ≤ ∑ j : Fin s, c j * (if g j = true then 1 else 0)) ↔
        (t0' ≤ ∑ j : Fin s, c' j * (if g j = true then 1 else 0)) := by
  classical
  let σ : (Fin s → Bool) → ℤ := fun g =>
    if t0 ≤ ∑ j : Fin s, c j * (if g j = true then 1 else 0) then 1 else -1
  let R : (Fin s → Bool) → Fin (s + 1) → ℤ := fun g =>
    Fin.snoc (fun j : Fin s => σ g * (if g j = true then 1 else 0)) (-σ g)
  have hσ : ∀ g, |σ g| = 1 := by
    intro g
    simp only [σ]
    split_ifs <;> simp
  have hR : ∀ g j, |R g j| ≤ 1 := by
    intro g j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [R, hσ]
    · simp only [R, Fin.snoc_castSucc, abs_mul, hσ, one_mul]
      split_ifs <;> simp
  let z0 : Fin (s + 1) → ℚ :=
    Fin.snoc (fun j : Fin s => (2 * c j : ℚ)) (2 * t0 - 1 : ℚ)
  have hz0 : ∀ g, (1 : ℚ) ≤ ∑ j, (R g j : ℚ) * z0 j := by
    intro g
    have key : (1 : ℤ) ≤ σ g * (2 * (∑ j : Fin s, c j * (if g j = true then 1 else 0)) -
        (2 * t0 - 1)) := by
      simp only [σ]
      split_ifs with h
      · linarith
      · rw [not_le] at h
        linarith
    have hsum : (∑ j, (R g j : ℚ) * z0 j) = ((σ g * (2 * (∑ j : Fin s, c j *
        (if g j = true then 1 else 0)) - (2 * t0 - 1)) : ℤ) : ℚ) := by
      rw [Fin.sum_univ_castSucc]
      simp only [R, z0, Fin.snoc_castSucc, Fin.snoc_last]
      push_cast
      have : ∀ j : Fin s, ((σ g : ℚ) * (if g j = true then 1 else 0)) * (2 * (c j : ℚ)) =
          (σ g : ℚ) * (2 * ((c j : ℚ) * (if g j = true then 1 else 0))) := fun j => by ring
      simp only [this, ← Finset.mul_sum]
      ring
    rw [hsum]
    exact_mod_cast key
  obtain ⟨N, hN, hRN⟩ := weightBound_integer R hR z0 hz0
  refine ⟨fun j => N j.castSucc, N (Fin.last s), ?_, ?_⟩
  · have h1 : ∑ j : Fin s, |N j.castSucc| ≤ ∑ _j : Fin s, (((s + 1).factorial : ℕ) : ℤ) :=
      Finset.sum_le_sum fun j _ => hN _
    have h2 : s * (s + 1).factorial ≤ (s + 2) ^ (s + 2) := by
      calc s * (s + 1).factorial ≤ (s + 2) * (s + 1).factorial :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (s + 2).factorial := (Nat.factorial_succ (s + 1)).symm
        _ ≤ (s + 2) ^ (s + 2) := Nat.factorial_le_pow _
    have h3 : ((s : ℤ) * ((s + 1).factorial : ℕ)) ≤ ((s : ℤ) + 2) ^ (s + 2) := by
      exact_mod_cast h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    exact h1.trans h3
  · intro g
    have h := hRN g
    rw [Fin.sum_univ_castSucc] at h
    simp only [R, Fin.snoc_castSucc, Fin.snoc_last] at h
    have hrew : ∑ j : Fin s, σ g * (if g j = true then 1 else 0) * N j.castSucc =
        σ g * ∑ j : Fin s, N j.castSucc * (if g j = true then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrew] at h
    simp only [σ] at h
    split_ifs at h with hg
    · simp only [hg, true_iff]
      linarith
    · simp only [hg, false_iff]
      linarith

/-- The same statement, with the equivalence stated only on a given set of inputs. -/
theorem threshold_small_weights_on (s : ℕ) (c : Fin s → ℤ) (t0 : ℤ)
    (S : Set (Fin s → Bool)) :
    ∃ (c' : Fin s → ℤ) (t0' : ℤ), (∑ j : Fin s, |c' j| ≤ ((s : ℤ) + 2) ^ (s + 2)) ∧
      ∀ g ∈ S, (t0 ≤ ∑ j : Fin s, c j * (if g j = true then 1 else 0)) ↔
        (t0' ≤ ∑ j : Fin s, c' j * (if g j = true then 1 else 0)) := by
  obtain ⟨c', t0', hb, h⟩ := threshold_small_weights s c t0
  exact ⟨c', t0', hb, fun g _ => h g⟩

end PEqualNP.CircuitLowerBounds.Helpers
