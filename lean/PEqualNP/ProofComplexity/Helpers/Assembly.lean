import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.Defs.ProofComplexityBit
import PEqualNP.Defs.ProofComplexityLin
import PEqualNP.ProofComplexity.Helpers.PCToolkit
import Mathlib

/-!
# Helpers: the final assembly of the bit pigeonhole lower bound for Res(⊕)

* `pcRefutable_of_blockSystem_zero`: a refutation of a block system with no blocks is a
  refutation of the base system;
* `isRowLinear_one`: the constant `1` is row-linear;
* the arithmetic of the parameter choice (`pow_bound`, `log_bound`, the natural number side
  conditions);
* `assembly`: the three links of the chain give the exponential lower bound.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

/-- With no blocks, the block system is the base system in renamed variables, so a
refutation transfers back in the same degree. -/
theorem pcRefutable_of_blockSystem_zero {V : Type} (F : Set (MvPolynomial V (ZMod 2)))
    (h W D : ℕ) (g : Fin 0 → Fin W → MvPolynomial V (ZMod 2))
    (H : PCRefutable (blockSystem F h 0 W g) D) : PCRefutable F D := by
  have key := pcDerivable_replay (F := blockSystem F h 0 W g) (G := F) (T := 1) (D := D)
    (s := 0) (Sum.elim X (fun _ => 0))
    (by rintro (v | r) <;> simp) 1 (by simp)
    (by
      intro a ha hdeg
      rcases ha with ⟨q, hq, rfl⟩ | ⟨r, _⟩ | ⟨j, _⟩
      · have hq' : bind₁ (Sum.elim X (fun _ => 0) : BlockVar V h 0 W → MvPolynomial V (ZMod 2))
            (rename Sum.inl q) = q := by
          rw [bind₁_rename]
          have : ((Sum.elim X (fun _ => 0) : BlockVar V h 0 W → MvPolynomial V (ZMod 2)) ∘
              Sum.inl) = X := rfl
          rw [this, bind₁_X_left]
          rfl
        have hle := totalDegree_bind₁_le (T := 1)
          (Sum.elim X (fun _ => 0) : BlockVar V h 0 W → MvPolynomial V (ZMod 2))
          (by rintro (v | r) <;> simp) (rename Sum.inl q)
        rw [hq'] at hle
        rw [hq', show (1 : MvPolynomial V (ZMod 2)) * q = q from one_mul q]
        exact .ax hq (by omega)
      · exact r.1.elim0
      · exact j.elim0) H
  have h1 : (1 : MvPolynomial V (ZMod 2)) * bind₁ (Sum.elim X (fun _ => 0) :
      BlockVar V h 0 W → MvPolynomial V (ZMod 2)) 1 = 1 := by simp
  rw [h1] at key
  have h2 : 1 * D + 0 = D := by omega
  rw [h2] at key
  exact key

/-- The constant `1` is row-linear of every degree. -/
theorem isRowLinear_one (m l k : ℕ) : IsRowLinear m l k (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)) := by
  intro u hu
  have h1 : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, support_monomial] at hu
  simp at hu
  subst hu
  simp

/-- `2 ^ l` dominates `65536 * l ^ 3` from `l = 32` on. -/
theorem pow_bound (l : ℕ) (hl : 32 ≤ l) : 65536 * l ^ 3 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    have h1 : (l + 1) ^ 3 ≤ 2 * l ^ 3 := by
      have : 32 * l ^ 2 ≤ l ^ 3 := by nlinarith [sq_nonneg l]
      nlinarith [sq_nonneg l]
    rw [pow_succ 2 l]
    linarith

/-- The real number part: if the proof has at most `exp x` lines, then the logarithm of
four times the number of blocks is small compared with `k ^ 2`. -/
theorem log_bound (l S M : ℕ) (hl : 32 ≤ l)
    (hS : (S : ℝ) ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)))
    (hM : M ≤ 3 * S + (2 ^ l + 1).choose 2) (hM1 : 1 ≤ M) :
    ((2 ^ l + 1 : ℕ) : ℝ) * Real.log (4 * (M : ℝ)) ≤ ((2 ^ l / (32 * l) : ℕ) : ℝ) ^ 2 := by
  set x : ℝ := (2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2) with hx
  set E : ℝ := Real.exp x with hE
  have hpb := pow_bound l hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  have hden : (0 : ℝ) < 32768 * (l : ℝ) ^ 2 := by positivity
  have hpbR : (65536 : ℝ) * (l : ℝ) ^ 3 ≤ (2 : ℝ) ^ l := by exact_mod_cast hpb
  -- x ≥ 2 l
  have hx2l : ((2 * l : ℕ) : ℝ) * 1 ≤ x := by
    rw [hx, le_div_iff₀ hden]
    push_cast
    nlinarith
  -- E ≥ n ^ 2
  have hEn : ((2 : ℝ) ^ l) ^ 2 ≤ E := by
    have h1 : Real.exp (((2 * l : ℕ) : ℝ) * 1) ≤ E := Real.exp_le_exp.mpr hx2l
    rw [Real.exp_nat_mul] at h1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h3 : (2 : ℝ) ^ (2 * l) ≤ Real.exp 1 ^ (2 * l) :=
      pow_le_pow_left₀ (by norm_num) h2 _
    have h4 : ((2 : ℝ) ^ l) ^ 2 = (2 : ℝ) ^ (2 * l) := by rw [← pow_mul, mul_comm]
    rw [h4]
    exact h3.trans h1
  have hn32 : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) hl
  have hnpos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hE16 : (28 : ℝ) ≤ E := by nlinarith
  -- 4 M ≤ E ^ 4
  have hchoose : ((2 ^ l + 1).choose 2 : ℝ) ≤ ((2 : ℝ) ^ l + 1) ^ 2 := by
    have := Nat.choose_le_pow (2 ^ l + 1) 2
    exact_mod_cast this
  have hMR : (M : ℝ) ≤ 3 * (S : ℝ) + ((2 ^ l + 1).choose 2 : ℝ) := by exact_mod_cast hM
  have h4M : 4 * (M : ℝ) ≤ 28 * E := by nlinarith
  have hE3 : (28 : ℝ) ≤ E ^ 3 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < E) 2]
  have h4M' : 4 * (M : ℝ) ≤ Real.exp (((4 : ℕ) : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    have : E ^ 4 = E * E ^ 3 := by ring
    rw [← hE, this]
    nlinarith
  have hMpos : (0 : ℝ) < 4 * (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hlog : Real.log (4 * (M : ℝ)) ≤ 4 * x := by
    have := Real.log_le_log hMpos h4M'
    rw [Real.log_exp] at this
    simpa using this
  -- natural number bound on k
  have hk : 4 * (2 ^ l * (2 ^ l + 1)) ≤ 32768 * l ^ 2 * (2 ^ l / (32 * l)) ^ 2 := by
    set n := 2 ^ l with hn
    set k := n / (32 * l) with hkdef
    have hdm : n < 32 * l * (k + 1) := Nat.lt_mul_div_succ n (by omega)
    rw [mul_add, mul_one] at hdm
    have h64 : 64 * l ≤ n := by nlinarith [sq_nonneg l]
    have ha : n ≤ 2 * (32 * l * k) := by linarith
    have hsq : n * n ≤ (2 * (32 * l * k)) * (2 * (32 * l * k)) := Nat.mul_le_mul ha ha
    have h1n : 1 ≤ n := by omega
    nlinarith
  have hkR : 4 * ((2 : ℝ) ^ l * ((2 : ℝ) ^ l + 1)) ≤
      32768 * (l : ℝ) ^ 2 * ((2 ^ l / (32 * l) : ℕ) : ℝ) ^ 2 := by exact_mod_cast hk
  have hxeq : x * (32768 * (l : ℝ) ^ 2) = (2 : ℝ) ^ l := by
    rw [hx]; field_simp
  have hgoal : ((2 : ℝ) ^ l + 1) * (4 * x) ≤ ((2 ^ l / (32 * l) : ℕ) : ℝ) ^ 2 := by
    have h5 : ((2 : ℝ) ^ l + 1) * (4 * x) * (32768 * (l : ℝ) ^ 2) ≤
        ((2 ^ l / (32 * l) : ℕ) : ℝ) ^ 2 * (32768 * (l : ℝ) ^ 2) := by
      calc ((2 : ℝ) ^ l + 1) * (4 * x) * (32768 * (l : ℝ) ^ 2)
          = 4 * ((2 : ℝ) ^ l * ((2 : ℝ) ^ l + 1)) := by rw [← hxeq]; ring
        _ ≤ _ := by linarith
    exact le_of_mul_le_mul_right h5 hden
  have hm0 : (0 : ℝ) ≤ ((2 ^ l + 1 : ℕ) : ℝ) := by positivity
  calc ((2 ^ l + 1 : ℕ) : ℝ) * Real.log (4 * (M : ℝ))
      ≤ ((2 ^ l + 1 : ℕ) : ℝ) * (4 * x) := mul_le_mul_of_nonneg_left hlog hm0
    _ = ((2 : ℝ) ^ l + 1) * (4 * x) := by push_cast; ring
    _ ≤ _ := hgoal

/-- The natural number side conditions of the parameter choice `k = 2 ^ l / (32 * l)`. -/
theorem nat_side (l : ℕ) (hl : 32 ≤ l) :
    1 ≤ 2 ^ l / (32 * l) ∧ 2 ^ l / (32 * l) ≤ 2 ^ l + 1 ∧
    4 * (2 ^ l / (32 * l) - 1) < 2 ^ l ∧
    2 * (2 ^ l / (32 * l) * (12 * l + 1 + 1)) + 2 * (2 ^ l / (32 * l)) ≤ 2 ^ l + 1 ∧
    2 * (12 * l + 1) + 2 * 1 ≤ 2 ^ l + 1 := by
  have hpb := pow_bound l hl
  set n := 2 ^ l with hn
  have h64 : 64 * l ≤ n := by nlinarith [sq_nonneg l]
  have hk1 : 1 ≤ n / (32 * l) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hkl : 32 * l * (n / (32 * l)) ≤ n := Nat.mul_div_le n (32 * l)
  set k := n / (32 * l) with hk
  have hkn : k ≤ n := Nat.div_le_self _ _
  have h32 : 32 * k ≤ 32 * l * k := by nlinarith
  refine ⟨hk1, by omega, by omega, ?_, by omega⟩
  have : 2 * (k * (12 * l + 1 + 1)) + 2 * k ≤ 32 * l * k := by nlinarith
  omega

/-- The assembly: the degree lower bound for row-linear polynomials, the simulation of
Res(⊕) by block systems, and the elimination of the blocks together give the exponential
lower bound on the length of Res(⊕) refutations of bit pigeonhole. -/
theorem assembly
    (HB : ∀ (m l k B : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → 1 ≤ k → k ≤ B →
      4 * (k - 1) < 2 ^ l → 2 * B + 2 * k ≤ 2 ^ l + 1 → f ≠ 0 → IsRowLinear m l k f →
      ¬ PCDerivable (bitPHPSystem m l) B f)
    (HC : ∀ (m l h : ℕ) (π : List (LinClause (Fin m × Fin l))), 1 ≤ h →
      IsLinRefutation (BPHP m l) π →
      ∃ (M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)),
        M ≤ 3 * π.length + m.choose 2 ∧ (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) ∧
        PCRefutable (blockSystem (bitPHPSystem m l) h M W g) (max (2 * h + l) (4 * h + 1)))
    (HD : ∀ (m l k D M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)),
      0 < m → 1 ≤ l → 1 ≤ k → 1 ≤ M → k ≤ m →
      (m : ℝ) * Real.log (4 * (M : ℝ)) ≤ (k : ℝ) ^ 2 → 2 * (3 * l) + 1 ≤ D →
      (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) →
      PCRefutable (blockSystem (bitPHPSystem m l) (3 * l) M W g) D →
      ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ IsRowLinear m l k f ∧
        PCDerivable (bitPHPSystem m l) (k * (D + 1)) f)
    (l : ℕ) (π : List (LinClause (Fin (2 ^ l + 1) × Fin l))) (hl : 32 ≤ l)
    (hπ : IsLinRefutation (BPHP (2 ^ l + 1) l) π) :
    Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) < (π.length : ℝ) := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨M, W, g, hM, hg, href⟩ := HC (2 ^ l + 1) l (3 * l) π (by omega) hπ
  have hD : max (2 * (3 * l) + l) (4 * (3 * l) + 1) = 12 * l + 1 := by omega
  rw [hD] at href
  obtain ⟨hk1, hkm, hk4, hkB, hone⟩ := nat_side l hl
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    have hbase := pcRefutable_of_blockSystem_zero _ _ _ _ g href
    exact HB (2 ^ l + 1) l 1 (12 * l + 1) 1 (by omega) le_rfl (by omega) (by positivity)
      hone one_ne_zero (isRowLinear_one _ _ _) hbase
  · obtain ⟨f, hf0, hfrow, hfder⟩ := HD (2 ^ l + 1) l (2 ^ l / (32 * l)) (12 * l + 1) M W g
      (by omega) (by omega) hk1 hMpos hkm (log_bound l π.length M hl hcon hM hMpos)
      (by omega) hg href
    refine HB (2 ^ l + 1) l (2 ^ l / (32 * l)) _ f (by omega) hk1 ?_ hk4 hkB hf0 hfrow hfder
    exact Nat.le_mul_of_pos_right _ (by omega)

end PEqualNP.ProofComplexity.Helpers
