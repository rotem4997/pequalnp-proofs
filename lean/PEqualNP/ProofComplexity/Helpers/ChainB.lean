import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.ProofComplexity.Helpers.PCToolkit
import PEqualNP.ProofComplexity.Helpers.DegreeBound

/-!
# Helpers: no nonzero row-linear polynomial of small degree is derivable from bit pigeonhole

The second link of the chain of Section 5 of arXiv:2609.23015 (unrefereed), on our own
definitions. Let `f` be a nonzero row-linear polynomial of degree at most `k` in the bit
variables, and suppose `f` is derivable from `bitPHPSystem m l` in degree `B`.

1. By the decoder lemma (a hypothesis of `chainB_of_decoder`, proved elsewhere), the decoded
   polynomial `bitDecoder m l f` is derivable in degree `B` from the functional pigeonhole
   system with `2 ^ l` holes.
2. Take a monomial `u0` of `f` of largest degree. It uses a set `S` of pigeons, one bit
   `τ i` for each `i ∈ S`, and no other variable.
3. Choose for every `i ∈ S` two holes `a i`, `b i` whose labels differ in bit `τ i` and in no
   other bit, all these holes being different (`exists_pairs`; this uses
   `4 * (S.card - 1) < 2 ^ l`).
4. For every subset `E` of `S`, send the pigeon `i ∈ S` to the hole `b i` if `i ∈ E` and to
   `a i` otherwise, and forbid all the chosen holes to the other pigeons. This substitution
   (`restr`) maps every axiom of the functional system with `2 ^ l` holes to zero or to an
   axiom of the functional system on the remaining holes (`restr_axiom`), and the target
   system does not depend on `E`.
5. The sum over `E` of the restricted decoded polynomials is the constant `1`
   (`sum_theta_eq_one`): for a monomial `u` the sum factors over the rows of `S`, the factor
   of row `i` is `1` when `u` contains the variable `(i, τ i)` and `0` otherwise, and the
   only monomial of `f` that contains all these variables is `u0`.
6. So `1` is derivable in degree `B` from a functional pigeonhole system with at least
   `2 ^ l - 2 * k` holes, against `funPHP_no_pc_refutation`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

/-! ### Characteristic two -/

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c; decide

theorem mvPoly_add_self {σ : Type} (p : MvPolynomial σ (ZMod 2)) : p + p = 0 := by
  have h : (C (1 + 1 : ZMod 2) : MvPolynomial σ (ZMod 2)) * p = p + p := by
    rw [C_add, C_1]; ring
  rw [← h, zmod2_add_self, C_0, zero_mul]

/-! ### The restriction of the functional pigeonhole system -/

/-- The image of the one-hot variable `(i, j)` of a pigeon that is not sent anywhere: the
variable `(i, j')` when `j` is the image `e j'` of a remaining hole, and zero when `j` is
not in the range of `e`. -/
noncomputable def holeVar {m n N' : ℕ} (e : Fin N' → Fin n) (i : Fin m) (j : Fin n) :
    MvPolynomial (Fin m × Fin N') (ZMod 2) :=
  ∑ j' : Fin N', if e j' = j then X (i, j') else 0

theorem holeVar_cases {m n N' : ℕ} (e : Fin N' → Fin n) (he : Function.Injective e)
    (i : Fin m) (j : Fin n) :
    ((∀ j', e j' ≠ j) ∧ holeVar e i j = 0) ∨ ∃ j', e j' = j ∧ holeVar e i j = X (i, j') := by
  by_cases h : ∃ j', e j' = j
  · obtain ⟨j', rfl⟩ := h
    refine Or.inr ⟨j', rfl, ?_⟩
    unfold holeVar
    rw [Finset.sum_eq_single j']
    · simp
    · intro b _ hb
      rw [ite_eq_right (fun h => hb (he h))]
    · intro h; exact absurd (Finset.mem_univ _) h
  · push Not at h
    refine Or.inl ⟨h, ?_⟩
    unfold holeVar
    exact Finset.sum_eq_zero fun j' _ => ite_eq_right (h j')

/-- The restriction that sends every pigeon `i ∈ S` to the hole `ε i` and keeps for the other
pigeons only the holes in the range of `e`. -/
noncomputable def restr {m n N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin n)
    (e : Fin N' → Fin n) (v : Fin m × Fin n) : MvPolynomial (Fin m × Fin N') (ZMod 2) :=
  if v.1 ∈ S then C (if v.2 = ε v.1 then 1 else 0) else holeVar e v.1 v.2

theorem restr_of_mem {m n N' : ℕ} {S : Finset (Fin m)} (ε : Fin m → Fin n)
    (e : Fin N' → Fin n) {i : Fin m} (hi : i ∈ S) (j : Fin n) :
    restr S ε e (i, j) = C (if j = ε i then 1 else 0) :=
  ite_eq_left hi

theorem restr_of_notMem {m n N' : ℕ} {S : Finset (Fin m)} (ε : Fin m → Fin n)
    (e : Fin N' → Fin n) {i : Fin m} (hi : i ∉ S) (j : Fin n) :
    restr S ε e (i, j) = holeVar e i j :=
  ite_eq_right hi

theorem restr_totalDegree_le {m n N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin n)
    (e : Fin N' → Fin n) (he : Function.Injective e) (v : Fin m × Fin n) :
    (restr S ε e v).totalDegree ≤ 1 := by
  obtain ⟨i, j⟩ := v
  by_cases hi : i ∈ S
  · rw [restr_of_mem ε e hi, totalDegree_C]; exact Nat.zero_le _
  · rw [restr_of_notMem ε e hi]
    rcases holeVar_cases e he i j with ⟨-, h0⟩ | ⟨j', -, hX⟩
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · rw [hX, totalDegree_X]

/-- Every axiom of the functional pigeonhole system is mapped by the restriction to zero or to
an axiom of the functional pigeonhole system on the remaining holes. -/
theorem restr_axiom {m n N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin n) (e : Fin N' → Fin n)
    (he : Function.Injective e)
    (hε : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ε i ≠ ε i')
    (hεe : ∀ i ∈ S, ∀ j', e j' ≠ ε i) :
    ∀ p ∈ funPHPSystem m n,
      bind₁ (restr S ε e) p = 0 ∨ bind₁ (restr S ε e) p ∈ funPHPSystem m N' := by
  rintro p (⟨⟨i, j⟩, rfl⟩ | ⟨i, j, j', hjj, rfl⟩ | ⟨i, i', j, hii, rfl⟩ | ⟨i, rfl⟩)
  · simp only [map_add, map_mul, bind₁_X_right]
    by_cases hi : i ∈ S
    · left
      rw [restr_of_mem ε e hi]
      split_ifs
      · rw [C_1, one_mul]; exact mvPoly_add_self 1
      · simp
    · rw [restr_of_notMem ε e hi]
      rcases holeVar_cases e he i j with ⟨-, h0⟩ | ⟨j1, -, hX⟩
      · left; rw [h0]; simp
      · right; rw [hX]; exact Or.inl ⟨(i, j1), rfl⟩
  · simp only [map_mul, bind₁_X_right]
    by_cases hi : i ∈ S
    · left
      rw [restr_of_mem ε e hi, restr_of_mem ε e hi]
      by_cases h1 : j = ε i
      · have h2 : ¬ j' = ε i := fun h => hjj (h1.trans h.symm)
        rw [ite_eq_right h2, C_0, mul_zero]
      · rw [ite_eq_right h1, C_0, zero_mul]
    · rw [restr_of_notMem ε e hi, restr_of_notMem ε e hi]
      rcases holeVar_cases e he i j with ⟨-, h0⟩ | ⟨j1, hj1, hX⟩
      · left; rw [h0, zero_mul]
      · rcases holeVar_cases e he i j' with ⟨-, h0'⟩ | ⟨j2, hj2, hX'⟩
        · left; rw [h0', mul_zero]
        · right; rw [hX, hX']
          exact Or.inr (Or.inl ⟨i, j1, j2, fun h => hjj (by rw [← hj1, ← hj2, h]), rfl⟩)
  · simp only [map_mul, bind₁_X_right]
    by_cases hi : i ∈ S
    · by_cases hi' : i' ∈ S
      · left
        rw [restr_of_mem ε e hi, restr_of_mem ε e hi']
        by_cases h1 : j = ε i
        · have h2 : ¬ j = ε i' := fun h => hε i hi i' hi' hii (h1.symm.trans h)
          rw [ite_eq_right h2, C_0, mul_zero]
        · rw [ite_eq_right h1, C_0, zero_mul]
      · left
        rw [restr_of_mem ε e hi, restr_of_notMem ε e hi']
        by_cases h1 : j = ε i
        · rcases holeVar_cases e he i' j with ⟨-, h0⟩ | ⟨j1, hj1, -⟩
          · rw [h0, mul_zero]
          · exact absurd (hj1.trans h1) (hεe i hi j1)
        · rw [ite_eq_right h1, C_0, zero_mul]
    · by_cases hi' : i' ∈ S
      · left
        rw [restr_of_notMem ε e hi, restr_of_mem ε e hi']
        by_cases h1 : j = ε i'
        · rcases holeVar_cases e he i j with ⟨-, h0⟩ | ⟨j1, hj1, -⟩
          · rw [h0, zero_mul]
          · exact absurd (hj1.trans h1) (hεe i' hi' j1)
        · rw [ite_eq_right h1, C_0, mul_zero]
      · rw [restr_of_notMem ε e hi, restr_of_notMem ε e hi']
        rcases holeVar_cases e he i j with ⟨-, h0⟩ | ⟨j1, hj1, hX⟩
        · left; rw [h0, zero_mul]
        · rcases holeVar_cases e he i' j with ⟨-, h0'⟩ | ⟨j2, hj2, hX'⟩
          · left; rw [h0', mul_zero]
          · right; rw [hX, hX']
            have h12 : j1 = j2 := he (hj1.trans hj2.symm)
            subst h12
            exact Or.inr (Or.inr (Or.inl ⟨i, i', j1, hii, rfl⟩))
  · simp only [map_add, map_sum, map_one, bind₁_X_right]
    by_cases hi : i ∈ S
    · left
      have hsum : ∑ j : Fin n, restr S ε e (i, j) = 1 := by
        simp only [restr_of_mem ε e hi]
        rw [← map_sum, Finset.sum_ite_eq']
        simp
      rw [hsum]; exact mvPoly_add_self 1
    · right
      have hsum : ∑ j : Fin n, restr S ε e (i, j) = ∑ j' : Fin N', X (i, j') := by
        simp only [restr_of_notMem ε e hi, holeVar]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_ite_eq]; simp
      rw [hsum]
      exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))

/-- The restriction maps derivations of degree `B` to derivations of degree `B`. -/
theorem restr_derivable {m n N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin n)
    (e : Fin N' → Fin n) (he : Function.Injective e)
    (hε : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ε i ≠ ε i')
    (hεe : ∀ i ∈ S, ∀ j', e j' ≠ ε i) {B : ℕ} {p : MvPolynomial (Fin m × Fin n) (ZMod 2)}
    (h : PCDerivable (funPHPSystem m n) B p) :
    PCDerivable (funPHPSystem m N') B (bind₁ (restr S ε e) p) := by
  have key : PCDerivable (funPHPSystem m N') (1 * B + 0) (1 * bind₁ (restr S ε e) p) := by
    refine pcDerivable_replay (restr S ε e) (restr_totalDegree_le S ε e he) 1 (by simp)
      (fun a ha hdeg => ?_) h
    rw [one_mul, one_mul, add_zero]
    rcases restr_axiom S ε e he hε hεe a ha with h0 | hmem
    · rw [h0]; exact .zero
    · refine .ax hmem ?_
      have := totalDegree_bind₁_le (restr S ε e) (restr_totalDegree_le S ε e he) a
      omega
  simpa using key

/-! ### The restriction after the decoder -/

/-- Bit `t` of the hole `x`, as an element of `ZMod 2`. -/
def bitVal {l : ℕ} (x : Fin (2 ^ l)) (t : Fin l) : ZMod 2 :=
  if x.val.testBit t.val = true then 1 else 0

/-- The decoded bit variable of a pigeon that is not sent anywhere, after the restriction. -/
noncomputable def decHole {m l N' : ℕ} (e : Fin N' → Fin (2 ^ l)) (v : Fin m × Fin l) :
    MvPolynomial (Fin m × Fin N') (ZMod 2) :=
  ∑ j : Fin (2 ^ l), if j.val.testBit v.2.val = true then holeVar e v.1 j else 0

/-- The image of a bit variable under the decoder followed by the restriction. -/
noncomputable def theta {m l N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin (2 ^ l))
    (e : Fin N' → Fin (2 ^ l)) (v : Fin m × Fin l) : MvPolynomial (Fin m × Fin N') (ZMod 2) :=
  if v.1 ∈ S then C (bitVal (ε v.1) v.2) else decHole e v

theorem restr_bitDecoder {m l N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin (2 ^ l))
    (e : Fin N' → Fin (2 ^ l)) (p : MvPolynomial (Fin m × Fin l) (ZMod 2)) :
    bind₁ (restr S ε e) (bitDecoder m l p) = aeval (theta S ε e) p := by
  have h : (bind₁ (restr S ε e)).comp (bitDecoder m l) = aeval (theta S ε e) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, t⟩
    have hterm : ∀ j : Fin (2 ^ l),
        bind₁ (restr S ε e) (if j.val.testBit t.val = true then X (i, j) else 0)
          = if j.val.testBit t.val = true then restr S ε e (i, j) else 0 := by
      intro j; split_ifs <;> simp
    simp only [AlgHom.comp_apply, bitDecoder, aeval_X, map_sum, hterm]
    by_cases hi : i ∈ S
    · simp only [theta, ite_eq_left hi, restr_of_mem ε e hi]
      rw [Finset.sum_eq_single (ε i)]
      · simp only [ite_true, bitVal]
        split_ifs <;> simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [theta, ite_eq_right hi, restr_of_notMem ε e hi, decHole]
  exact DFunLike.congr_fun h p

theorem aeval_theta_monomial {m l N' : ℕ} (S : Finset (Fin m)) (ε : Fin m → Fin (2 ^ l))
    (e : Fin N' → Fin (2 ^ l)) (u : (Fin m × Fin l) →₀ ℕ) :
    aeval (theta S ε e) (monomial u (1 : ZMod 2))
      = (∏ i ∈ Sᶜ, ∏ t : Fin l, decHole e (i, t) ^ u (i, t))
        * ∏ i ∈ S, C (∏ t : Fin l, bitVal (ε i) t ^ u (i, t)) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, ← Finset.prod_mul_prod_compl S, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun t _ => ?_
    rw [theta, ite_eq_right (Finset.mem_compl.mp hi)]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [theta, ite_eq_left hi, map_pow]

/-- The sum over all subsets `E` of `S` of the restricted monomial `u` factors over the rows
of `S`. -/
theorem sum_theta_monomial {m l N' : ℕ} (S : Finset (Fin m)) (a b : Fin m → Fin (2 ^ l))
    (e : Fin N' → Fin (2 ^ l)) (u : (Fin m × Fin l) →₀ ℕ) :
    ∑ E ∈ S.powerset,
        aeval (theta S (fun i => if i ∈ E then b i else a i) e) (monomial u (1 : ZMod 2))
      = (∏ i ∈ Sᶜ, ∏ t : Fin l, decHole e (i, t) ^ u (i, t))
        * ∏ i ∈ S, C ((∏ t : Fin l, bitVal (b i) t ^ u (i, t))
            + ∏ t : Fin l, bitVal (a i) t ^ u (i, t)) := by
  simp only [aeval_theta_monomial]
  rw [← Finset.mul_sum]
  congr 1
  simp only [C_add]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun E hE => ?_
  have hE' := Finset.mem_powerset.mp hE
  rw [← Finset.prod_sdiff hE', mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [ite_eq_left hi]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [ite_eq_right (Finset.mem_sdiff.mp hi).2]

/-! ### Rows of a row-linear monomial -/

theorem row_cases {l : ℕ} (r : Fin l → ℕ) (hr : ∑ t, r t ≤ 1) :
    (∀ t, r t = 0) ∨ ∃ t0, ∀ t, r t = if t = t0 then 1 else 0 := by
  by_cases h : ∀ t, r t = 0
  · exact Or.inl h
  · push Not at h
    obtain ⟨t0, ht0⟩ := h
    refine Or.inr ⟨t0, fun t => ?_⟩
    have h1 : r t0 ≤ ∑ t, r t :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t0)
    by_cases htt : t = t0
    · subst htt; rw [ite_eq_left rfl]; omega
    · rw [ite_eq_right htt]
      have h2 : r t0 + ∑ t ∈ Finset.univ.erase t0, r t = ∑ t, r t :=
        Finset.add_sum_erase _ _ (Finset.mem_univ t0)
      have h3 : r t ≤ ∑ t ∈ Finset.univ.erase t0, r t :=
        Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨htt, Finset.mem_univ t⟩)
      omega

/-- The factor of one row: two holes that differ in bit `t0` only see a row with at most one
variable in the same way unless that variable is the bit `t0`. -/
theorem row_pair_sum {l : ℕ} (x y : Fin (2 ^ l)) (t0 : Fin l)
    (hxy : ∀ t : Fin l, (x.val.testBit t.val ≠ y.val.testBit t.val) ↔ t = t0)
    (r : Fin l → ℕ) (hr : ∑ t, r t ≤ 1) :
    (∏ t, bitVal y t ^ r t) + (∏ t, bitVal x t ^ r t) = if r t0 = 0 then (0 : ZMod 2) else 1 := by
  rcases row_cases r hr with h0 | ⟨t1, h1⟩
  · simp only [h0, pow_zero, Finset.prod_const_one, ite_true]
    exact zmod2_add_self 1
  · have hprod : ∀ z : Fin (2 ^ l), ∏ t, bitVal z t ^ r t = bitVal z t1 := by
      intro z
      rw [Finset.prod_eq_single t1]
      · rw [h1 t1, ite_eq_left rfl, pow_one]
      · intro t _ ht; rw [h1 t, ite_eq_right ht, pow_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hprod, hprod, h1 t0]
    by_cases h : t1 = t0
    · subst h
      have hne := (hxy t1).2 rfl
      rw [ite_eq_left rfl, ite_eq_right one_ne_zero]
      unfold bitVal
      revert hne
      cases x.val.testBit t1.val <;> cases y.val.testBit t1.val <;> simp
    · have heq : x.val.testBit t1.val = y.val.testBit t1.val := by
        by_contra hne
        exact h ((hxy t1).1 hne)
      rw [ite_eq_right (Ne.symm h), ite_eq_left rfl]
      unfold bitVal
      rw [heq]
      exact zmod2_add_self _

/-- The cube sum: the sum over all subsets `E` of `S` of the restricted decoded `f` is the
constant `1`. -/
theorem sum_theta_eq_one {m l N' : ℕ} (S : Finset (Fin m)) (τ : Fin m → Fin l)
    (a b : Fin m → Fin (2 ^ l)) (e : Fin N' → Fin (2 ^ l))
    (f : MvPolynomial (Fin m × Fin l) (ZMod 2)) (u0 : (Fin m × Fin l) →₀ ℕ)
    (hrow : ∀ u ∈ f.support, ∀ i : Fin m, ∑ t : Fin l, u (i, t) ≤ 1)
    (hu0 : u0 ∈ f.support)
    (hS1 : ∀ i ∈ S, u0 (i, τ i) ≠ 0) (hS0 : ∀ i ∉ S, ∀ t, u0 (i, t) = 0)
    (hother : ∀ u ∈ f.support, u ≠ u0 → ∃ i ∈ S, u (i, τ i) = 0)
    (hab : ∀ i ∈ S, ∀ t : Fin l,
      ((a i).val.testBit t.val ≠ (b i).val.testBit t.val) ↔ t = τ i) :
    ∑ E ∈ S.powerset, aeval (theta S (fun i => if i ∈ E then b i else a i) e) f = 1 := by
  have hf : f = ∑ u ∈ f.support, monomial u (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h0 : f.coeff u ≠ 0 := mem_support_iff.mp hu
    have h1 : f.coeff u = 1 := by
      generalize f.coeff u = c at h0
      revert h0; revert c; decide
    rw [h1]
  have hpair : ∀ u ∈ f.support, ∀ i ∈ S,
      (∏ t : Fin l, bitVal (b i) t ^ u (i, t)) + ∏ t : Fin l, bitVal (a i) t ^ u (i, t)
        = if u (i, τ i) = 0 then (0 : ZMod 2) else 1 := fun u hu i hi =>
    row_pair_sum (a i) (b i) (τ i) (hab i hi) (fun t => u (i, t)) (hrow u hu i)
  have key : ∀ E : Finset (Fin m),
      aeval (theta S (fun i => if i ∈ E then b i else a i) e) f
        = ∑ u ∈ f.support,
          aeval (theta S (fun i => if i ∈ E then b i else a i) e) (monomial u (1 : ZMod 2)) := by
    intro E
    conv_lhs => rw [hf]
    rw [map_sum]
  simp only [key]
  rw [Finset.sum_comm]
  simp only [sum_theta_monomial]
  rw [Finset.sum_eq_single u0]
  · have h1 : ∏ i ∈ Sᶜ, ∏ t : Fin l, (decHole e (i, t) :
        MvPolynomial (Fin m × Fin N') (ZMod 2)) ^ u0 (i, t) = 1 :=
      Finset.prod_eq_one fun i hi => Finset.prod_eq_one fun t _ => by
        rw [hS0 i (Finset.mem_compl.mp hi) t, pow_zero]
    have h2 : ∏ i ∈ S, (C ((∏ t : Fin l, bitVal (b i) t ^ u0 (i, t))
        + ∏ t : Fin l, bitVal (a i) t ^ u0 (i, t)) :
          MvPolynomial (Fin m × Fin N') (ZMod 2)) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [hpair u0 hu0 i hi, ite_eq_right (hS1 i hi), C_1]
    rw [h1, h2, mul_one]
  · intro u hu hne
    obtain ⟨i, hi, hz⟩ := hother u hu hne
    rw [Finset.prod_eq_zero hi (by rw [hpair u hu i hi, ite_eq_left hz, C_0]), mul_zero]
  · intro h; exact absurd hu0 h

/-! ### Disjoint pairs of holes that differ in one prescribed bit -/

/-- The hole whose label differs from that of `x` in bit `t` only. -/
def flipBit {l : ℕ} (t : Fin l) (x : Fin (2 ^ l)) : Fin (2 ^ l) :=
  ⟨x.val ^^^ 2 ^ t.val, Nat.xor_lt_two_pow x.2 (Nat.pow_lt_pow_right (by norm_num) t.2)⟩

theorem flipBit_testBit {l : ℕ} (t : Fin l) (x : Fin (2 ^ l)) (s : Fin l) :
    (x.val.testBit s.val ≠ (flipBit t x).val.testBit s.val) ↔ s = t := by
  simp only [flipBit, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : s = t
  · subst h; simp
  · have h' : ¬ t.val = s.val := fun h' => h (Fin.ext h'.symm)
    simp [h, h']

theorem flipBit_injective {l : ℕ} (t : Fin l) : Function.Injective (flipBit t) := by
  intro x y h
  have h' := congrArg Fin.val h
  simp only [flipBit] at h'
  exact Fin.ext (Nat.xor_left_injective h')

/-- For every pigeon of `S` a pair of holes that differ exactly in the prescribed bit, all
the holes being different. A greedy choice: the pairs chosen so far exclude at most
`4 * (S.card - 1)` candidates for the first hole of the next pair. -/
theorem exists_pairs {m l : ℕ} (τ : Fin m → Fin l) (S : Finset (Fin m))
    (hS : 4 * (S.card - 1) < 2 ^ l) :
    ∃ a b : Fin m → Fin (2 ^ l),
      (∀ i ∈ S, ∀ t : Fin l,
        ((a i).val.testBit t.val ≠ (b i).val.testBit t.val) ↔ t = τ i) ∧
      (∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → a i ≠ a i' ∧ a i ≠ b i' ∧ b i ≠ b i') := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (by positivity)⟩,
      fun _ => ⟨0, Nat.pos_of_ne_zero (by positivity)⟩, by simp, by simp⟩
  | insert i0 S hi0 ih =>
    rw [Finset.card_insert_of_notMem hi0, Nat.add_sub_cancel] at hS
    obtain ⟨a, b, hbit, hdis⟩ := ih (by omega)
    have hUc : (S.image a ∪ S.image b).card ≤ 2 * S.card := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 := Finset.card_image_le (s := S) (f := a)
      have h2 := Finset.card_image_le (s := S) (f := b)
      omega
    generalize hU : S.image a ∪ S.image b = U at hUc
    have haU : ∀ i ∈ S, a i ∈ U := fun i hi =>
      hU ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem a hi)
    have hbU : ∀ i ∈ S, b i ∈ U := fun i hi =>
      hU ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem b hi)
    have hVc : (Finset.univ.filter (fun x => flipBit (τ i0) x ∈ U)).card ≤ U.card :=
      Finset.card_le_card_of_injOn (flipBit (τ i0))
        (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ y _ h => flipBit_injective _ h)
    have hex : ∃ x, x ∉ U ∪ Finset.univ.filter (fun x => flipBit (τ i0) x ∈ U) := by
      by_contra hcon
      push Not at hcon
      have h1 : (Finset.univ : Finset (Fin (2 ^ l))).card
          ≤ (U ∪ Finset.univ.filter (fun x => flipBit (τ i0) x ∈ U)).card :=
        Finset.card_le_card fun x _ => hcon x
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_union_le U (Finset.univ.filter (fun x => flipBit (τ i0) x ∈ U))
      omega
    obtain ⟨x, hx⟩ := hex
    have hxU : x ∉ U := fun h => hx (Finset.mem_union_left _ h)
    have hfU : flipBit (τ i0) x ∉ U := fun h =>
      hx (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    refine ⟨fun i => if i = i0 then x else a i,
      fun i => if i = i0 then flipBit (τ i0) x else b i, ?_, ?_⟩
    · intro i hi t
      rcases Finset.mem_insert.mp hi with heq | hi
      · simp only [ite_eq_left heq]
        rw [heq]
        exact flipBit_testBit _ _ _
      · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
        simp only [ite_eq_right hne]
        exact hbit i hi t
    · intro i hi i' hi' hii
      rcases Finset.mem_insert.mp hi with heq | hi <;>
        rcases Finset.mem_insert.mp hi' with heq' | hi'
      · exact absurd (heq.trans heq'.symm) hii
      · have hne : i' ≠ i0 := fun h => hi0 (h ▸ hi')
        simp only [ite_eq_left heq, ite_eq_right hne]
        exact ⟨fun h => hxU (by rw [h]; exact haU i' hi'),
          fun h => hxU (by rw [h]; exact hbU i' hi'),
          fun h => hfU (by rw [h]; exact hbU i' hi')⟩
      · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
        simp only [ite_eq_left heq', ite_eq_right hne]
        exact ⟨fun h => hxU (by rw [← h]; exact haU i hi),
          fun h => hfU (by rw [← h]; exact haU i hi),
          fun h => hfU (by rw [← h]; exact hbU i hi)⟩
      · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
        have hne' : i' ≠ i0 := fun h => hi0 (h ▸ hi')
        simp only [ite_eq_right hne, ite_eq_right hne']
        exact hdis i hi i' hi' hii

/-! ### The main argument -/

/-- The core of the argument on a fixed top monomial `u0` with rows `S` and bits `τ`: the
decoded polynomial is not derivable from the functional pigeonhole system. -/
theorem chainB_core {m l k B : ℕ} (f : MvPolynomial (Fin m × Fin l) (ZMod 2))
    (hk : 1 ≤ k) (hkB : k ≤ B) (h4 : 4 * (k - 1) < 2 ^ l) (hB : 2 * B + 2 * k ≤ 2 ^ l + 1)
    (S : Finset (Fin m)) (hSk : S.card ≤ k) (τ : Fin m → Fin l)
    (u0 : (Fin m × Fin l) →₀ ℕ)
    (hrow : ∀ u ∈ f.support, ∀ i : Fin m, ∑ t : Fin l, u (i, t) ≤ 1)
    (hu0 : u0 ∈ f.support)
    (hS1 : ∀ i ∈ S, u0 (i, τ i) ≠ 0) (hS0 : ∀ i ∉ S, ∀ t, u0 (i, t) = 0)
    (hother : ∀ u ∈ f.support, u ≠ u0 → ∃ i ∈ S, u (i, τ i) = 0) :
    ¬ PCDerivable (funPHPSystem m (2 ^ l)) B (bitDecoder m l f) := by
  intro hder
  obtain ⟨a, b, hbit, hdis⟩ := exists_pairs τ S (by
    have : 4 * (S.card - 1) ≤ 4 * (k - 1) := by omega
    omega)
  have hUc : (S.image a ∪ S.image b).card ≤ 2 * S.card := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := S) (f := a)
    have h2 := Finset.card_image_le (s := S) (f := b)
    omega
  generalize hU : S.image a ∪ S.image b = U at hUc
  have haU : ∀ i ∈ S, a i ∈ U := fun i hi =>
    hU ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem a hi)
  have hbU : ∀ i ∈ S, b i ∈ U := fun i hi =>
    hU ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem b hi)
  have hcard : Uᶜ.card = 2 ^ l - U.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have he : Function.Injective (fun j' : Fin Uᶜ.card => Uᶜ.orderEmbOfFin rfl j') :=
    (Uᶜ.orderEmbOfFin rfl).injective
  have heU : ∀ j' : Fin Uᶜ.card, Uᶜ.orderEmbOfFin rfl j' ∉ U := fun j' =>
    Finset.mem_compl.mp (Finset.orderEmbOfFin_mem _ _ _)
  have hE : ∀ E ∈ S.powerset, PCDerivable (funPHPSystem m Uᶜ.card) B
      (aeval (theta S (fun i => if i ∈ E then b i else a i)
        (fun j' : Fin Uᶜ.card => Uᶜ.orderEmbOfFin rfl j')) f) := by
    intro E _
    rw [← restr_bitDecoder]
    refine restr_derivable S _ _ he ?_ ?_ hder
    · intro i hi i' hi' hii
      obtain ⟨h1, h2, h3⟩ := hdis i hi i' hi' hii
      obtain ⟨-, h2', -⟩ := hdis i' hi' i hi (Ne.symm hii)
      split_ifs
      exacts [h3, fun h => h2' h.symm, h2, h1]
    · intro i hi j' h
      have hmem : (if i ∈ E then b i else a i) ∈ U := by
        split_ifs
        exacts [hbU i hi, haU i hi]
      exact heU j' (by rw [h]; exact hmem)
  have h1 := pcDerivable_sum S.powerset _ hE
  rw [sum_theta_eq_one S τ a b _ f u0 hrow hu0 hS1 hS0 hother hbit] at h1
  exact funPHP_no_pc_refutation m Uᶜ.card B (by omega) (by omega) h1

/-- Chain link B, given the decoder lemma (chain link A) as a hypothesis: under the stated
numeric conditions no nonzero row-linear polynomial of degree at most `k` is derivable in
degree `B` from the bit pigeonhole system. -/
theorem chainB_of_decoder
    (hdec : ∀ (m l B : ℕ) (q : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l →
      PCDerivable (bitPHPSystem m l) B q →
      PCDerivable (funPHPSystem m (2 ^ l)) B (bitDecoder m l q)) :
    ∀ (m l k B : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → 1 ≤ k → k ≤ B →
      4 * (k - 1) < 2 ^ l → 2 * B + 2 * k ≤ 2 ^ l + 1 → f ≠ 0 →
      PEqualNP.ProofComplexity.IsRowLinear m l k f →
      ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) B f := by
  intro m l k B f hl hk hkB h4 hB hf hrl hder
  classical
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hf
  obtain ⟨u0, hu0, hmax⟩ :=
    Finset.exists_max_image f.support (fun u => u.sum fun _ e => e) hne
  have hrow : ∀ u ∈ f.support, ∀ i : Fin m, ∑ t : Fin l, u (i, t) ≤ 1 := fun u hu =>
    (hrl u hu).2
  have hdeg : ∀ u : (Fin m × Fin l) →₀ ℕ,
      (u.sum fun _ e => e) = ∑ i : Fin m, ∑ t : Fin l, u (i, t) := fun u => by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  have hlpos : 0 < l := by omega
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin m), ∀ i, i ∈ S ↔ ∃ t, u0 (i, t) ≠ 0 :=
    ⟨Finset.univ.filter fun i => ∃ t, u0 (i, t) ≠ 0, fun i => by simp⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin m → Fin l, ∀ i ∈ S, u0 (i, τ i) ≠ 0 := by
    refine ⟨fun i => if h : ∃ t, u0 (i, t) ≠ 0 then h.choose else ⟨0, hlpos⟩, fun i hi => ?_⟩
    have h : ∃ t, u0 (i, t) ≠ 0 := (hSdef i).1 hi
    simp only [dite_eq_left h]
    exact h.choose_spec
  have hS0 : ∀ i ∉ S, ∀ t, u0 (i, t) = 0 := by
    intro i hi t
    by_contra h
    exact hi ((hSdef i).2 ⟨t, h⟩)
  have hrs0 : ∀ i, ∑ t : Fin l, u0 (i, t) = if i ∈ S then 1 else 0 := by
    intro i
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      have h1 := hrow u0 hu0 i
      have h2 := Finset.single_le_sum (f := fun t => u0 (i, t)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (τ i))
      have h3 := hτ i hi
      omega
    · rw [ite_eq_right hi]
      exact Finset.sum_eq_zero fun t _ => hS0 i hi t
  have hSk : S.card ≤ k := by
    have h1 := (hrl u0 hu0).1
    rw [hdeg] at h1
    simp only [hrs0] at h1
    simpa using h1
  have hother : ∀ u ∈ f.support, u ≠ u0 → ∃ i ∈ S, u (i, τ i) = 0 := by
    intro u hu hne
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : ∀ i, ∑ t : Fin l, u0 (i, t) ≤ ∑ t : Fin l, u (i, t) := by
      intro i
      rw [hrs0]
      split_ifs with hi
      · have h2 := Finset.single_le_sum (f := fun t => u (i, t)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ (τ i))
        have h3 := hcon i hi
        omega
      · exact Nat.zero_le _
    have htot : ∑ i : Fin m, ∑ t : Fin l, u (i, t) ≤ ∑ i : Fin m, ∑ t : Fin l, u0 (i, t) := by
      rw [← hdeg, ← hdeg]
      exact hmax u hu
    have heq : ∀ i, ∑ t : Fin l, u (i, t) = ∑ t : Fin l, u0 (i, t) := by
      intro i
      by_contra hlt
      have hlt' : ∑ i : Fin m, ∑ t : Fin l, u0 (i, t) < ∑ i : Fin m, ∑ t : Fin l, u (i, t) :=
        Finset.sum_lt_sum (fun i _ => hle i)
          ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hle i) (Ne.symm hlt)⟩
      omega
    ext ⟨i, t⟩
    by_cases hi : i ∈ S
    · rcases row_cases (fun t => u (i, t)) (hrow u hu i) with h0 | ⟨t1, h1⟩
      · exact absurd (h0 (τ i)) (hcon i hi)
      · rcases row_cases (fun t => u0 (i, t)) (hrow u0 hu0 i) with h0' | ⟨t2, h2⟩
        · exact absurd (h0' (τ i)) (hτ i hi)
        · have e1 : t1 = τ i := by
            by_contra h
            exact hcon i hi (by rw [h1 (τ i), ite_eq_right (Ne.symm h)])
          have e2 : t2 = τ i := by
            by_contra h
            exact hτ i hi (by rw [h2 (τ i), ite_eq_right (Ne.symm h)])
          rw [h1 t, h2 t, e1, e2]
    · have hz : ∑ t : Fin l, u (i, t) = 0 := by rw [heq, hrs0, ite_eq_right hi]
      have h1 := (Finset.sum_eq_zero_iff.mp hz) t (Finset.mem_univ t)
      rw [h1, hS0 i hi t]
  exact chainB_core f hk hkB h4 hB S hSk τ u0 hrow hu0 hτ hS0 hother (hdec m l B f hl hder)

end PEqualNP.ProofComplexity.Helpers
