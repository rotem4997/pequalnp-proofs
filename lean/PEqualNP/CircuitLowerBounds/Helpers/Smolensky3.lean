import PEqualNP.CircuitLowerBounds.Helpers.Smolensky0
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky1
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky2

/-!
# MOD q is not in AC0[p], from the approximation statement

Helper module (proofs only, no statement may use it). The assembly of the Razborov and
Smolensky bound: padding the input with `j` true bits turns a circuit for "the count is
divisible by `q`" into the indicator of every residue; the approximating polynomials of the
residues combine, over a field with a `q`-th root of unity `ω`, into one low-degree polynomial
that agrees with `ω ^ count` on most inputs; the counting step and the numbers finish.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds MvPolynomial

/-- The input `x` followed by `q` more bits, the first `j` of them true. -/
def smolPad {n : ℕ} (q j : ℕ) (x : Fin n → Bool) : Fin (n + q) → Bool :=
  Fin.append x (fun i => decide (i.val < j))

theorem smol_count_tail (q j : ℕ) :
    (List.ofFn (fun i : Fin q => decide (i.val < j))).count true = min j q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : q < j
    · simp [h]; omega
    · simp [h]; omega

theorem smol_count_pad {n : ℕ} (q j : ℕ) (hj : j ≤ q) (x : Fin n → Bool) :
    (List.ofFn (smolPad q j x)).count true = (List.ofFn x).count true + j := by
  rw [smolPad, List.ofFn_fin_append, List.count_append, smol_count_tail, min_eq_left hj]

theorem smolPad_injective {n : ℕ} (q j : ℕ) : Function.Injective (smolPad (n := n) q j) := by
  intro x x' h
  funext i
  have := congrFun h (Fin.castAdd q i)
  simpa [smolPad, Fin.append_left] using this

/-- The inputs none of whose `q` paddings is in `E` are all but `q * |E|`. -/
theorem smol_cover {n : ℕ} (q : ℕ) (E : Finset (Fin (n + q) → Bool)) :
    2 ^ n ≤ (Finset.univ.filter fun x : Fin n → Bool =>
      ∀ j ∈ Finset.range q, smolPad q j x ∉ E).card + q * E.card := by
  classical
  have hsub : (Finset.univ : Finset (Fin n → Bool)) ⊆
      (Finset.univ.filter fun x : Fin n → Bool => ∀ j ∈ Finset.range q, smolPad q j x ∉ E) ∪
        (Finset.range q).biUnion fun j => Finset.univ.filter fun x => smolPad q j x ∈ E := by
    intro x _
    by_cases h : ∀ j ∈ Finset.range q, smolPad q j x ∉ E
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · push_neg at h
      obtain ⟨j, hj, hjE⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, by simp [hjE]⟩)
  have h1 : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  have h2 : ∀ j ∈ Finset.range q,
      (Finset.univ.filter fun x : Fin n → Bool => smolPad q j x ∈ E).card ≤ E.card := by
    intro j _
    refine Finset.card_le_card_of_injOn (smolPad q j) ?_ (smolPad_injective q j).injOn
    intro x hx
    simpa using hx
  calc 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := h1.symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ + ((Finset.range q).biUnion fun j =>
          Finset.univ.filter fun x : Fin n → Bool => smolPad q j x ∈ E).card :=
        Finset.card_union_le _ _
    _ ≤ _ + ∑ j ∈ Finset.range q,
          (Finset.univ.filter fun x : Fin n → Bool => smolPad q j x ∈ E).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ _ + ∑ _j ∈ Finset.range q, E.card := Nat.add_le_add_left (Finset.sum_le_sum h2) _
    _ = _ := by simp

section

variable {K : Type*} [Field K]

theorem smol_prod_eq_pow (ω : K) : ∀ (n : ℕ) (x : Fin n → Bool),
    ∏ i, (if x i = true then ω else 1) = ω ^ (List.ofFn x).count true := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [Fin.prod_univ_succ, List.ofFn_succ, ih, List.count_cons]
    cases h : x 0 <;> simp [pow_succ, mul_comm]

/-- A power of a `q`-th root of unity is the combination of the indicators of the residues. -/
theorem smol_residue_sum (ω : K) (q c : ℕ) (hq : 0 < q) (hω : ω ^ q = 1) :
    ω ^ c = ∑ j ∈ Finset.range q, (ω⁻¹) ^ j * (if (c + j) % q = 0 then (1 : K) else 0) := by
  have hj0 : (q - c % q) % q < q := Nat.mod_lt _ hq
  have hmod : (c + (q - c % q) % q) % q = 0 := by
    rw [Nat.add_mod_mod]
    have h1 := Nat.div_add_mod c q
    have h2 := Nat.mod_lt c hq
    have h3 : c + (q - c % q) = q * (c / q + 1) := by
      rw [mul_add, mul_one]
      omega
    rw [h3, Nat.mul_mod_right]
  rw [Finset.sum_eq_single ((q - c % q) % q)]
  · rw [if_pos hmod, mul_one, inv_pow]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hmod
    rw [ht, pow_mul, hω, one_pow]
  · intro j hj hne
    rw [if_neg, mul_zero]
    intro h
    apply hne
    have h1 : c + j ≡ c + (q - c % q) % q [MOD q] := by
      rw [Nat.ModEq, h, hmod]
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' c h1) (Finset.mem_range.mp hj) hj0
  · intro h
    exact absurd (Finset.mem_range.mpr hj0) h

variable {R : Type*} [CommRing R]

/-- Substituting polynomials of degree at most one does not raise the total degree. -/
theorem smol_subst_deg {N n : ℕ} (φ : R →+* K) (σ : Fin N → MvPolynomial (Fin n) K)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (F : MvPolynomial (Fin N) R) :
    (eval₂ (C.comp φ) σ F).totalDegree ≤ F.totalDegree := by
  rw [eval₂_eq]
  refine totalDegree_finsetSum_le fun d hd => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [RingHom.comp_apply, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_totalDegree hd)
  refine (totalDegree_pow _ _).trans ?_
  calc d i * (σ i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hσ i)
    _ = d i := mul_one _

theorem smol_subst_eval {N n : ℕ} (φ : R →+* K) (σ : Fin N → MvPolynomial (Fin n) K)
    (F : MvPolynomial (Fin N) R) (f : Fin n → K) (b : Fin N → R)
    (h : ∀ i, eval f (σ i) = φ (b i)) :
    eval f (eval₂ (C.comp φ) σ F) = φ (eval b F) := by
  rw [eval₂_eq, eval_eq b F]
  simp [map_sum, map_prod, h]

/-- Steps 1 and 2: from a polynomial in `n + q` variables that computes, on the paddings of
the points of `A`, the indicator of "the count is divisible by `q`", a polynomial in `n`
variables of no larger degree that computes `ω ^ count` on `A`. -/
theorem smol_combine {n : ℕ} (q : ℕ) (hq : 0 < q) (φ : R →+* K) (ω : K) (hω : ω ^ q = 1)
    (F : MvPolynomial (Fin (n + q)) R) (A : Finset (Fin n → Bool))
    (hF : ∀ x ∈ A, ∀ j ∈ Finset.range q,
      eval (fun i => if smolPad q j x i = true then (1 : R) else 0) F =
        if ((List.ofFn x).count true + j) % q = 0 then 1 else 0) :
    ∃ G : MvPolynomial (Fin n) K, G.totalDegree ≤ F.totalDegree ∧
      ∀ x ∈ A, eval (fun i => if x i = true then (1 : K) else 0) G =
        ∏ i, (if x i = true then ω else 1) := by
  let σ : ℕ → Fin (n + q) → MvPolynomial (Fin n) K := fun j =>
    Fin.append (fun i => X i) (fun i => if i.val < j then 1 else 0)
  have hσ : ∀ j i, (σ j i).totalDegree ≤ 1 := by
    intro j i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [σ, Fin.append_left]
    · simp only [σ, Fin.append_right]
      split_ifs <;> simp
  refine ⟨∑ j ∈ Finset.range q, C ((ω⁻¹) ^ j) * eval₂ (C.comp φ) (σ j) F, ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact smol_subst_deg φ (σ j) (hσ j) F
  · intro x hx
    rw [smol_prod_eq_pow, smol_residue_sum ω q _ hq hω, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_mul, eval_C]
    congr 1
    rw [smol_subst_eval φ (σ j) F _ (fun i => if smolPad q j x i = true then (1 : R) else 0),
      hF x hx j hj]
    · split_ifs <;> simp
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [σ, smolPad, Fin.append_left, eval_X]
        split_ifs <;> simp
      · simp only [σ, smolPad, Fin.append_right, decide_eq_true_eq]
        split_ifs <;> simp

end

/-- MOD `q` is not in AC0[`p`] for distinct primes `p` and `q`, given the approximation of
constant-depth circuits with MOD `p` gates by polynomials of low degree. -/
theorem modq_not_in_ac0p_of (hA : ApproxStatement) :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
      ({x : List Bool | x.count true % q = 0} : Language Bool) ∉
        PEqualNP.CircuitLowerBounds.AC0Mod p := by
  intro p q hp hq hpq hmem
  obtain ⟨P, d, hL⟩ := hmem
  obtain ⟨m, l, hl1, hsz, hdeg⟩ := exists_params P p q d
  obtain ⟨Cc, hgates, hsize, hdepth, hdec⟩ := hL (2 * m + 1 + q)
  obtain ⟨F, hFdeg, hErr⟩ := hA p hp (2 * m + 1 + q) (P.eval (2 * m + 1 + q)) d l Cc
    (fun g hg => (hgates g hg).1) hsize hdepth hl1
  haveI : Fact p.Prime := ⟨hp⟩
  have hqp : (q : ZMod p) ≠ 0 := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((ZMod.natCast_eq_zero_iff q p).mp h))
  haveI : NeZero (q : ZMod p) := ⟨hqp⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure (ZMod p)) q
  have hωq : ω ^ q = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one hq.one_lt
  have hω0 : ω ≠ 0 := hω.ne_zero hq.ne_zero
  set E := (Finset.univ.filter fun x : Fin (2 * m + 1 + q) → Bool =>
    MvPolynomial.eval (fun i => if x i = true then (1 : ZMod p) else 0) F ≠
      (if Cc.eval (List.ofFn x) = true then (1 : ZMod p) else 0)) with hE
  set A := (Finset.univ.filter fun x : Fin (2 * m + 1) → Bool =>
    ∀ j ∈ Finset.range q, smolPad q j x ∉ E) with hAdef
  have hcover : 2 ^ (2 * m + 1) ≤ A.card + q * E.card := smol_cover q E
  have hF : ∀ x ∈ A, ∀ j ∈ Finset.range q,
      eval (fun i => if smolPad q j x i = true then (1 : ZMod p) else 0) F =
        if ((List.ofFn x).count true + j) % q = 0 then 1 else 0 := by
    intro x hx j hj
    have h1 : smolPad q j x ∉ E := (Finset.mem_filter.mp hx).2 j hj
    rw [hE, Finset.mem_filter, not_and, not_not] at h1
    rw [h1 (Finset.mem_univ _)]
    refine if_congr ?_ rfl rfl
    rw [hdec (List.ofFn (smolPad q j x)) (by simp)]
    show (List.ofFn (smolPad q j x)).count true % q = 0 ↔ _
    rw [smol_count_pad q j (Finset.mem_range.mp hj).le]
  obtain ⟨G, hGdeg, hG⟩ := smol_combine q hq.pos
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ω hωq F A hF
  have hcard := smolensky_card_le ω hω0 hω1 (((p - 1) * l) ^ d) G (hGdeg.trans hFdeg) A hG
  rw [show (2 * m + 1) / 2 = m by omega] at hcard
  have hcard' := hcard.trans (sum_choose_le m (((p - 1) * l) ^ d))
  have hcb := centralBinom_sq_mul_le (m + 1)
  -- the numbers
  generalize ((p - 1) * l) ^ d = D at hdeg hcard'
  generalize Nat.centralBinom (m + 1) = c at hcard' hcb
  generalize A.card = a at hcover hcard'
  generalize E.card = e at hcover hErr
  generalize P.eval (2 * m + 1 + q) = s at hsz hErr
  have hT : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have h1 : 2 ^ l * (4 * q * e) ≤ 2 ^ l * (2 * 4 ^ m) := by
    calc 2 ^ l * (4 * q * e) = 4 * q * (e * 2 ^ l) := by ring
      _ ≤ 4 * q * (s * 2 ^ (2 * m + 1 + q)) := Nat.mul_le_mul_left _ hErr
      _ = (4 * q * s * 2 ^ q) * 2 ^ (2 * m + 1) := by
          rw [pow_add (2 : ℕ) (2 * m + 1) q]
          ring
      _ ≤ 2 ^ l * 2 ^ (2 * m + 1) := Nat.mul_le_mul_right _ hsz
      _ = 2 ^ l * (2 * 4 ^ m) := by rw [hT]
  have h2 : 4 * q * e ≤ 2 * 4 ^ m := Nat.le_of_mul_le_mul_left h1 (by positivity)
  rw [hT] at hcover
  have h3 : 4 ^ m ≤ 2 * D * c := by nlinarith
  have h4 : 16 ^ m ≤ 4 * D ^ 2 * c ^ 2 := by
    calc 16 ^ m = 4 ^ m * 4 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (2 * D * c) * (2 * D * c) := Nat.mul_le_mul h3 h3
      _ = _ := by ring
  have h5 : (2 * m + 3) * 16 ^ m ≤ 64 * D ^ 2 * 16 ^ m := by
    calc (2 * m + 3) * 16 ^ m ≤ (2 * m + 3) * (4 * D ^ 2 * c ^ 2) := Nat.mul_le_mul_left _ h4
      _ = 4 * D ^ 2 * (c ^ 2 * (2 * (m + 1) + 1)) := by ring
      _ ≤ 4 * D ^ 2 * 16 ^ (m + 1) := Nat.mul_le_mul_left _ hcb
      _ = 64 * D ^ 2 * 16 ^ m := by ring
  have h6 : 2 * m + 3 ≤ 64 * D ^ 2 := Nat.le_of_mul_le_mul_right h5 (by positivity)
  omega

end PEqualNP.CircuitLowerBounds.Helpers
