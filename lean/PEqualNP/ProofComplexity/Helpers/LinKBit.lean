import PEqualNP.ProofComplexity.Helpers.LinKWire
import PEqualNP.ProofComplexity.Helpers.LinKSim
import PEqualNP.ProofComplexity.Helpers.BoolVanish
import PEqualNP.ProofComplexity.Helpers.DegSizeSim
import PEqualNP.ProofComplexity.Helpers.ExpBeatsPoly
import PEqualNP.ProofComplexity.L027
import PEqualNP.ProofComplexity.L031
import PEqualNP.Defs.ProofComplexityBit

/-!
# L-pcx-061: Res(k, ⊕) (termwise weakening) is not polynomially bounded on bit pigeonhole

The chain:

* `clause_derivable`: the polynomial of every clause of `BPHP m l` is derivable from
  `bitPHPSystem m l` in degree `3 * l`. With `P` the clause polynomial of pigeons `i`, `i'` and
  hole `α`, and `A` the axiom `∏ t, (1 + X (i, t) + X (i', t))`: `P = P * A + P * (1 + A)`,
  the first summand is a multiple of an axiom and the second vanishes on the cube.
* `transfer`: a degree `D` derivation from `cnfSystem (BPHP m l)` replays from
  `bitPHPSystem m l` in degree `D + 3 * l`.
* `bphp_not_refutable`: with the decoder L-pcx-031 and the degree bound L-pcx-027, the system
  `cnfSystem (BPHP m l)` has no refutation of degree `D` when `2 * (D + 3 * l) ≤ 2 ^ l + 1`.
* `bit_not_poly`: the general degree to size theorem for Res(k, ⊕) at degree `2 ^ (l - 2)`,
  and an `l` at which the exponential bound exceeds the polynomial.
-/

namespace PEqualNP.ProofComplexity.LinKBit

open MvPolynomial PEqualNP.ProofComplexity

/-- Every clause of the bit pigeonhole formula has at most `2 * l` literals. -/
theorem bphp_width {m l : ℕ} : ∀ C ∈ BPHP m l, C.card ≤ 2 * l := by
  rintro C ⟨i, i', α, -, rfl⟩
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin l)))
    (f := fun b : Fin l => (((i, b), !α b) : Literal (Fin m × Fin l)))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin l)))
    (f := fun b : Fin l => (((i', b), !α b) : Literal (Fin m × Fin l)))
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

/-- The two-element field fact behind `clause_eval`. -/
theorem z2_fact : ∀ (b : Bool) (u v : ZMod 2),
    (if (!b) = true then 1 + u else u) ≠ 0 → (if (!b) = true then 1 + v else v) ≠ 0 →
    1 + u + v = 1 := by decide

/-- Where the polynomial of the clause of `i`, `i'`, `α` is not zero, both pigeons sit in the
hole `α`, so the bit pigeonhole axiom of `i`, `i'` is `1`. -/
theorem clause_eval {m l : ℕ} (i i' : Fin m) (α : Fin l → Bool) (x : Fin m × Fin l → ZMod 2)
    (h : eval x (clausePoly (Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
        Finset.univ.image (fun b : Fin l => ((i', b), !α b)))) ≠ 0) :
    eval x (∏ t : Fin l, (1 + X (i, t) + X (i', t))) = 1 := by
  unfold clausePoly at h
  rw [map_prod] at h
  have hne := Finset.prod_ne_zero_iff.mp h
  rw [map_prod]
  refine Finset.prod_eq_one fun t _ => ?_
  have a1 := hne ((i, t), !α t)
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
  have a2 := hne ((i', t), !α t)
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
  simp only [apply_ite (eval x), map_add, map_one, eval_X] at a1 a2
  simp only [map_add, map_one, eval_X]
  exact z2_fact (α t) _ _ a1 a2

/-- The polynomial of every clause of the bit pigeonhole formula is derivable from the bit
pigeonhole polynomial system in degree `3 * l`. -/
theorem clause_derivable {m l : ℕ} :
    ∀ C ∈ BPHP m l, PCDerivable (bitPHPSystem m l) (3 * l) (clausePoly C) := by
  intro C hC
  have hw := bphp_width C hC
  have hPdeg : (clausePoly C).totalDegree ≤ 2 * l :=
    (DegSizeSim.totalDegree_clausePoly_le C).trans hw
  obtain ⟨i, i', α, hne, hCeq⟩ := hC
  obtain ⟨A, hA⟩ : ∃ A : MvPolynomial (Fin m × Fin l) (ZMod 2),
      A = ∏ t : Fin l, (1 + X (i, t) + X (i', t)) := ⟨_, rfl⟩
  have hAdeg : A.totalDegree ≤ l := by
    rw [hA]
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ t : Fin l,
          (1 + X (i, t) + X (i', t) : MvPolynomial (Fin m × Fin l) (ZMod 2)).totalDegree
        ≤ ∑ _t : Fin l, 1 := Finset.sum_le_sum fun t _ =>
          (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
            (max_le (by simp) (by simp))) (by simp))
      _ = l := by simp
  have hAax : PCDerivable (bitPHPSystem m l) l A :=
    .ax (Or.inr ⟨i, i', hne, hA⟩) hAdeg
  have h1 : PCDerivable (bitPHPSystem m l) (3 * l) (clausePoly C * A) :=
    Helpers.pcDerivable_mono (Helpers.pcDerivable_mul_left hAax (clausePoly C))
      (max_le (by omega) (by omega)) subset_rfl
  have h1A : (1 + A).totalDegree ≤ l :=
    (totalDegree_add _ _).trans (max_le (by simp) hAdeg)
  have h2 : PCDerivable (bitPHPSystem m l) (3 * l) (clausePoly C * (1 + A)) := by
    refine Helpers.BoolVanish.vanish_derivable _ _ _ _ (fun v => Or.inl ⟨v, rfl⟩)
      ((totalDegree_mul _ _).trans (by omega)) (fun x => ?_)
    by_cases h : eval x (clausePoly C) = 0
    · rw [map_mul, h, zero_mul]
    · have hA1 : eval x A = 1 := by
        rw [hA]
        exact clause_eval i i' α x (hCeq ▸ h)
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [map_mul, map_add, map_one, hA1, h11, mul_zero]
  have e : clausePoly C = clausePoly C * A + clausePoly C * (1 + A) := by
    have h0 : clausePoly C * A + clausePoly C * A = 0 := CharTwo.add_self_eq_zero _
    linear_combination -h0
  rw [e]
  exact .add h1 h2

/-- A polynomial calculus derivation from the clause system of bit pigeonhole replays from the
bit pigeonhole polynomial system, with `3 * l` more degree. -/
theorem transfer {m l D : ℕ} {p : MvPolynomial (Fin m × Fin l) (ZMod 2)}
    (h : PCDerivable (cnfSystem (BPHP m l)) D p) :
    PCDerivable (bitPHPSystem m l) (D + 3 * l) p := by
  have hr := Helpers.pcDerivable_replay (F := cnfSystem (BPHP m l)) (G := bitPHPSystem m l)
    (T := 1) (D := D) (s := 3 * l) X (fun j => by simp) 1 (by simp) ?_ h
  · simpa only [one_mul, bind₁_X_left, AlgHom.coe_id, id_eq] using hr
  · intro a ha hdeg
    simp only [one_mul, bind₁_X_left, AlgHom.coe_id, id_eq]
    rcases ha with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
    · exact .ax (Or.inl ⟨v, rfl⟩) (hdeg.trans (by omega))
    · exact Helpers.pcDerivable_mono (clause_derivable C hC) (by omega) subset_rfl

/-- The clause system of bit pigeonhole has no polynomial calculus refutation of degree `D`
when `2 * (D + 3 * l) ≤ 2 ^ l + 1`. -/
theorem bphp_not_refutable (m l D : ℕ) (hl : 2 ≤ l) (hD : 2 * (D + 3 * l) ≤ 2 ^ l + 1) :
    ¬ PCRefutable (cnfSystem (BPHP m l)) D := by
  intro h
  have h1 : PCDerivable (bitPHPSystem m l) (D + 3 * l) 1 := transfer h
  have h2 := PEqualNP.ProofComplexity.L031 m l (D + 3 * l) 1 hl h1
  rw [map_one] at h2
  exact PEqualNP.ProofComplexity.L027 m (2 ^ l) (D + 3 * l) Nat.one_le_two_pow hD h2

/-- A power of two eventually exceeds any constant times any fixed power. -/
theorem exists_l (M K : ℕ) : ∃ l : ℕ, 7 ≤ l ∧ M * l ^ K ≤ 2 ^ l := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt K (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
  have hev := Filter.Tendsto.eventually_lt_const hpos ht
  obtain ⟨l, hl, h7⟩ := (hev.and (Filter.eventually_ge_atTop 7)).exists
  refine ⟨l, h7, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at hl
  have hnn : (0 : ℝ) ≤ (l : ℝ) ^ K := by positivity
  have : (M : ℝ) * (l : ℝ) ^ K ≤ (2 : ℝ) ^ l := by nlinarith
  exact_mod_cast this

/-- L-pcx-061 from the general degree to size theorem for Res(k, ⊕). -/
theorem bit_not_poly (hL : LinKFinal.StmtLinK) :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinKLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval ((2 ^ l + 1) * l) < π.length := by
  intro k hk p
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨l, h7, hl⟩ := exists_l ((C + 3 * d) * (64 * k * 32 ^ k) + 64 * k + 32) (k + 1)
  refine ⟨l, fun π hπ => ?_⟩
  -- the natural number side
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = l ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = 2 ^ l := ⟨_, rfl⟩
  rw [← hLdef, ← hNdef] at hl
  have hL1 : 1 ≤ L := hLdef ▸ Nat.one_le_pow _ _ (by omega)
  have hlL : l ≤ L := by
    rw [hLdef]
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hexp : ((C + 3 * d) * (64 * k * 32 ^ k) + 64 * k + 32) * L =
      (C + 3 * d) * (64 * k * 32 ^ k) * L + 64 * k * L + 32 * L := by ring
  have hk1 : 64 * k ≤ 64 * k * L := Nat.le_mul_of_pos_right _ (by omega)
  have hA : (C + 3 * d) * (64 * k * 32 ^ k) * L ≤ N := by omega
  have hB : 64 * k ≤ N := by omega
  have hC32 : 32 * l ≤ N := by omega
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 4 * D = N := by
    refine ⟨2 ^ (l - 2), ?_⟩
    have e : l = (l - 2) + 2 := by omega
    rw [hNdef]
    conv_rhs => rw [e, pow_add]
    ring
  have hnr : ¬ PCRefutable (cnfSystem (BPHP (2 ^ l + 1) l)) D :=
    bphp_not_refutable _ l D (by omega) (by omega)
  have hsize := hL (Fin (2 ^ l + 1) × Fin l) (BPHP (2 ^ l + 1) l) π k (2 * l) D
    bphp_width hk (by omega) (by omega) hnr hπ
  simp only [Fintype.card_prod, Fintype.card_fin] at hsize
  -- the polynomial at the number of variables
  have hl2 : l ≤ N := by omega
  have h2N : 2 ≤ N := by omega
  have hcardN : (2 ^ l + 1) * l ≤ N ^ 3 := by
    rw [← hNdef]
    calc (N + 1) * l ≤ (2 * N) * N := Nat.mul_le_mul (by omega) hl2
      _ ≤ (N * N) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2N)
      _ = N ^ 3 := by ring
  have hcard1 : 1 ≤ (2 ^ l + 1) * l := Nat.mul_pos (by positivity) (by omega)
  have hpolyN : p.eval ((2 ^ l + 1) * l) ≤ C * (N ^ 3) ^ d := by
    have h1 := Helpers.poly_eval_le_coeffSum_mul_pow p ((2 ^ l + 1) * l) hcard1
    rw [← hC, ← hd] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcardN d))
  -- the real side
  have hpolyR : ((p.eval ((2 ^ l + 1) * l) : ℕ) : ℝ) ≤ (C : ℝ) * (((2 : ℝ) ^ l) ^ 3) ^ d := by
    rw [hNdef] at hpolyN
    exact_mod_cast hpolyN
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpd : (((2 : ℝ) ^ l) ^ 3) ^ d ≤ Real.exp (3 * (l : ℝ) * (d : ℝ)) := by
    rw [← pow_mul, ← pow_mul]
    have e : Real.exp (3 * (l : ℝ) * (d : ℝ)) = Real.exp 1 ^ (l * (3 * d)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) h2exp _
  have hCexp : (C : ℝ) < Real.exp (C : ℝ) := by
    have := Real.add_one_le_exp (C : ℝ)
    linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hNR : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have hDR : 4 * (D : ℝ) = (2 : ℝ) ^ l := by
    rw [hNdef] at hD
    exact_mod_cast hD
  have hAR : ((C : ℝ) + 3 * (d : ℝ)) * (64 * (k : ℝ) * (32 : ℝ) ^ k) * (l : ℝ) ^ (k + 1) ≤
      (2 : ℝ) ^ l := by
    rw [hNdef, hLdef] at hA
    exact_mod_cast hA
  have key : ((C : ℝ) + 3 * (l : ℝ) * (d : ℝ)) * (64 * (k : ℝ) * (32 * (l : ℝ)) ^ k) ≤
      (2 : ℝ) ^ l := by
    calc ((C : ℝ) + 3 * (l : ℝ) * (d : ℝ)) * (64 * (k : ℝ) * (32 * (l : ℝ)) ^ k)
        ≤ (((C : ℝ) + 3 * (d : ℝ)) * (l : ℝ)) * (64 * (k : ℝ) * (32 * (l : ℝ)) ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_nonneg hCnn (sub_nonneg.mpr hlR)]
      _ = ((C : ℝ) + 3 * (d : ℝ)) * (64 * (k : ℝ) * (32 : ℝ) ^ k) * (l : ℝ) ^ (k + 1) := by
          rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ l := hAR
  have hfirst : (D : ℝ) / (16 * (k : ℝ)) = (2 : ℝ) ^ l / (64 * (k : ℝ)) := by
    rw [← hDR]; field_simp; ring
  have hbase : 1 / (32 * (l : ℝ)) ≤ (D : ℝ) / (4 * (((2 : ℝ) ^ l + 1) * (l : ℝ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNR) hlpos.le]
  have hpow : (1 / (32 * (l : ℝ))) ^ k ≤
      ((D : ℝ) / (4 * (((2 : ℝ) ^ l + 1) * (l : ℝ)))) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  have hexpo : (C : ℝ) + 3 * (l : ℝ) * (d : ℝ) ≤
      (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (((2 : ℝ) ^ l + 1) * (l : ℝ)))) ^ k := by
    have h1 : (C : ℝ) + 3 * (l : ℝ) * (d : ℝ) ≤
        (2 : ℝ) ^ l / (64 * (k : ℝ)) * (1 / (32 * (l : ℝ))) ^ k := by
      rw [one_div_pow, div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
      exact key
    rw [hfirst]
    exact h1.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  push_cast at hsize
  have hfin : ((p.eval ((2 ^ l + 1) * l) : ℕ) : ℝ) < (π.length : ℝ) := by
    calc ((p.eval ((2 ^ l + 1) * l) : ℕ) : ℝ)
        ≤ (C : ℝ) * (((2 : ℝ) ^ l) ^ 3) ^ d := hpolyR
      _ ≤ (C : ℝ) * Real.exp (3 * (l : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hpd hCnn
      _ < Real.exp (C : ℝ) * Real.exp (3 * (l : ℝ) * (d : ℝ)) :=
          mul_lt_mul_of_pos_right hCexp (Real.exp_pos _)
      _ = Real.exp ((C : ℝ) + 3 * (l : ℝ) * (d : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hexpo
      _ ≤ (π.length : ℝ) := hsize
  exact_mod_cast hfin

/-- L-pcx-061, with the general theorem supplied by the checked simulation. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinKLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval ((2 ^ l + 1) * l) < π.length :=
  bit_not_poly (LinKWire.general LinKSim.simulation_refutation)

end PEqualNP.ProofComplexity.LinKBit
