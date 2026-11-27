import PEqualNP.ProofComplexity.Helpers.DegSizePlan
import PEqualNP.ProofComplexity.Helpers.BoolVanish
import PEqualNP.ProofComplexity.Helpers.Lin

/-!
# Helpers: the closing links of the degree to size theorem for Res(⊕)

Three statements of the plan `DegSizePlan`, proved here.

* `complete_deg`: an unsatisfiable CNF formula of width at most `w` has a polynomial calculus
  refutation in every degree `D` with `w ≤ D` and `card V ≤ D`. The indicator polynomial of
  an assignment `a` is a multiple of the polynomial of a clause that `a` falsifies, of degree
  at most `card V`; one plus the sum of all indicators vanishes on the cube.
* `eta_ge`: the binomial estimate `K / (2 (n + 1)) ≤ eta n K` for `1 ≤ K ≤ n + 1`.
* `final_of_assembly_256`, `final_of_assembly`: the size bound from the assembly inequality,
  which is taken as a hypothesis. Both use `K = t = D / 4` (rounded down).
-/

namespace PEqualNP.ProofComplexity.DegSizeArith

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

section Completeness

variable {V : Type}

/-- The factor of the indicator polynomial of the assignment `a` at the variable `v`. -/
noncomputable def fac (a : V → Bool) (v : V) : MvPolynomial V (ZMod 2) :=
  if a v = true then X v else 1 + X v

theorem totalDegree_fac_le (a : V → Bool) (v : V) : (fac a v).totalDegree ≤ 1 := by
  unfold fac
  split_ifs
  · rw [totalDegree_X]
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp

theorem totalDegree_prod_fac_le (a : V → Bool) (S : Finset V) :
    (∏ v ∈ S, fac a v).totalDegree ≤ S.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ v ∈ S, (fac a v).totalDegree ≤ ∑ _v ∈ S, 1 :=
        Finset.sum_le_sum fun v _ => totalDegree_fac_le a v
    _ = S.card := by simp

theorem eval_fac (a : V → Bool) (x : V → ZMod 2) (v : V) :
    eval x (fac a v) = if (x v = 1 ↔ a v = true) then 1 else 0 := by
  unfold fac
  have hx : x v = 0 ∨ x v = 1 := by
    generalize x v = c
    revert c
    decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hx with h | h <;> cases a v <;> simp [h, h11]

/-- Completeness of polynomial calculus in degree `max (card V) w`. -/
theorem complete_deg :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → ¬ Satisfiable F → w ≤ D → Fintype.card V ≤ D →
      PCRefutable (cnfSystem F) D := by
  classical
  intro V _ _ F w D hw hunsat hwD hVD
  have hfals : ∀ a : V → Bool, ∃ A ∈ F, ¬ ClauseSat a A := by
    intro a
    by_contra hb
    exact hunsat ⟨a, fun A hA => by_contra fun hn => hb ⟨A, hA, hn⟩⟩
  have hind : ∀ a : V → Bool, PCDerivable (cnfSystem F) D (∏ v, fac a v) := by
    intro a
    obtain ⟨A, hAF, hA⟩ := hfals a
    have hne : ∀ l ∈ A, a l.1 = !l.2 := by
      intro l hl
      have h0 : ¬ a l.1 = l.2 := fun h => hA ⟨l, hl, h⟩
      revert h0
      cases a l.1 <;> cases l.2 <;> simp
    have hinj : Set.InjOn (fun l : Literal V => l.1) (↑A : Set (Literal V)) := by
      intro l hl l' hl' h
      have h' : l.1 = l'.1 := h
      have h1 := hne l hl
      have h2 := hne l' hl'
      rw [h'] at h1
      have h3 : (!l.2) = !l'.2 := h1.symm.trans h2
      have h4 : l.2 = l'.2 := by simpa using h3
      exact Prod.ext h' h4
    set S : Finset V := A.image (fun l => l.1) with hS
    have hcl : clausePoly A = ∏ v ∈ S, fac a v := by
      rw [hS, Finset.prod_image hinj]
      unfold clausePoly
      refine Finset.prod_congr rfl fun l hl => ?_
      have h1 := hne l hl
      unfold fac
      rw [h1]
      cases l.2 <;> simp
    have hsplit : ∏ v, fac a v = (∏ v ∈ Sᶜ, fac a v) * clausePoly A := by
      rw [hcl, Finset.prod_compl_mul_prod]
    have hdegc : (clausePoly A).totalDegree ≤ S.card := by
      rw [hcl]
      exact totalDegree_prod_fac_le a S
    have hScard : S.card ≤ w := Finset.card_image_le.trans (hw A hAF)
    have hax : PCDerivable (cnfSystem F) D (clausePoly A) :=
      .ax (Or.inr ⟨A, hAF, rfl⟩) (hdegc.trans (hScard.trans hwD))
    rw [hsplit]
    refine pcDerivable_mono (pcDerivable_mul_left hax (∏ v ∈ Sᶜ, fac a v)) ?_ subset_rfl
    refine max_le le_rfl ?_
    have h1 := totalDegree_prod_fac_le a Sᶜ
    have h2 : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    omega
  set p : MvPolynomial V (ZMod 2) := ∑ a : V → Bool, ∏ v, fac a v with hp
  have hpder : PCDerivable (cnfSystem F) D p := pcDerivable_sum _ _ fun a _ => hind a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hvan : ∀ x : V → ZMod 2, eval x (1 + p) = 0 := by
    intro x
    have hx : eval x p = 1 := by
      rw [hp, map_sum]
      simp only [map_prod, eval_fac, Finset.prod_boole]
      rw [Finset.sum_eq_single (fun v => decide (x v = 1))]
      · simp
      · intro b _ hb
        split_ifs with h
        · exfalso
          apply hb
          funext v
          have := h v (Finset.mem_univ v)
          cases hbv : b v <;> simp_all
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [map_add, map_one, hx, h11]
  have hdeg : (1 + p).totalDegree ≤ D := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]
      exact Nat.zero_le _
    · rw [hp]
      refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_prod_fac_le a Finset.univ).trans ?_
      rwa [Finset.card_univ]
  have h1 := BoolVanish.vanish_derivable V (cnfSystem F) D (1 + p)
    (fun v => Or.inl ⟨v, rfl⟩) hdeg hvan
  have h2 := PCDerivable.add h1 hpder
  have e : 1 + p + p = 1 := by
    rw [add_assoc, ← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  rw [e] at h2
  exact h2

end Completeness

section Binomial

theorem numMono_succ (n k : ℕ) : numMono n (k + 1) = numMono n k + n.choose (k + 1) := by
  unfold numMono
  rw [Finset.sum_range_succ]

theorem choose_le_numMono (n k : ℕ) : n.choose k ≤ numMono n k := by
  unfold numMono
  exact Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
    (Finset.self_mem_range_succ k)

theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : n.choose 0 ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos k))
  rw [Nat.choose_zero_right] at h
  exact h

/-- The counting core of the binomial estimate, over the naturals. -/
theorem numMono_ratio (n k : ℕ) (hk : k ≤ n) :
    (k + 1) * numMono n (k + 1) ≤ (n + 1) * numMono n k := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 := choose_le_numMono n k
  have h3 : n.choose k * (n - k) ≤ numMono n k * (n - k) := Nat.mul_le_mul_right _ h2
  have h4 : numMono n k * (k + 1) + numMono n k * (n - k) = numMono n k * (n + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [numMono_succ]
  calc (k + 1) * (numMono n k + n.choose (k + 1))
      = numMono n k * (k + 1) + n.choose (k + 1) * (k + 1) := by ring
    _ ≤ numMono n k * (k + 1) + numMono n k * (n - k) := by rw [h1]; exact Nat.add_le_add_left h3 _
    _ = (n + 1) * numMono n k := by rw [h4]; ring

theorem eta_le_one (n K : ℕ) (hK : 1 ≤ K) : eta n K ≤ 1 := by
  unfold eta
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hpos : (0 : ℝ) < numMono n (k + 1) := by exact_mod_cast numMono_pos n (k + 1)
  have hle : (numMono n k : ℝ) ≤ numMono n (k + 1) := by
    exact_mod_cast (numMono_succ n k) ▸ Nat.le_add_right _ _
  rw [Nat.add_sub_cancel, div_le_one (by positivity)]
  linarith

/-- The binomial estimate: `η ≥ K / (2 (n + 1))` for `1 ≤ K ≤ n + 1`. -/
theorem eta_ge : ∀ n K : ℕ, 1 ≤ K → K ≤ n + 1 → (K : ℝ) / (2 * (n + 1)) ≤ eta n K := by
  intro n K hK hKn
  unfold eta
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hpos : (0 : ℝ) < numMono n (k + 1) := by exact_mod_cast numMono_pos n (k + 1)
  have hnat : (((k + 1 : ℕ) : ℝ)) * numMono n (k + 1) ≤ ((n : ℝ) + 1) * numMono n k := by
    exact_mod_cast numMono_ratio n k (by omega)
  have hn : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  rw [Nat.add_sub_cancel, div_le_div_iff₀ hn (by positivity)]
  nlinarith

end Binomial

section Final

/-- The final theorem from the assembly inequality, in the stronger form: width up to
`D / 2`, constant `256`. -/
theorem final_of_assembly_256 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D : ℕ),
      (∀ C ∈ F, C.card ≤ w) → 2 * w ≤ D → 32 ≤ D → ¬ PCRefutable (cnfSystem F) D →
      IsLinRefutation F π →
      (∀ K t : ℕ, 1 ≤ K → K + max (2 * t + 2) (t + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - eta (Fintype.card V) K) ^ t) →
      Real.exp ((D : ℝ) ^ 2 / (256 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ) := by
  intro V _ _ F π w D hw hwD hD hnr href hasm
  have hunsat : ¬ Satisfiable F := lin_refutation_unsat href
  set n := Fintype.card V with hn
  have hDn : D < n := by
    by_contra hcon
    exact hnr (complete_deg V F w D hw hunsat (by omega) (by omega))
  set K := D / 4 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hbud : K + max (2 * K + 2) (K + w) ≤ D := by
    rcases max_cases (2 * K + 2) (K + w) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  have h := hasm K K hK1 hbud
  set x := eta n K with hx
  have hx1 : x ≤ 1 := eta_le_one n K hK1
  have hxge : (K : ℝ) / (2 * (n + 1)) ≤ x := eta_ge n K hK1 (by omega)
  have hpow : (1 - x) ^ K ≤ Real.exp (-((K : ℝ) * x)) := by
    have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have h2 : (1 - x) ^ K ≤ Real.exp (-x) ^ K := pow_le_pow_left₀ (by linarith) h1 K
    rw [← Real.exp_nat_mul] at h2
    rwa [mul_neg] at h2
  have hlen0 : (0 : ℝ) ≤ (π.length : ℝ) := Nat.cast_nonneg _
  have h3 : 1 ≤ (π.length : ℝ) * Real.exp (-((K : ℝ) * x)) :=
    h.trans (mul_le_mul_of_nonneg_left hpow hlen0)
  have h4 : Real.exp ((K : ℝ) * x) ≤ (π.length : ℝ) := by
    have hpos : 0 < Real.exp ((K : ℝ) * x) := Real.exp_pos _
    calc Real.exp ((K : ℝ) * x) = Real.exp ((K : ℝ) * x) * 1 := (mul_one _).symm
      _ ≤ Real.exp ((K : ℝ) * x) * ((π.length : ℝ) * Real.exp (-((K : ℝ) * x))) :=
          mul_le_mul_of_nonneg_left h3 hpos.le
      _ = (π.length : ℝ) * (Real.exp ((K : ℝ) * x) * Real.exp (-((K : ℝ) * x))) := by ring
      _ = (π.length : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  refine le_trans (Real.exp_le_exp.mpr ?_) h4
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hD8 : (D : ℝ) ≤ 8 * (K : ℝ) := by exact_mod_cast (by omega : D ≤ 8 * K)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hstep : (D : ℝ) ^ 2 / (256 * (n : ℝ)) ≤ (K : ℝ) * ((K : ℝ) / (2 * ((n : ℝ) + 1))) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (D : ℝ) ^ 2 ≤ 64 * ((K : ℝ) * (K : ℝ)) := by nlinarith
    have hKK : (0 : ℝ) ≤ (K : ℝ) * (K : ℝ) := mul_nonneg hKnn hKnn
    calc (D : ℝ) ^ 2 * (2 * ((n : ℝ) + 1)) ≤ 64 * ((K : ℝ) * (K : ℝ)) * (2 * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ 64 * ((K : ℝ) * (K : ℝ)) * (4 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (K : ℝ) * (K : ℝ) * (256 * (n : ℝ)) := by ring
  exact hstep.trans (mul_le_mul_of_nonneg_left hxge hKnn)

/-- The final theorem from the assembly inequality, as the recorded lemma needs it: width up
to `D / 32`, constant `1024`. -/
theorem final_of_assembly :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D : ℕ),
      (∀ C ∈ F, C.card ≤ w) → 32 * w ≤ D → 32 ≤ D → ¬ PCRefutable (cnfSystem F) D →
      IsLinRefutation F π →
      (∀ K t : ℕ, 1 ≤ K → K + max (2 * t + 2) (t + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - eta (Fintype.card V) K) ^ t) →
      Real.exp ((D : ℝ) ^ 2 / (1024 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ) := by
  intro V _ _ F π w D hw hwD hD hnr href hasm
  refine le_trans (Real.exp_le_exp.mpr ?_)
    (final_of_assembly_256 V F π w D hw (by omega) hD hnr href hasm)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_left hD0
    (by
      have hunsat : ¬ Satisfiable F := lin_refutation_unsat href
      have hpos : 0 < Fintype.card V := by
        by_contra hcon
        exact hnr (complete_deg V F w D hw hunsat (by omega) (by omega))
      have : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hpos
      positivity)
    (by nlinarith)

end Final

end PEqualNP.ProofComplexity.DegSizeArith
