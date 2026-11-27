import Mathlib
import PEqualNP.Defs

-- The nonzero columns are the five successive Fourier multiples of one row profile.
-- Cycling these columns forces each required homogeneous sum to vanish.
namespace PEqualNP.Outside.L_gct_206_aux

noncomputable def mat (z : ℂ) (u w : Fin 4 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  if p.2 = 0 then u p.1 else w p.1 * z ^ (p.2.val - 1)

noncomputable def center206 (u : Fin 3 → ℂ) : Fin 4 → ℂ := Fin.cons (-(∑ i, u i)) u

lemma center206_sum (u : Fin 3 → ℂ) : ∑ i, center206 u i = 0 := by
  rw [Fin.sum_univ_succ]
  simp [center206]

lemma center206_add (u v : Fin 3 → ℂ) : center206 (u + v) = center206 u + center206 v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [center206, Finset.sum_add_distrib, add_comm]
  · rfl

lemma center206_smul (c : ℂ) (u : Fin 3 → ℂ) : center206 (c • u) = c • center206 u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [center206, ← Finset.mul_sum]
  · rfl

noncomputable def matrixMap206 (z : ℂ) :
    ((Fin 3 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun q := mat z (center206 q.1) q.2
  map_add' q r := by
    funext p
    by_cases h : p.2 = 0 <;> simp [mat, h, center206_add, add_mul]
  map_smul' c q := by
    funext p
    by_cases h : p.2 = 0 <;> simp [mat, h, center206_smul, mul_assoc]

lemma matrixMap206_inj (z : ℂ) : Function.Injective (matrixMap206 z) := by
  intro q r h
  apply Prod.ext
  · funext i
    exact congrFun h (i.succ, 0)
  · funext i
    have e := congrFun h (i, 1)
    simpa [matrixMap206, mat] using e

theorem space206 (z : ℂ) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧
      ∀ t ∈ L, ∃ u w : Fin 4 → ℂ, (∑ i, u i) = 0 ∧ t = mat z u w := by
  refine ⟨LinearMap.range (matrixMap206 z), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (matrixMap206_inj z), Module.finrank_prod]
    simp
  · rintro t ⟨⟨u,w⟩, rfl⟩
    exact ⟨center206 u, w, center206_sum u, rfl⟩

open Finset

-- Enumeration of ordered subsets follows the argument in Gct.Helpers.RankOne.
abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

def emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun b => S.1.orderEmbOfFin S.2 (σ b), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

theorem range_emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) :
    Set.range (emb S σ) = (S.1 : Set (Fin n)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

theorem emb_bijective (n k : ℕ) :
    Function.Bijective (fun p : KSub n k × Equiv.Perm (Fin k) => emb p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    simp only at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_emb S σ, ← range_emb T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub n k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin n)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]

theorem sum_emb (n k : ℕ) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i, F i = ∑ S : KSub n k, ∑ σ : Equiv.Perm (Fin k), F (emb S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (emb_bijective n k) (fun p => F (emb p.1 p.2)) F
    (fun _ => rfl)).symm

theorem sum_perm_perm (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a)
      = (k.factorial : ℂ) * M.permanent := by
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin k),
      ∑ σ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a) = M.permanent := by
    intro τ
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, M (σ a) (τ a) = ∏ b, M ((σ * τ⁻¹) b) b := by
      intro σ
      exact Fintype.prod_equiv τ _ _ (fun a => by simp)
    simp_rw [h1]
    unfold Matrix.permanent
    exact Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ (fun _ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]


lemma gated206 {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (f : Subtype p → ℂ) :
    (∑ a, if h : p a then f ⟨a,h⟩ else 0) = ∑ s, f s := by
  classical
  have e := Fintype.sum_subtype_add_sum_subtype p (fun a => if h : p a then f ⟨a,h⟩ else 0)
  refine e.symm.trans ?_
  have pos (s : Subtype p) : (if h : p s.val then f ⟨s.val,h⟩ else 0) = f s := by simp [s.property]
  have neg (s : {a // ¬ p a}) : (if h : p s.val then f ⟨s.val,h⟩ else 0) = 0 := by simp [s.property]
  simp only [pos, neg, sum_const_zero, add_zero]

noncomputable def coeff206 (k : ℕ) (t : Fin 4 × Fin 6 → ℂ) : ℂ :=
  ∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
    if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
    else 0

lemma rectangular_inj206 (k : ℕ) (t : Fin 4 × Fin 6 → ℂ) :
    (k.factorial : ℂ) * coeff206 k t =
      ∑ i : Fin k ↪ Fin 4, ∑ j : Fin k ↪ Fin 6, ∏ a, t (i a, j a) := by
  let F := fun (R : KSub 4 k) (C : KSub 6 k) =>
    Matrix.permanent (Matrix.of fun a b => t (R.val.orderEmbOfFin R.property a,
      C.val.orderEmbOfFin C.property b))
  have sub : coeff206 k t = ∑ R : KSub 4 k, ∑ C : KSub 6 k, F R C := by
    unfold coeff206
    calc
      _ = ∑ R : Finset (Fin 4), if h : R.card = k then ∑ C : KSub 6 k, F ⟨R,h⟩ C else 0 := by
        apply sum_congr rfl
        intro R _
        by_cases hr : R.card = k
        · simp only [hr, true_and, ↓reduceDIte]
          exact gated206 _ (F ⟨R,hr⟩)
        · simp [hr]
      _ = _ := gated206 (fun R : Finset (Fin 4) => R.card = k) (fun R => ∑ C, F R C)
  rw [sub, sum_emb 4 k]
  simp_rw [sum_emb 6 k (fun j => ∏ a, t (_, j a))]
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro C _
  rw [← sum_perm_perm]
  rfl

noncomputable def shift206 : Equiv.Perm (Fin 6) := Equiv.Perm.decomposeFin.symm (0, finRotate 5)

lemma shift206_zero : shift206 0 = 0 := by simp [shift206]

lemma shift206_mat (z : ℂ) (hz : IsPrimitiveRoot z 5) (u w : Fin 4 → ℂ)
    (x : Fin 4) (y : Fin 6) :
    mat z u w (x, shift206 y) = (if y = 0 then 1 else z) * mat z u w (x,y) := by
  refine Fin.cases ?_ (fun i => ?_) y
  · simp [shift206_zero]
  · have rot (j : Fin 5) : z ^ ((finRotate 5 j).val) = z * z ^ j.val := by
      by_cases h : j = Fin.last 4
      · subst j
        simp only [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
        rw [← pow_succ', hz.pow_eq_one]
      · rw [coe_finRotate_of_ne_last h, pow_succ']
    simp [shift206, mat]
    have e := rot i
    rw [finRotate_apply] at e
    rw [e]
    ring

lemma phase206 {k : ℕ} (z : ℂ) (j : Fin k ↪ Fin 6) :
    (∏ a, if j a = 0 then 1 else z) = z^(if ∃ a, j a = 0 then k-1 else k) := by
  classical
  by_cases h : ∃ a, j a = 0
  · obtain ⟨i,hi⟩ := h
    simp only [show ∃ a, j a = 0 from ⟨i,hi⟩, ↓reduceIte]
    rw [← mul_prod_erase univ _ (mem_univ i)]
    simp only [hi, ↓reduceIte, one_mul]
    calc
      _ = ∏ _a ∈ univ.erase i, z := by
        apply prod_congr rfl
        intro a ha
        have hne : j a ≠ 0 := fun hz => (mem_erase.mp ha).1 (j.injective (hz.trans hi.symm))
        simp [hne]
      _ = _ := by simp
  · have hn (a : Fin k) := not_exists.mp h a
    simp [hn]

lemma orbit_zero206 {α : Type*} [Fintype α] (e : α ≃ α) (P : α → ℂ) (factor : ℂ)
    (hc : factor ≠ 1) (h : ∀ i, P (e i) = factor * P i) : ∑ i, P i = 0 := by
  have eq : (∑ i, P i) = factor * ∑ i, P i := by
    calc
      _ = ∑ i, P (e i) := (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = _ := by simp_rw [h, mul_sum]
  exact (mul_eq_zero.mp (show (factor-1) * ∑ i, P i = 0 by linear_combination -eq)).resolve_left
    (sub_ne_zero.mpr hc)

lemma higher206 {k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ 4)
    (z : ℂ) (hz : IsPrimitiveRoot z 5) (u w : Fin 4 → ℂ) (i : Fin k ↪ Fin 4) :
    ∑ j : Fin k ↪ Fin 6, ∏ a, mat z u w (i a,j a) = 0 := by
  classical
  let P := fun j : Fin k ↪ Fin 6 => ∏ a, mat z u w (i a,j a)
  let E := (Equiv.refl (Fin k)).embeddingCongr shift206
  let H := fun j : Fin k ↪ Fin 6 => ∃ a, j a = 0
  have orbitH (j : Fin k ↪ Fin 6) : H (E j) ↔ H j := by
    change (∃ a, shift206 (j a) = 0) ↔ ∃ a, j a = 0
    have h0 (a : Fin k) : shift206 (j a) = 0 ↔ j a = 0 :=
      ⟨fun h => shift206.injective (h.trans shift206_zero.symm), fun h => h ▸ shift206_zero⟩
    simp_rw [h0]
  have orbitP (j : Fin k ↪ Fin 6) : P (E j) = z^(if H j then k-1 else k) * P j := by
    change (∏ a, mat z u w (i a,shift206 (j a))) = _ * P j
    simp_rw [shift206_mat z hz u w, prod_mul_distrib, phase206]
    rfl
  have part1 := orbit_zero206 E (fun j => if H j then P j else 0) (z^(k-1))
    (hz.pow_ne_one_of_pos_of_lt (by omega) (by omega)) (fun j => by
      by_cases h : H j <;> simp [orbitH, orbitP, h])
  have part2 := orbit_zero206 E (fun j => if H j then 0 else P j) (z^k)
    (hz.pow_ne_one_of_pos_of_lt (by omega) (by omega)) (fun j => by
      by_cases h : H j <;> simp [orbitH, orbitP, h])
  change ∑ j, P j = 0
  calc
    _ = ∑ j, ((if H j then P j else 0) + (if H j then 0 else P j)) :=
      sum_congr rfl fun j _ => by by_cases h : H j <;> simp [h]
    _ = 0 := by rw [sum_add_distrib, part1, part2, add_zero]

lemma first206 (z : ℂ) (hz : IsPrimitiveRoot z 5) (u w : Fin 4 → ℂ) (hu : ∑ i, u i = 0) :
    (∑ i : Fin 1 ↪ Fin 4, ∑ j : Fin 1 ↪ Fin 6, ∏ a, mat z u w (i a,j a)) = 0 := by
  simp only [Fin.prod_univ_one]
  have geom : ∑ j : Fin 5, z^j.val = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hz.geom_sum_eq_zero (by decide)
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 6, mat z u w (i,j) := by
      apply Fintype.sum_equiv Equiv.embeddingUnique
      intro i
      exact Fintype.sum_equiv Equiv.embeddingUnique _ _ fun j => rfl
    _ = ∑ i, u i := by
      apply sum_congr rfl
      intro i _
      rw [Fin.sum_univ_succ]
      simp [mat, ← mul_sum, geom]
    _ = 0 := hu

lemma vanish206 (z : ℂ) (hz : IsPrimitiveRoot z 5) (u w : Fin 4 → ℂ) (hu : ∑ i, u i = 0)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) :
    coeff206 k (mat z u w) = 0 := by
  have h := rectangular_inj206 k (mat z u w)
  have zero : (∑ i : Fin k ↪ Fin 4, ∑ j : Fin k ↪ Fin 6, ∏ a, mat z u w (i a,j a)) = 0 := by
    by_cases one : k = 1
    · subst k
      exact first206 z hz u w hu
    · exact sum_eq_zero fun i _ => higher206 (by omega) hk' z hz u w i
  exact (mul_eq_zero.mp (h.trans zero)).resolve_left (by exact_mod_cast k.factorial_ne_zero)

end PEqualNP.Outside.L_gct_206_aux

theorem PEqualNP.Outside.L_gct_206 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ 5
  obtain ⟨L,hL,hmat⟩ := PEqualNP.Outside.L_gct_206_aux.space206 z
  refine ⟨L,hL,?_⟩
  intro t ht k hk hk4
  obtain ⟨u,w,hu,rfl⟩ := hmat t ht
  exact PEqualNP.Outside.L_gct_206_aux.vanish206 z hz u w hu k hk hk4
