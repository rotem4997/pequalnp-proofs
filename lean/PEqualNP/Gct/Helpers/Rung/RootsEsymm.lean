import Mathlib

/-!
# Elementary symmetric sums of the powers of a primitive root of unity

For a primitive `r`-th root of unity `z` in a commutative domain, the `t`-th elementary
symmetric sum of `z ^ 0, ..., z ^ (r - 1)` is `1` for `t = 0`, `(-1) ^ (r + 1)` for `t = r`
and `0` otherwise. This is Vieta's formula read off `X ^ r - 1 = ∏ l, (X - C (z ^ l))`.
-/

namespace PEqualNP.Gct.Rung

open Polynomial

/-- The `r`-th roots of unity are exactly the powers `z ^ l`, `l < r`, of a primitive root. -/
theorem nthRootsFinset_eq_image_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (r : ℕ) (hr : 1 ≤ r) (z : R) (hz : IsPrimitiveRoot z r) :
    nthRootsFinset r (1 : R) = (Finset.univ : Finset (Fin r)).image (fun l : Fin r => z ^ (l : ℕ)) := by
  have hinj : Function.Injective (fun l : Fin r => z ^ (l : ℕ)) := fun a b h =>
    Fin.ext (hz.pow_inj a.2 b.2 h)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_nthRootsFinset hr, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  · rw [hz.card_nthRootsFinset, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]

/-- Elementary symmetric sums of the powers of a primitive root of unity, in a commutative
domain. -/
theorem esymm_roots_of_unity' {R : Type*} [CommRing R] [IsDomain R]
    (r : ℕ) (hr : 1 ≤ r) (z : R) (hz : IsPrimitiveRoot z r) (t : ℕ) :
    (∑ s ∈ (Finset.univ : Finset (Fin r)).powersetCard t, ∏ l ∈ s, z ^ (l : ℕ)) =
      if t = 0 then 1 else if t = r then (-1) ^ (r + 1) else 0 := by
  classical
  by_cases htr : r < t
  · rw [Finset.powersetCard_eq_empty.2 (by simpa using htr), Finset.sum_empty,
      if_neg (by omega), if_neg (by omega)]
  have htr' : t ≤ r := by omega
  have hinj : Function.Injective (fun l : Fin r => z ^ (l : ℕ)) := fun a b h =>
    Fin.ext (hz.pow_inj a.2 b.2 h)
  set m : Multiset R := (Finset.univ : Finset (Fin r)).val.map (fun l : Fin r => z ^ (l : ℕ)) with hm
  have hcard : Multiset.card m = r := by simp [hm]
  have hprod : (X ^ r - 1 : R[X]) = (m.map fun a => X - C a).prod := by
    rw [X_pow_sub_one_eq_prod hr hz, nthRootsFinset_eq_image_pow r hr z hz,
      Finset.prod_image (fun a _ b _ h => hinj h), hm, Multiset.map_map]
    rfl
  have hco := Multiset.prod_X_sub_C_coeff m (k := r - t) (by omega)
  rw [← hprod, hcard, show r - (r - t) = t by omega, hm, Finset.esymm_map_val] at hco
  have hsum : (∑ s ∈ (Finset.univ : Finset (Fin r)).powersetCard t, ∏ l ∈ s, z ^ (l : ℕ)) =
      (-1) ^ t * (X ^ r - 1 : R[X]).coeff (r - t) := by
    rw [hco, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨t, rfl⟩, one_mul]
  rw [hsum, coeff_sub, coeff_X_pow, coeff_one]
  by_cases h0 : t = 0
  · subst h0
    have : r ≠ 0 := by omega
    simp [this]
  · by_cases h1 : t = r
    · subst h1
      have : ¬ (0 = t) := fun h => h0 h.symm
      simp [this, h0, pow_succ]
    · have h2 : r - t ≠ r := by omega
      have h3 : r - t ≠ 0 := by omega
      simp [h0, h1, h2, h3]

/-- Elementary symmetric sums of the powers of a primitive complex root of unity. -/
theorem esymm_roots_of_unity (r : ℕ) (hr : 1 ≤ r) (z : ℂ) (hz : IsPrimitiveRoot z r) (t : ℕ) :
    (∑ s ∈ (Finset.univ : Finset (Fin r)).powersetCard t, ∏ l ∈ s, z ^ (l : ℕ)) =
      if t = 0 then 1 else if t = r then (-1) ^ (r + 1) else 0 :=
  esymm_roots_of_unity' r hr z hz t

end PEqualNP.Gct.Rung
