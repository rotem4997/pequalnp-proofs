import Mathlib
import PEqualNP.Gct.Helpers.Rung.BlockPermA1
import PEqualNP.Gct.Helpers.Rung.BlockPermA2
import PEqualNP.Gct.Helpers.Rung.BlockPermA3

/-!
# Helper module (proofs only): the block matrix and its permanent

The matrix of Theorem C of the notes, with rows `Row` (the `a` top rows, `(N - 1) r` extra
rows, `b` rows per block) and columns `Col` (`a - r` padding columns, `b` columns per block,
`r` selector columns per block). The rows only depend on their group (`grp`: top rows are
alone, the extra rows form one group, the rows of a block form one group), so `pm_group`
turns the permanent into a coefficient of the product of the column forms, and the selector
columns of a block multiply to `q ^ r + (-1) ^ (r + 1) * U ^ r`.

`pm_block` is the identity: the permanent is a nonzero integer constant times the sum over
the blocks of the sums of `r × r` subpermanents.
-/

namespace PEqualNP.Gct.Rung.BPA

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

/-- Rows: top rows, extra rows, block rows. -/
abbrev Row (N a b r : ℕ) := (Fin a ⊕ Fin ((N - 1) * r)) ⊕ (Fin N × Fin b)

/-- Columns: padding columns, block columns, selector columns. -/
abbrev Col (N a b r : ℕ) := Fin (a - r) ⊕ ((Fin N × Fin b) ⊕ (Fin N × Fin r))

/-- Groups of rows: each top row, the extra rows, each block. -/
abbrev Grp (N a : ℕ) := (Fin a ⊕ Unit) ⊕ Fin N

/-- The group of a row. -/
def grp (N a b r : ℕ) : Row N a b r → Grp N a := Sum.map (Sum.map id (fun _ => ())) Prod.fst

/-- The entry of the matrix in a row of the given group. -/
def entry (N a b r : ℕ) (x : Fin N → Fin a → Fin b → R) (ζ : R) : Grp N a → Col N a b r → R
  | .inl (.inl _), .inl _ => 1
  | .inl (.inl i), .inr (.inl (h, j)) => x h i j
  | .inl (.inl _), .inr (.inr _) => 0
  | .inl (.inr _), .inl _ => 0
  | .inl (.inr _), .inr (.inl _) => 0
  | .inl (.inr _), .inr (.inr _) => 1
  | .inr _, .inl _ => 0
  | .inr h, .inr (.inl (h', _)) => if h = h' then 1 else 0
  | .inr h, .inr (.inr (h', l)) => if h = h' then ζ ^ (l : ℕ) else 0

/-- The linear form of a block column in the top row variables. -/
noncomputable def blkC {N a b : ℕ} (x : Fin N → Fin a → Fin b → R) (h : Fin N) (j : Fin b) :
    MvPolynomial (Fin a) R := ∑ i, C (x h i j) * X i

/-- Coefficient of a term of the expansion of the factor of a block. -/
noncomputable def facC {N a b : ℕ} (r : ℕ) (x : Fin N → Fin a → Fin b → R) (h : Fin N)
    (y : Finset (Fin b) × Bool) : MvPolynomial (Fin a ⊕ Unit) R :=
  (∏ j ∈ y.1, rename Sum.inl (blkC x h j)) *
    (if y.2 then C ((-1) ^ (r + 1)) else X (Sum.inr ()) ^ r)

/-- Exponent of the block variable in a term of the expansion of the factor of a block. -/
def facE (b r : ℕ) (y : Finset (Fin b) × Bool) : ℕ := (b - y.1.card) + (if y.2 then r else 0)

variable {N a b r : ℕ} (x : Fin N → Fin a → Fin b → R) (ζ : R)

theorem form_pad (p : Fin (a - r)) :
    (∑ γ : Grp N a, C (entry N a b r x ζ γ (.inl p)) * X γ : MvPolynomial (Grp N a) R) =
      rename Sum.inl (rename Sum.inl (∑ i : Fin a, X i)) := by
  simp [Fintype.sum_sum_type, entry]

theorem form_blk (h : Fin N) (j : Fin b) :
    (∑ γ : Grp N a, C (entry N a b r x ζ γ (.inr (.inl (h, j)))) * X γ :
      MvPolynomial (Grp N a) R) =
      rename Sum.inl (rename Sum.inl (blkC x h j)) + X (.inr h) := by
  have h3 : ∑ h' : Fin N, C (if h' = h then (1 : R) else 0) * X (Sum.inr h') =
      (X (Sum.inr h) : MvPolynomial (Grp N a) R) := by
    rw [Finset.sum_eq_single h] <;> simp +contextual
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [entry]
  rw [h3]
  simp [blkC]

theorem form_sel (h : Fin N) (l : Fin r) :
    (∑ γ : Grp N a, C (entry N a b r x ζ γ (.inr (.inr (h, l)))) * X γ :
      MvPolynomial (Grp N a) R) =
      C (ζ ^ (l : ℕ)) * X (.inr h) + X (.inl (.inr ())) := by
  have h3 : ∑ h' : Fin N, C (if h' = h then ζ ^ (l : ℕ) else 0) * X (Sum.inr h') =
      (C (ζ ^ (l : ℕ)) * X (Sum.inr h) : MvPolynomial (Grp N a) R) := by
    rw [Finset.sum_eq_single h] <;> simp +contextual
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [entry]
  rw [h3]
  simp [add_comm]

theorem prod_sel [IsDomain R] (hr : 1 ≤ r) (hζ : IsPrimitiveRoot ζ r) (h : Fin N) :
    (∏ l : Fin r, (C (ζ ^ (l : ℕ)) * X (.inr h) + X (.inl (.inr ()))) :
      MvPolynomial (Grp N a) R) =
      X (.inl (.inr ())) ^ r + C ((-1) ^ (r + 1)) * X (.inr h) ^ r := by
  have key := prod_add_root_mul hr (hζ.map_of_injective (C_injective (Grp N a) R))
    (X (.inr h)) (X (.inl (.inr ())))
  calc (∏ l : Fin r, (C (ζ ^ (l : ℕ)) * X (.inr h) + X (.inl (.inr ()))) :
        MvPolynomial (Grp N a) R)
      = ∏ l : Fin r, (X (.inl (.inr ())) + (C ζ) ^ (l : ℕ) * X (.inr h)) :=
        prod_congr rfl fun l _ => by rw [map_pow, add_comm]
    _ = ∏ l ∈ range r, (X (.inl (.inr ())) + (C ζ) ^ l * X (.inr h)) := by rw [Finset.prod_range]
    _ = _ := by
        rw [key]
        simp

/-- The product of the column forms, each block factor expanded. -/
theorem prod_forms [IsDomain R] (hr : 1 ≤ r) (hζ : IsPrimitiveRoot ζ r) :
    (∏ j : Col N a b r, ∑ γ : Grp N a, C (entry N a b r x ζ γ j) * X γ :
      MvPolynomial (Grp N a) R) =
      rename Sum.inl (rename Sum.inl (∑ i : Fin a, X i) ^ (a - r)) *
        ∏ h : Fin N, ∑ y ∈ (univ : Finset (Finset (Fin b) × Bool)),
          rename Sum.inl (facC r x h y) * X (Sum.inr h) ^ facE b r y := by
  classical
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_prod_type,
    Fintype.prod_prod_type]
  simp only [form_pad, form_blk, form_sel]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_mul_distrib,
    map_pow (rename Sum.inl) (rename Sum.inl (∑ i : Fin a, X i)) (a - r)]
  congr 1
  refine prod_congr rfl fun h _ => ?_
  rw [prod_sel ζ hr hζ, Finset.prod_add, Finset.powerset_univ, Finset.sum_mul,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun J _ => ?_
  rw [Fintype.sum_bool, Finset.prod_const, Finset.card_univ_sdiff, Fintype.card_fin]
  simp only [facC, facE, ite_true, Bool.false_eq_true, ite_false, map_mul, map_prod, map_pow,
    rename_X, rename_C, add_zero, pow_add]
  ring

theorem profile_grp :
    (∑ i : Row N a b r, Finsupp.single (grp N a b r i) 1) =
      Finsupp.sumElim (Finsupp.sumElim (∑ i : Fin a, Finsupp.single i 1)
        (Finsupp.single () ((N - 1) * r))) (Finsupp.equivFunOnFinite.symm fun _ => b) := by
  ext ((i | u) | h)
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finsupp.single_apply, grp]
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, grp]
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finsupp.single_apply, grp]

theorem sum_facC (h : Fin N) :
    ∑ y ∈ (univ : Finset (Finset (Fin b) × Bool)).filter (fun y => facE b r y = b),
      facC r x h y =
      X (Sum.inr ()) ^ r + rename Sum.inl (C ((-1) ^ (r + 1)) *
        ∑ J ∈ (univ : Finset (Finset (Fin b))).filter (fun J => J.card = r),
          ∏ j ∈ J, blkC x h j) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, facC, facE, ite_true, Bool.false_eq_true, ite_false, add_zero]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro J _ hJ
      have h1 : 0 < J.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ)
      have h2 := Finset.card_le_univ J
      simp only [Fintype.card_fin] at h2
      rw [ite_eq_right]
      omega
    · simp
  · rw [map_mul, map_sum, Finset.mul_sum, Finset.sum_filter]
    refine sum_congr rfl fun J _ => ?_
    have h2 := Finset.card_le_univ J
    simp only [Fintype.card_fin] at h2
    by_cases hJ : J.card = r
    · rw [ite_eq_left (by omega), ite_eq_left hJ, map_prod, mul_comm, rename_C]
    · rw [ite_eq_right (by omega), ite_eq_right hJ]

/-- Extraction of the coefficient in the variable of the extra rows: exactly one block
contributes its second term. -/
theorem coeff_one_block (hN : 1 ≤ N) (hr : 1 ≤ r) (A : MvPolynomial (Fin a) R)
    (g : Fin N → MvPolynomial (Fin a) R) (u : Fin a →₀ ℕ) :
    (rename Sum.inl A * ∏ h : Fin N, (X (Sum.inr ()) ^ r + rename Sum.inl (g h)) :
      MvPolynomial (Fin a ⊕ Unit) R).coeff
      (Finsupp.sumElim u (Finsupp.single () ((N - 1) * r))) = (A * ∑ h, g h).coeff u := by
  classical
  have hp : (∏ h : Fin N, (X (Sum.inr ()) ^ r + rename Sum.inl (g h)) :
      MvPolynomial (Fin a ⊕ Unit) R) =
      ∏ v : Unit, ∑ t ∈ (univ : Finset (Fin N)).powerset,
        rename Sum.inl (∏ h ∈ t, g h) * X (Sum.inr v) ^ (r * (univ \ t).card) := by
    conv_rhs => rw [Fintype.prod_unique]
    simp only [add_comm (X (Sum.inr ()) ^ r : MvPolynomial (Fin a ⊕ Unit) R)]
    rw [Finset.prod_add]
    refine sum_congr rfl fun t _ => ?_
    rw [map_prod, Finset.prod_const, ← pow_mul]
  rw [hp, coeff_sep, Fintype.prod_unique]
  have hfilter : ((univ : Finset (Fin N)).powerset.filter fun t =>
      r * (univ \ t).card = (Finsupp.single () ((N - 1) * r) : Unit →₀ ℕ) default) =
      Finset.powersetCard 1 univ := by
    ext t
    simp only [mem_filter, mem_powerset, subset_univ, true_and, mem_powersetCard]
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
    have h2 := Finset.card_le_univ t
    simp only [Fintype.card_fin] at h2
    have hs : (Finsupp.single () ((N - 1) * r) : Unit →₀ ℕ) default = (N - 1) * r := by simp
    rw [hs, mul_comm r, Nat.mul_left_inj (by omega)]
    omega
  rw [hfilter, Finset.powersetCard_one, Finset.sum_map]
  simp

/-- The coefficient of the product of the column forms. -/
theorem coeff_block [IsDomain R] (hN : 1 ≤ N) (hr : 1 ≤ r) (hζ : IsPrimitiveRoot ζ r) :
    (∏ j : Col N a b r, ∑ γ : Grp N a, C (entry N a b r x ζ γ j) * X γ :
      MvPolynomial (Grp N a) R).coeff (∑ i : Row N a b r, Finsupp.single (grp N a b r i) 1) =
      (-1) ^ (r + 1) * ∑ h : Fin N,
        ∑ J ∈ (univ : Finset (Finset (Fin b))).filter (fun J => J.card = r),
          ((∑ i : Fin a, X i) ^ (a - r) * ∏ j ∈ J, blkC x h j : MvPolynomial (Fin a) R).coeff
            (∑ i, Finsupp.single i 1) := by
  classical
  have hv : ∀ h : Fin N, (Finsupp.equivFunOnFinite.symm fun _ : Fin N => b) h = b :=
    fun _ => rfl
  rw [prod_forms x ζ hr hζ, profile_grp, coeff_sep]
  simp only [hv, sum_facC]
  rw [← map_pow (rename (Sum.inl : Fin a → Fin a ⊕ Unit))
    (∑ i : Fin a, (X i : MvPolynomial (Fin a) R)) (a - r), coeff_one_block hN hr]
  have he : ((∑ i : Fin a, X i) ^ (a - r) * ∑ h : Fin N, C ((-1) ^ (r + 1)) *
      ∑ J ∈ (univ : Finset (Finset (Fin b))).filter (fun J => J.card = r),
        ∏ j ∈ J, blkC x h j : MvPolynomial (Fin a) R) =
      C ((-1) ^ (r + 1)) * ∑ h : Fin N,
        ∑ J ∈ (univ : Finset (Finset (Fin b))).filter (fun J => J.card = r),
          (∑ i : Fin a, X i) ^ (a - r) * ∏ j ∈ J, blkC x h j := by
    simp only [Finset.mul_sum]
    refine sum_congr rfl fun h _ => sum_congr rfl fun J _ => ?_
    ring
  rw [he, coeff_C_mul, coeff_sum]
  simp only [coeff_sum]

/-- The permanent of the block matrix. -/
theorem pm_block [IsDomain R] (hN : 1 ≤ N) (hr : 1 ≤ r) (hra : r ≤ a)
    (hζ : IsPrimitiveRoot ζ r) :
    pm (fun (i : Row N a b r) (j : Col N a b r) => entry N a b r x ζ (grp N a b r i) j) =
      (stab (grp N a b r) : R) * ((-1) ^ (r + 1) * ((stab (pad a r) : R) *
        ∑ h : Fin N, ∑ J : {J : Finset (Fin b) // J.card = r},
          ∑ I : {I : Finset (Fin a) // I.card = r},
            Matrix.permanent (Matrix.of fun m n : Fin r =>
              x h (I.1.orderEmbOfFin I.2 m) (J.1.orderEmbOfFin J.2 n)))) := by
  classical
  rw [pm_group, coeff_block x ζ hN hr hζ]
  congr 2
  rw [Finset.mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [Finset.sum_subtype (p := fun J : Finset (Fin b) => J.card = r) _ (by simp),
    Finset.mul_sum]
  refine sum_congr rfl fun J _ => ?_
  have hprod : (∏ j ∈ J.1, blkC x h j : MvPolynomial (Fin a) R) =
      ∏ n : Fin r, ∑ i, C (x h i (J.1.orderEmbOfFin J.2 n)) * X i := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J.1 J.2, Finset.prod_map]
    rfl
  rw [hprod]
  exact coeff_pad a r hra fun i n => x h i (J.1.orderEmbOfFin J.2 n)

end PEqualNP.Gct.Rung.BPA
