import Mathlib
import PEqualNP.Gct.Helpers.ThreeRow

/-!
# Three-row level bound from Rado's theorem

`centred_of_rado` derives the statement of row L-gct-157 (`ThreeRow.StmtCentred`) from Rado's
theorem for linear independence (`RadoStmt`, the statement of row L-gct-171), taken as a
hypothesis. Conjecture until checked.

Encoding. Columns are a fixed finite type `κ`; a support `C : Finset κ` stands for the column
set, so passing to the complement of a column set `U` keeps the type and shrinks the support to
`C \ U`. The level space is replaced by its centred part `V` (the kernel of the functional),
and the condition `N(x + c J) = q c^3` by the vanishing of the three column-symmetric sums.
-/

namespace PEqualNP.Gct.Helpers.ThreeRowRado

open Module

/-- Rado's theorem for linear independence, as a hypothesis (statement of L-gct-171). -/
def RadoStmt : Prop :=
  ∀ (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Finset W), (∀ U : Finset ι, U.card ≤ Module.finrank K (Submodule.span K (⋃ j ∈ U, (A j : Set W)))) → ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- First elementary symmetric function of column `j`. -/
def e1 (x : Fin 3 × κ → ℂ) (j : κ) : ℂ := x (0, j) + x (1, j) + x (2, j)

/-- Second elementary symmetric function of column `j`. -/
def e2 (x : Fin 3 × κ → ℂ) (j : κ) : ℂ := x (0, j) * x (1, j) + x (0, j) * x (2, j) + x (1, j) * x (2, j)

/-- Third elementary symmetric function of column `j`. -/
def e3 (x : Fin 3 × κ → ℂ) (j : κ) : ℂ := x (0, j) * x (1, j) * x (2, j)

/-- The hypothesis of the induction: every element of `V` is supported on the columns of `C`
and has the three column-symmetric sums zero. -/
def Good (V : Submodule ℂ (Fin 3 × κ → ℂ)) (C : Finset κ) : Prop :=
  ∀ x ∈ V, (∀ i, ∀ j ∉ C, x (i, j) = 0) ∧ ∑ j, e1 x j = 0 ∧ ∑ j, e2 x j = 0 ∧ ∑ j, e3 x j = 0

/-- The entry functional `x ↦ x (i, j)` on `V`. -/
def g (V : Submodule ℂ (Fin 3 × κ → ℂ)) (i : Fin 3) (j : κ) : Module.Dual ℂ V :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 × κ => ℂ) (i, j)).comp V.subtype

@[simp] theorem g_apply (V : Submodule ℂ (Fin 3 × κ → ℂ)) (i : Fin 3) (j : κ) (x : V) :
    g V i j x = (x : Fin 3 × κ → ℂ) (i, j) := rfl

/-- The entry functionals of the columns in `U`. -/
def S (V : Submodule ℂ (Fin 3 × κ → ℂ)) (U : Finset κ) : Set (Module.Dual ℂ V) :=
  {φ | ∃ i, ∃ j ∈ U, φ = g V i j}

theorem mem_coann_span_iff {V : Type} [AddCommGroup V] [Module ℂ V] (T : Set (Module.Dual ℂ V))
    (x : V) : x ∈ (Submodule.span ℂ T).dualCoannihilator ↔ ∀ φ ∈ T, φ x = 0 := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    exact h φ (Submodule.subset_span hφ)
  · intro h φ hφ
    have hle : Submodule.span ℂ T ≤ LinearMap.ker (Module.Dual.eval ℂ V x) := by
      rw [Submodule.span_le]
      intro ψ hψ
      simp [h ψ hψ]
    have := hle hφ
    simpa using this

theorem mem_coann_S (V : Submodule ℂ (Fin 3 × κ → ℂ)) (U : Finset κ) (x : V) :
    x ∈ (Submodule.span ℂ (S V U)).dualCoannihilator ↔
      ∀ i, ∀ j ∈ U, (x : Fin 3 × κ → ℂ) (i, j) = 0 := by
  rw [mem_coann_span_iff]
  constructor
  · intro h i j hj
    exact h (g V i j) ⟨i, j, hj, rfl⟩
  · rintro h φ ⟨i, j, hj, rfl⟩
    simpa using h i j hj

theorem finrank_span_S (V : Submodule ℂ (Fin 3 × κ → ℂ)) (U : Finset κ) :
    finrank ℂ (Submodule.span ℂ (S V U)) =
      finrank ℂ V - finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (S V U))
  omega

/-- Per column: `(a + y0)(a + y1)(a + y2) = a + e1 + e2 + e3` for `a` the indicator of `C`. -/
theorem col_expand (C : Finset κ) (y : Fin 3 × κ → ℂ) (hy : ∀ i, ∀ j ∉ C, y (i, j) = 0)
    (j : κ) :
    ((if j ∈ C then 1 else 0) + y (0, j)) * ((if j ∈ C then 1 else 0) + y (1, j)) *
        ((if j ∈ C then 1 else 0) + y (2, j)) =
      (if j ∈ C then 1 else 0) + e1 y j + e2 y j + e3 y j := by
  by_cases hj : j ∈ C
  · simp only [hj, if_true, e1, e2, e3]; ring
  · simp [hj, e1, e2, e3, hy _ j hj]

theorem bound (hR : RadoStmt) : ∀ (n : ℕ) (C : Finset κ) (V : Submodule ℂ (Fin 3 × κ → ℂ)),
    C.card = n → C.Nonempty → Good V C → finrank ℂ V < n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C V hCn hCne hV
  by_contra hcon
  push_neg at hcon
  -- Step 1: strict Hall
  have step1 : ∀ U : Finset κ, U ⊆ C → U.Nonempty →
      finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator ≤ C.card - U.card := by
    intro U hUC hUne
    set Kc := (Submodule.span ℂ (S V U)).dualCoannihilator with hKc
    by_cases hUeq : U = C
    · have : Kc = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [hKc, mem_coann_S] at hx
        rw [Submodule.mem_bot]
        apply Subtype.ext
        funext ⟨i, j⟩
        by_cases hj : j ∈ C
        · exact hx i j (hUeq ▸ hj)
        · exact (hV x.1 x.2).1 i j hj
      rw [this, finrank_bot]
      exact Nat.zero_le _
    · set K := Kc.map V.subtype with hK
      have hKr : finrank ℂ K = finrank ℂ Kc :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype V.injective_subtype Kc)).symm
      have hgood : Good K (C \ U) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        rw [hKc, mem_coann_S] at hy
        obtain ⟨h0, h1, h2, h3⟩ := hV y.1 y.2
        refine ⟨?_, h1, h2, h3⟩
        intro i j hj
        rw [Finset.mem_sdiff, not_and_or, not_not] at hj
        rcases hj with hj | hj
        · exact h0 i j hj
        · exact hy i j hj
      have hlt : (C \ U).card < n := by
        rw [← hCn]
        exact Finset.card_lt_card (Finset.sdiff_ssubset hUC hUne)
      have hne : (C \ U).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro h
        exact hUeq (Finset.Subset.antisymm hUC h)
      have := ih _ hlt (C \ U) K rfl hne hgood
      rw [Finset.card_sdiff_of_subset hUC] at this
      omega
  -- Step 2: Rado
  let ι := {j // j ∈ C}
  let A : ι → Finset (Module.Dual ℂ V) := fun j => Finset.univ.image (fun i => g V i j.1)
  have hcond : ∀ U : Finset ι, U.card ≤ finrank ℂ
      (Submodule.span ℂ (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V)))) := by
    intro U
    set U' : Finset κ := U.map (Function.Embedding.subtype _) with hU'
    have hset : (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V))) = S V U' := by
      ext φ
      simp only [Set.mem_iUnion, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range, S, Set.mem_setOf_eq, hU', Finset.mem_map, Function.Embedding.coe_subtype,
        A]
      constructor
      · rintro ⟨j, hj, i, rfl⟩
        exact ⟨i, j.1, ⟨j, hj, rfl⟩, rfl⟩
      · rintro ⟨i, _, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, i, rfl⟩
    rw [hset, finrank_span_S]
    have hcard : U'.card = U.card := Finset.card_map _
    have hsub : U' ⊆ C := by
      intro j hj
      rw [hU', Finset.mem_map] at hj
      obtain ⟨a, _, rfl⟩ := hj
      exact a.2
    have hUle : U'.card ≤ C.card := Finset.card_le_card hsub
    rcases U'.eq_empty_or_nonempty with he | hne
    · have : U.card = 0 := by rw [← hcard, he, Finset.card_empty]
      omega
    · have := step1 U' hsub hne
      omega
  obtain ⟨f, hfA, hfind⟩ := hR ℂ (Module.Dual ℂ V) ι A hcond
  have hσ : ∀ j : ι, ∃ i : Fin 3, g V i j.1 = f j := by
    intro j
    have := hfA j
    simpa [A] using this
  choose σ hσ using hσ
  -- the evaluation map at the chosen functionals is onto
  let Ψ : V →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun j => f j)
  have hker : LinearMap.ker Ψ = (Submodule.span ℂ (Set.range f)).dualCoannihilator := by
    ext x
    rw [mem_coann_span_iff, LinearMap.mem_ker]
    constructor
    · rintro h φ ⟨j, rfl⟩
      exact congrFun h j
    · intro h
      funext j
      exact h (f j) ⟨j, rfl⟩
  have hspan : finrank ℂ (Submodule.span ℂ (Set.range f)) = Fintype.card ι :=
    finrank_span_eq_card hfind
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (Set.range f))
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  have hfun : finrank ℂ (ι → ℂ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℂ
  have htop : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hker] at hrn
    omega
  obtain ⟨y, hy⟩ : (fun _ => (-1 : ℂ)) ∈ LinearMap.range Ψ := htop ▸ Submodule.mem_top
  have hyσ : ∀ j : ι, (y : Fin 3 × κ → ℂ) (σ j, j.1) = -1 := by
    intro j
    have := congrFun hy j
    simp only [Ψ, LinearMap.pi_apply] at this
    rw [← hσ j] at this
    simpa [Ψ] using this
  -- Step 3: the shifted point has a zero in every column
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hV y.1 y.2
  have hzero : ∀ j : κ,
      ((if j ∈ C then 1 else 0) + (y : Fin 3 × κ → ℂ) (0, j)) *
          ((if j ∈ C then 1 else 0) + (y : Fin 3 × κ → ℂ) (1, j)) *
          ((if j ∈ C then 1 else 0) + (y : Fin 3 × κ → ℂ) (2, j)) = 0 := by
    intro j
    by_cases hj : j ∈ C
    · have h := hyσ ⟨j, hj⟩
      simp only [hj, if_true]
      generalize σ ⟨j, hj⟩ = s at h
      fin_cases s
      · simp only [Fin.zero_eta] at h; rw [h]; ring
      · simp only [Fin.mk_one] at h; rw [h]; ring
      · simp only [Fin.reduceFinMk] at h; rw [h]; ring
    · simp [hj, hy0 _ j hj]
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => col_expand C y.1 hy0 j)
  simp only [hzero, Finset.sum_const_zero] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hy1, hy2, hy3,
    Finset.sum_boole] at hsum
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, add_zero] at hsum
  have hc : (C.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hCne).ne'
  exact hc hsum.symm

/-- Step 0: a row-centred level element has the three column-symmetric sums zero. -/
theorem step0 {q : ℕ} (t : Fin 3 × Fin q → ℂ)
    (hrow : ∀ i : Fin 3, ∑ j, t (i, j) = 0)
    (h2 : (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0)
    (h3 : (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) :
    ∑ j, e1 t j = 0 ∧ ∑ j, e2 t j = 0 ∧ ∑ j, e3 t j = 0 := by
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  refine ⟨?_, ?_, ?_⟩
  · simp only [e1, Finset.sum_add_distrib, r0, r1, r2, add_zero]
  · have hsplit : ∀ j l : Fin q, (if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) =
        (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l)) -
          (if j = l then (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l)) else 0) := by
      intro j l
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
    have hfull : (∑ j, ∑ l, (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul_sum, r0, r1, zero_mul, add_zero]
    rw [hfull, zero_sub, neg_eq_zero] at h2
    simpa [e2] using h2
  · have hsplit : ∀ j l m : Fin q, (if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) =
        t (0, j) * t (1, l) * t (2, m) - (if j = l then t (0, j) * t (1, l) * t (2, m) else 0)
          - (if j = m then t (0, j) * t (1, l) * t (2, m) else 0)
          - (if l = m then t (0, j) * t (1, l) * t (2, m) else 0)
          + 2 * (if j = l then (if l = m then t (0, j) * t (1, l) * t (2, m) else 0) else 0) := by
      intro j l m
      by_cases hjl : j = l <;> by_cases hjm : j = m <;> by_cases hlm : l = m <;>
        simp [hjl, hjm, hlm] <;> (try subst_vars) <;> (try simp_all) <;> ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h3
    have a1 : (∑ j, ∑ l, ∑ m, t (0, j) * t (1, l) * t (2, m)) = 0 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, r2, r1, r0, mul_zero, zero_mul,
        Finset.sum_const_zero]
    have a2 : (∑ j, ∑ l, ∑ m, if j = l then t (0, j) * t (1, l) * t (2, m) else 0) = 0 := by
      have : ∀ j l : Fin q, (∑ m, if j = l then t (0, j) * t (1, l) * t (2, m) else 0) =
          if j = l then t (0, j) * t (1, l) * ∑ m, t (2, m) else 0 := by
        intro j l; split_ifs <;> simp [Finset.mul_sum]
      simp only [this, r2, mul_zero, ite_self, Finset.sum_const_zero]
    have a3 : (∑ j, ∑ l, ∑ m, if j = m then t (0, j) * t (1, l) * t (2, m) else 0) = 0 := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp only [mul_right_comm _ _ (t (2, _)), ← Finset.mul_sum, r1, mul_zero,
        Finset.sum_const_zero]
    have a4 : (∑ j, ∑ l, ∑ m, if l = m then t (0, j) * t (1, l) * t (2, m) else 0) = 0 := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, r0, zero_mul]
    have a5 : (∑ j, ∑ l, ∑ m, if j = l then (if l = m then t (0, j) * t (1, l) * t (2, m) else 0) else 0) =
        ∑ j, e3 t j := by
      have : ∀ j l : Fin q, (∑ m, if j = l then (if l = m then t (0, j) * t (1, l) * t (2, m) else 0) else 0) =
          if j = l then t (0, j) * t (1, l) * t (2, l) else 0 := by
        intro j l; split_ifs <;> simp [Finset.sum_ite_eq]
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, e3]
    have a6 : (∑ j, ∑ l, ∑ m, 2 * if j = l then (if l = m then t (0, j) * t (1, l) * t (2, m) else 0) else 0) =
        2 * ∑ j, e3 t j := by
      rw [← a5]; simp only [Finset.mul_sum]
    rw [a1, a2, a3, a4, a6] at h3
    have : (2 : ℂ) * ∑ j, e3 t j = 0 := by linear_combination h3
    simpa using this

theorem centred_of_rado : RadoStmt → PEqualNP.Gct.Helpers.ThreeRow.StmtCentred := by
  intro hR q L hq hL
  have hgood : Good L (Finset.univ : Finset (Fin q)) := by
    intro x hx
    obtain ⟨hrow, h2, h3⟩ := hL x hx
    exact ⟨fun i j hj => absurd (Finset.mem_univ j) hj, step0 x hrow h2 h3⟩
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩
  have := bound hR q Finset.univ L (by simp) hne hgood
  omega

end PEqualNP.Gct.Helpers.ThreeRowRado
