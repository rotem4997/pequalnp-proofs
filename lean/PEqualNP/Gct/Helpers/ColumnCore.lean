import Mathlib
import PEqualNP.Gct.L171

/-!
# Column-product core for any number of rows (helpers for L-gct-175)

Generalizes `Helpers/ThreeRowRado.lean` from three rows to a finite row type `ρ`. The centred
hypothesis is kept in product form: every element of `V` vanishes outside the column support
`C`, and for every scalar `c` the sum over `C` of the column products of `c + x` is
`|C| c^|ρ|`. Strong induction on `|C|`, Rado's theorem (L-gct-171) for the transversal step,
and evaluation at `c = 1` for the contradiction. Conjecture until checked.
-/

namespace PEqualNP.Gct.Helpers.ColumnCore

open Module

variable {ρ κ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-- The hypothesis of the induction. -/
def Good (V : Submodule ℂ (ρ × κ → ℂ)) (C : Finset κ) : Prop :=
  ∀ x ∈ V, (∀ i, ∀ j ∉ C, x (i, j) = 0) ∧
    ∀ c : ℂ, ∑ j ∈ C, ∏ i, (c + x (i, j)) = (C.card : ℂ) * c ^ Fintype.card ρ

/-- The entry functional `x ↦ x (i, j)` on `V`. -/
def g (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) : Module.Dual ℂ V :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : ρ × κ => ℂ) (i, j)).comp V.subtype

@[simp] theorem g_apply (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) (x : V) :
    g V i j x = (x : ρ × κ → ℂ) (i, j) := rfl

/-- The entry functionals of the columns in `U`. -/
def S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) : Set (Module.Dual ℂ V) :=
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

theorem mem_coann_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) (x : V) :
    x ∈ (Submodule.span ℂ (S V U)).dualCoannihilator ↔
      ∀ i, ∀ j ∈ U, (x : ρ × κ → ℂ) (i, j) = 0 := by
  rw [mem_coann_span_iff]
  constructor
  · intro h i j hj
    exact h (g V i j) ⟨i, j, hj, rfl⟩
  · rintro h φ ⟨i, j, hj, rfl⟩
    simpa using h i j hj

theorem finrank_span_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) :
    finrank ℂ (Submodule.span ℂ (S V U)) =
      finrank ℂ V - finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (S V U))
  omega

/-- Removing a set `U` of columns on which `x` vanishes. -/
theorem sum_sdiff_of_zero (C U : Finset κ) (hUC : U ⊆ C) (x : ρ × κ → ℂ)
    (hx : ∀ i, ∀ j ∈ U, x (i, j) = 0) (c : ℂ)
    (h : ∑ j ∈ C, ∏ i, (c + x (i, j)) = (C.card : ℂ) * c ^ Fintype.card ρ) :
    ∑ j ∈ C \ U, ∏ i, (c + x (i, j)) = ((C \ U).card : ℂ) * c ^ Fintype.card ρ := by
  have hU : ∑ j ∈ U, ∏ i, (c + x (i, j)) = (U.card : ℂ) * c ^ Fintype.card ρ := by
    have : ∀ j ∈ U, ∏ i, (c + x (i, j)) = c ^ Fintype.card ρ := by
      intro j hj
      simp [hx _ j hj, Finset.prod_const]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hs := Finset.sum_sdiff (f := fun j => ∏ i, (c + x (i, j))) hUC
  rw [Finset.card_sdiff_of_subset hUC, Nat.cast_sub (Finset.card_le_card hUC)]
  rw [h, hU] at hs
  linear_combination hs

theorem bound : ∀ (n : ℕ) (C : Finset κ) (V : Submodule ℂ (ρ × κ → ℂ)),
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
        obtain ⟨h0, hc⟩ := hV y.1 y.2
        refine ⟨?_, fun c => sum_sdiff_of_zero C U hUC y.1 hy c (hc c)⟩
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
  obtain ⟨f, hfA, hfind⟩ := PEqualNP.Gct.L171 ℂ (Module.Dual ℂ V) ι A hcond
  have hσ : ∀ j : ι, ∃ i : ρ, g V i j.1 = f j := by
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
  have hyσ : ∀ j : ι, (y : ρ × κ → ℂ) (σ j, j.1) = -1 := by
    intro j
    have := congrFun hy j
    simp only [Ψ, LinearMap.pi_apply] at this
    rw [← hσ j] at this
    simpa [Ψ] using this
  -- Step 3: at c = 1 every column product in C vanishes
  obtain ⟨_, hy1⟩ := hV y.1 y.2
  have hzero : ∀ j ∈ C, ∏ i, ((1 : ℂ) + (y : ρ × κ → ℂ) (i, j)) = 0 := by
    intro j hj
    apply Finset.prod_eq_zero (Finset.mem_univ (σ ⟨j, hj⟩))
    rw [hyσ ⟨j, hj⟩]
    ring
  have hsum := hy1 1
  rw [Finset.sum_eq_zero hzero, one_pow, mul_one] at hsum
  have hc : (C.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hCne).ne'
  exact hc hsum.symm

/-- Rank and nullity on a subspace. -/
theorem finrank_map_add_finrank_inf_ker {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (p : Submodule ℂ E) :
    finrank ℂ (p.map f) + finrank ℂ (p ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, (Submodule.equivSubtypeMap p _).finrank_eq, Submodule.map_comap_subtype]

/-- The statement of L-gct-175. -/
theorem column_core : ∀ (p q : ℕ) (V : Submodule ℂ (Fin p × Fin q → ℂ))
    (lam : (Fin p × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V →
    lam (fun _ => (1 : ℂ)) = 1 → (∀ x ∈ V, (∑ j, ∏ i, x (i, j)) = (q : ℂ) * lam x ^ p) →
    Module.finrank ℂ V ≤ q := by
  intro p q V lam hJ hlam hN
  set W : Submodule ℂ (Fin p × Fin q → ℂ) := V ⊓ LinearMap.ker lam with hWdef
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      have : (fun _ => (1 : ℂ) : Fin p × Fin 0 → ℂ) = 0 := funext fun x => isEmptyElim x.2
      rw [this, map_zero] at hlam
      exact absurd hlam zero_ne_one
    · exact h0
  have hW : Good W (Finset.univ : Finset (Fin q)) := by
    intro w hw
    refine ⟨fun i j hj => absurd (Finset.mem_univ j) hj, fun c => ?_⟩
    obtain ⟨hwV, hwk⟩ := Submodule.mem_inf.mp hw
    have hx : w + c • (fun _ => (1 : ℂ)) ∈ V := V.add_mem hwV (V.smul_mem c hJ)
    have := hN _ hx
    rw [map_add, map_smul, LinearMap.mem_ker.mp hwk, hlam, smul_eq_mul, mul_one, zero_add] at this
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
    simp [add_comm]
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩
  have h1 := bound q Finset.univ W (by simp) hne hW
  change finrank ℂ ↥(V ⊓ LinearMap.ker lam) < q at h1
  have h2 := finrank_map_add_finrank_inf_ker lam V
  have h3 := Submodule.finrank_le (V.map lam)
  rw [Module.finrank_self] at h3
  omega

end PEqualNP.Gct.Helpers.ColumnCore
