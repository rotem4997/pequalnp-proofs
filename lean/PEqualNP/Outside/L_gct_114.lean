import Mathlib
import PEqualNP.Defs

/-!
# Row and column perturbations of the all-ones matrix

Turn off one family of perturbations. Expanding the permanent over subsets of the active
columns makes all nonempty injective sums vanish. Inclusion–exclusion then gives the
same vanishing for diagonal products. On the product of the perturbation spaces, the sum
of the column products of `c + x` is therefore `n * c ^ n`. The dimension bound for
such a space follows by induction on the number of columns, using Rado's transversal
theorem. Transposition gives the identical estimate on the other family.

The three local helper sections below adapt the project's `RadoLinear`, `ColumnCore`,
and `InvisibleBlock` arguments. Only the parts needed for this statement are included.
-/

namespace Gap114.Rado

open Submodule Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}

/-- The union of the sets `A j` over `j ∈ s`. -/
private def un (A : ι → Finset W) (s : Finset ι) : Set W := ⋃ j ∈ s, (A j : Set W)

private lemma un_finite (A : ι → Finset W) (s : Finset ι) : (un A s).Finite :=
  s.finite_toSet.biUnion fun j _ => (A j).finite_toSet

private lemma un_insert [DecidableEq ι] (A : ι → Finset W) (i : ι) (s : Finset ι) :
    un A (insert i s) = (A i : Set W) ∪ un A s := by
  simp only [un, Finset.set_biUnion_insert]

private lemma un_union [DecidableEq ι] (A : ι → Finset W) (s t : Finset ι) :
    un A (s ∪ t) = un A s ∪ un A t := by
  simp only [un, Finset.set_biUnion_union]

private lemma un_mono (A : ι → Finset W) {s t : Finset ι} (h : s ⊆ t) : un A s ⊆ un A t :=
  Set.biUnion_subset_biUnion_left (fun _ hx => h hx)

private lemma un_update_of_not_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∉ s) : un (Function.update A i B) s = un A s := by
  unfold un
  refine Set.iUnion₂_congr fun j hj => ?_
  rw [Function.update_of_ne (by rintro rfl; exact h hj)]

private lemma un_update_of_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∈ s) :
    un (Function.update A i B) s = (B : Set W) ∪ un A (s.erase i) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [un_insert, un_update_of_not_mem _ _ _ _ (Finset.notMem_erase i s),
    Function.update_self]

/-- The rank condition: every index set `s` has at most as many indices as the dimension of
the span of its union. -/
private def Good (K : Type*) [Field K] [Module K W] (A : ι → Finset W) : Prop :=
  ∀ s : Finset ι, s.card ≤ finrank K (span K (un A s))

private lemma finrank_span_mono {X Y : Set W} (hY : Y.Finite) (h : X ⊆ Y) :
    finrank K (span K X) ≤ finrank K (span K Y) := by
  haveI := FiniteDimensional.span_of_finite K hY
  exact Submodule.finrank_mono (span_mono h)

/-- If removing `c` from `A i` breaks the rank condition, there is an index set `t` avoiding
`i` with `dim span ((A i).erase c ∪ un A t) ≤ |t|`. -/
private lemma bad_erase [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    (c : W) (h : ¬ Good K (Function.update A i ((A i).erase c))) :
    ∃ t : Finset ι, i ∉ t ∧
      finrank K (span K ((((A i).erase c : Finset W) : Set W) ∪ un A t)) ≤ t.card := by
  simp only [Good, not_forall, not_le] at h
  obtain ⟨s, hs⟩ := h
  by_cases hi : i ∈ s
  · refine ⟨s.erase i, Finset.notMem_erase i s, ?_⟩
    rw [un_update_of_mem _ _ _ _ hi] at hs
    have := Finset.card_erase_add_one hi
    omega
  · rw [un_update_of_not_mem _ _ _ _ hi] at hs
    exact absurd (hA s) (not_le.mpr hs)

/-- The Rado / Mirsky reduction step: of two distinct elements of `A i`, one can be removed
keeping the rank condition. -/
private lemma erase_good [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    {a b : W} (ha : a ∈ A i) (hb : b ∈ A i) (hab : a ≠ b) :
    Good K (Function.update A i ((A i).erase a)) ∨
      Good K (Function.update A i ((A i).erase b)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨t1, hi1, h1⟩ := bad_erase A hA i a hcon.1
  obtain ⟨t2, hi2, h2⟩ := bad_erase A hA i b hcon.2
  set X : Set W := (((A i).erase a : Finset W) : Set W) ∪ un A t1 with hX
  set Y : Set W := (((A i).erase b : Finset W) : Set W) ∪ un A t2 with hY
  have hXf : X.Finite := ((A i).erase a).finite_toSet.union (un_finite A t1)
  have hYf : Y.Finite := ((A i).erase b).finite_toSet.union (un_finite A t2)
  haveI : FiniteDimensional K (span K X) := FiniteDimensional.span_of_finite K hXf
  haveI : FiniteDimensional K (span K Y) := FiniteDimensional.span_of_finite K hYf
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span K X) (span K Y)
  -- the union side
  have hU : un A (insert i (t1 ∪ t2)) ⊆ X ∪ Y := by
    rw [un_insert, un_union]
    intro x hx
    rcases hx with hx | hx | hx
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr (Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab, ha⟩)))
      · exact Or.inl (Or.inl (by simp [Finset.mem_erase, hxa, hx]))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  have hi12 : i ∉ t1 ∪ t2 := by simp [hi1, hi2]
  have hcardU := hA (insert i (t1 ∪ t2))
  rw [Finset.card_insert_of_notMem hi12] at hcardU
  have hsup : finrank K (span K (un A (insert i (t1 ∪ t2)))) ≤ finrank K ↥(span K X ⊔ span K Y) := by
    rw [← Submodule.span_union]
    exact finrank_span_mono (hXf.union hYf) hU
  -- the intersection side
  have hinf : finrank K (span K (un A (t1 ∩ t2))) ≤ finrank K ↥(span K X ⊓ span K Y) := by
    haveI : FiniteDimensional K ↥(span K X ⊓ span K Y) :=
      Submodule.finiteDimensional_inf_left _ _
    refine Submodule.finrank_mono (le_inf (span_mono ?_) (span_mono ?_))
    · exact (un_mono A Finset.inter_subset_left).trans Set.subset_union_right
    · exact (un_mono A Finset.inter_subset_right).trans Set.subset_union_right
  have hcardI := hA (t1 ∩ t2)
  have hc := Finset.card_union_add_card_inter t1 t2
  omega

/-- Rado's theorem, by induction on the total size of the sets. -/
private theorem rado_aux [Fintype ι] [DecidableEq ι] [DecidableEq W] :
    ∀ n : ℕ, ∀ A : ι → Finset W, ∑ j, (A j).card = n → Good K A →
      ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hA
  by_cases hbig : ∃ i, 1 < (A i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
    have key : ∃ c ∈ A i, Good K (Function.update A i ((A i).erase c)) := by
      rcases erase_good A hA i ha hb hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    obtain ⟨c, hc, hgood⟩ := key
    set A' := Function.update A i ((A i).erase c) with hA'
    have hlt : ∑ j, (A' j).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [hA', Function.update_self]
          exact Finset.card_erase_le
        · simp only [hA', Function.update_of_ne hj, le_refl]
      · simp only [hA', Function.update_self]
        exact Finset.card_erase_lt_of_mem hc
    obtain ⟨f, hf, hli⟩ := ih _ hlt A' rfl hgood
    refine ⟨f, fun j => ?_, hli⟩
    have := hf j
    by_cases hj : j = i
    · subst hj; simp only [hA', Function.update_self] at this
      exact Finset.mem_of_mem_erase this
    · simpa only [hA', Function.update_of_ne hj] using this
  · push Not at hbig
    have hone : ∀ j, ∃ v, A j = {v} := by
      intro j
      refine Finset.card_eq_one.mp (le_antisymm (hbig j) ?_)
      have h1 := hA {j}
      have hunj : un A {j} = (A j : Set W) := by simp [un]
      rw [hunj, Finset.card_singleton] at h1
      rw [Nat.one_le_iff_ne_zero] at h1 ⊢
      intro h0
      rw [Finset.card_eq_zero] at h0
      apply h1
      simp [h0]
    choose f hf using hone
    refine ⟨f, fun j => by simp [hf j], ?_⟩
    rw [linearIndependent_iff_card_le_finrank_span]
    have h := hA Finset.univ
    have hr : un A Finset.univ = Set.range f := by
      ext x; simp [un, hf, eq_comm]
    rw [hr, Finset.card_univ] at h
    exact h

end Gap114.Rado

namespace Gap114.Core

open Module

variable {ρ κ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-- The hypothesis of the induction. -/
private def Good (V : Submodule ℂ (ρ × κ → ℂ)) (C : Finset κ) : Prop :=
  ∀ x ∈ V, (∀ i, ∀ j ∉ C, x (i, j) = 0) ∧
    ∀ c : ℂ, ∑ j ∈ C, ∏ i, (c + x (i, j)) = (C.card : ℂ) * c ^ Fintype.card ρ

/-- The entry functional `x ↦ x (i, j)` on `V`. -/
private def g (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) : Module.Dual ℂ V :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : ρ × κ => ℂ) (i, j)).comp V.subtype

@[local simp] private theorem g_apply (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) (x : V) :
    g V i j x = (x : ρ × κ → ℂ) (i, j) := rfl

/-- The entry functionals of the columns in `U`. -/
private def S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) : Set (Module.Dual ℂ V) :=
  {φ | ∃ i, ∃ j ∈ U, φ = g V i j}

private theorem mem_coann_span_iff {V : Type} [AddCommGroup V] [Module ℂ V] (T : Set (Module.Dual ℂ V))
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

private theorem mem_coann_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) (x : V) :
    x ∈ (Submodule.span ℂ (S V U)).dualCoannihilator ↔
      ∀ i, ∀ j ∈ U, (x : ρ × κ → ℂ) (i, j) = 0 := by
  rw [mem_coann_span_iff]
  constructor
  · intro h i j hj
    exact h (g V i j) ⟨i, j, hj, rfl⟩
  · rintro h φ ⟨i, j, hj, rfl⟩
    simpa using h i j hj

private theorem finrank_span_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) :
    finrank ℂ (Submodule.span ℂ (S V U)) =
      finrank ℂ V - finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (S V U))
  omega

/-- Removing a set `U` of columns on which `x` vanishes. -/
private theorem sum_sdiff_of_zero (C U : Finset κ) (hUC : U ⊆ C) (x : ρ × κ → ℂ)
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

private theorem bound : ∀ (n : ℕ) (C : Finset κ) (V : Submodule ℂ (ρ × κ → ℂ)),
    C.card = n → C.Nonempty → Good V C → finrank ℂ V < n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C V hCn hCne hV
  by_contra hcon
  push Not at hcon
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
        Set.mem_range, S, Set.mem_ofPred_eq, hU', Finset.mem_map, Function.Embedding.coe_subtype,
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
  obtain ⟨f, hfA, hfind⟩ := Gap114.Rado.rado_aux _ A rfl hcond
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

end Gap114.Core

namespace Gap114.Moments

open Module Finset

variable {P m : ℕ}

/-! ### From injective sums to diagonal products -/

/-- The injective sum of a family of vectors. -/
private noncomputable def injSum {α : Type*} [Fintype α] [DecidableEq α] (u : α → Fin P → ℂ) : ℂ :=
  ∑ f : α ↪ Fin P, ∏ a, u a (f a)

/-- The diagonal sum of a family over a set of indices. -/
private def diagSum {α : Type*} (B : Finset α) (u : α → Fin P → ℂ) : ℂ :=
  ∑ i, ∏ a ∈ B, u a i

/-- The Moebius statement for an index type. -/
private def Moeb (P : ℕ) (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  Nonempty α → ∃ c : ℂ, c ≠ 0 ∧ ∀ u : α → Fin P → ℂ,
    (∀ B : Finset α, B.Nonempty → B ≠ univ → diagSum B u = 0) → injSum u = c * diagSum univ u

private theorem moeb_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (h : Moeb P α) : Moeb P β := by
  intro hβ
  obtain ⟨c, hc, hu⟩ := h (hβ.map e.symm)
  refine ⟨c, hc, fun u hB => ?_⟩
  have hI : injSum (fun a => u (e a)) = injSum u := by
    unfold injSum
    refine Fintype.sum_equiv (Equiv.embeddingCongr e (Equiv.refl _)) _ _ fun g => ?_
    refine Fintype.prod_equiv e _ _ fun a => ?_
    simp [Equiv.embeddingCongr_apply]
  have hD : ∀ B : Finset α, diagSum B (fun a => u (e a)) = diagSum (B.map e.toEmbedding) u := by
    intro B
    unfold diagSum
    simp [Finset.prod_map]
  have := hu (fun a => u (e a)) (fun B hBn hBu => by
    rw [hD]
    refine hB _ (hBn.map) fun hcon => hBu ?_
    rw [← Finset.map_univ_equiv e] at hcon
    exact Finset.map_injective _ hcon)
  rw [hI, hD, Finset.map_univ_equiv] at this
  exact this

private theorem exists_not_mem {α : Type*} [Fintype α] {B : Finset α} (h : B ≠ univ) : ∃ b, b ∉ B := by
  by_contra hc
  push Not at hc
  exact h (eq_univ_iff_forall.2 hc)

/-- The sum over the complement of the range of an embedding. -/
private theorem sum_compl_range {α : Type*} [Fintype α] (g : α ↪ Fin P) (φ : Fin P → ℂ)
    [Fintype ↥(Set.range g)ᶜ] :
    ∑ i : ↥(Set.range g)ᶜ, φ i = ∑ i, φ i - ∑ a, φ (g a) := by
  classical
  have h1 := Finset.sum_compl_add_sum (univ.map g) φ
  rw [Finset.sum_map] at h1
  have h2 : ∑ i ∈ (univ.map g)ᶜ, φ i = ∑ i : ↥(Set.range g)ᶜ, φ i :=
    Finset.sum_subtype _ (fun x => by simp) φ
  rw [← h2, eq_sub_iff_add_eq]
  exact h1

/-- The merged family: the factor of index `z` multiplied by the vector of `none`. -/
private def merge {α : Type*} [DecidableEq α] (u : Option α → Fin P → ℂ) (z : α) : α → Fin P → ℂ :=
  fun a i => u (some a) i * if a = z then u none i else 1

private theorem prod_merge {α : Type*} [DecidableEq α] (u : Option α → Fin P → ℂ) (z : α)
    (B : Finset α) (i : Fin P) :
    ∏ a ∈ B, merge u z a i = (∏ a ∈ B, u (some a) i) * if z ∈ B then u none i else 1 := by
  unfold merge
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']

/-- The recursion of the injective sum through `Option`. -/
private theorem injSum_option {α : Type*} [Fintype α] [DecidableEq α] (u : Option α → Fin P → ℂ) :
    injSum u = diagSum {none} u * injSum (fun a => u (some a))
      - ∑ z, injSum (merge u z) := by
  classical
  unfold injSum diagSum
  rw [Fintype.sum_equiv (Function.Embedding.optionEmbeddingEquiv α (Fin P)) _
    (fun p => u none p.2 * ∏ a, u (some a) (p.1 a)) (fun f => by
      rw [Fintype.prod_option]; rfl)]
  rw [Fintype.sum_sigma]
  simp only [Finset.prod_singleton]
  have hz : ∀ z : α, ∑ g : α ↪ Fin P, ∏ a, merge u z a (g a)
      = ∑ g : α ↪ Fin P, (∏ a, u (some a) (g a)) * u none (g z) := by
    intro z
    refine Fintype.sum_congr _ _ fun g => ?_
    unfold merge
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ z (fun a => u none (g a))]
    simp
  simp only [hz]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Fintype.sum_congr _ _ fun g => ?_
  rw [← Finset.sum_mul, sum_compl_range g (u none), sub_mul, ← Finset.mul_sum]
  ring

private theorem moeb_option {α : Type*} [Fintype α] [DecidableEq α] (h : Moeb P α) :
    Moeb P (Option α) := by
  intro _
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨1, one_ne_zero, fun u _ => ?_⟩
    rw [injSum_option]
    have h1 : injSum (P := P) (fun a : α => u (some a)) = 1 := by
      unfold injSum
      rw [Fintype.sum_eq_single (Function.Embedding.ofIsEmpty) (fun g hg =>
        absurd (Function.Embedding.ext fun a => isEmptyElim a) hg)]
      simp
    have h2 : ({none} : Finset (Option α)) = univ := by
      ext o; cases o with
      | none => exact ⟨fun _ => mem_univ _, fun _ => mem_singleton_self _⟩
      | some a => exact isEmptyElim a
    simp [h1, h2]
  · obtain ⟨c, hc, hu⟩ := h hα
    obtain ⟨a0⟩ := hα
    refine ⟨-(Fintype.card α : ℂ) * c, ?_, fun u hB => ?_⟩
    · have : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨a0⟩).ne'
      exact mul_ne_zero (neg_ne_zero.2 this) hc
    rw [injSum_option]
    have h0 : diagSum {none} u = 0 :=
      hB {none} (singleton_nonempty _) fun hcon => by
        have : some a0 ∈ ({none} : Finset (Option α)) := hcon ▸ mem_univ _
        simp at this
    have hfull : ∀ z, diagSum univ (merge u z) = diagSum univ u := by
      intro z
      unfold diagSum
      refine Fintype.sum_congr _ _ fun i => ?_
      rw [prod_merge, Fintype.prod_option, ite_eq_left (mem_univ z), mul_comm]
    have hm : ∀ z, injSum (merge u z) = c * diagSum univ u := by
      intro z
      rw [← hfull z]
      refine hu _ fun B hBn hBu => ?_
      obtain ⟨b, hb⟩ := exists_not_mem hBu
      by_cases hzB : z ∈ B
      · have hnone : none ∉ B.map Function.Embedding.some := by simp
        have heq : diagSum B (merge u z) = diagSum (insert none (B.map Function.Embedding.some)) u := by
          unfold diagSum
          refine Fintype.sum_congr _ _ fun i => ?_
          rw [prod_merge, ite_eq_left hzB, Finset.prod_insert hnone, Finset.prod_map, mul_comm]
          rfl
        rw [heq]
        refine hB _ (insert_nonempty _ _) fun hcon => ?_
        have : some b ∈ insert none (B.map Function.Embedding.some) := hcon ▸ mem_univ _
        simp [hb] at this
      · have heq : diagSum B (merge u z) = diagSum (B.map Function.Embedding.some) u := by
          unfold diagSum
          refine Fintype.sum_congr _ _ fun i => ?_
          rw [prod_merge, ite_eq_right hzB, Finset.prod_map, mul_one]
          rfl
        rw [heq]
        refine hB _ hBn.map fun hcon => ?_
        have : (none : Option α) ∈ B.map Function.Embedding.some := hcon ▸ mem_univ _
        simp at this
    simp only [h0, zero_mul, zero_sub, hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

private theorem moeb_fin (n : ℕ) : Moeb P (Fin n) := by
  induction n with
  | zero => intro h; exact isEmptyElim (h.some)
  | succ n ih => exact moeb_equiv (finSuccEquiv n).symm (moeb_option ih)

private theorem moeb (α : Type*) [Fintype α] [DecidableEq α] : Moeb P α :=
  moeb_equiv (Fintype.equivFin α).symm (moeb_fin _)

/-- Injective sums vanishing for families from subspaces give vanishing diagonal sums. -/
private theorem diag_of_inj (V : Fin m → Submodule ℂ (Fin P → ℂ))
    (hinj : ∀ Y : Finset (Fin m), Y.Nonempty → ∀ s : Fin m → Fin P → ℂ, (∀ y ∈ Y, s y ∈ V y) →
      ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, s y (f y) = 0) :
    ∀ A : Finset (Fin m), A.Nonempty → ∀ s : Fin m → Fin P → ℂ, (∀ j ∈ A, s j ∈ V j) →
      ∑ i, ∏ j ∈ A, s j i = 0 := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hA s hs
    obtain ⟨c, hc, hu⟩ := moeb (P := P) (↥A) hA.coe_sort
    have key := hu (fun y => s y) fun B hBn hBu => by
      obtain ⟨b, hb⟩ := exists_not_mem hBu
      unfold diagSum
      have := ih (B.map (Function.Embedding.subtype _)) ?_ hBn.map s ?_
      · simpa [Finset.prod_map] using this
      · rw [Finset.ssubset_iff_of_subset]
        · exact ⟨b, b.2, by simpa using hb⟩
        · intro x hx
          obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
          exact y.2
      · intro j hj
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hj
        exact hs _ y.2
    have h0 : injSum (fun y : ↥A => s y) = 0 := hinj A hA s hs
    rw [h0] at key
    have := (mul_eq_zero.1 key.symm).resolve_left hc
    unfold diagSum at this
    have e : ∀ i, ∏ y : ↥A, s y i = ∏ j ∈ A, s j i := fun i => Finset.prod_coe_sort A (fun j => s j i)
    simp only [← e]
    exact this

end Gap114.Moments

namespace Gap114

open Finset

private def restrictPerm {n : ℕ} (A : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : A ↪ Fin n :=
  ⟨fun a => σ a, σ.injective.comp Subtype.val_injective⟩

/-- Every injection on `A` has the same number of extensions to a permutation. -/
private theorem cardRestrict {n : ℕ} (A : Finset (Fin n)) (f : A ↪ Fin n)
    [Fintype {σ : Equiv.Perm (Fin n) // restrictPerm A σ = f}] :
    Fintype.card {σ : Equiv.Perm (Fin n) // restrictPerm A σ = f} = (n - A.card).factorial := by
  classical
  let φ : A ≃ Set.range f := Equiv.ofInjective f f.injective
  let τ : Equiv.Perm (Fin n) := φ.extendSubtype
  have hτ (a : A) : τ a = f a := φ.extendSubtype_apply_of_mem a a.property
  have hres (σ : Equiv.Perm (Fin n)) : restrictPerm A σ = f ↔ ∀ a : A, σ a = f a :=
    ⟨fun h a => DFunLike.congr_fun h a, fun h => DFunLike.ext _ _ h⟩
  let E : {σ : Equiv.Perm (Fin n) // restrictPerm A σ = f} ≃
      {ρ : Equiv.Perm (Fin n) // ∀ x, ¬ (x ∉ A) → ρ x = x} :=
    { toFun := fun σ => ⟨τ⁻¹ * σ.1, by
        intro x hx
        rw [not_not] at hx
        rw [Equiv.Perm.mul_apply, (hres σ.1).1 σ.2 ⟨x, hx⟩, ← hτ ⟨x, hx⟩]
        simp⟩
      invFun := fun ρ => ⟨τ * ρ.1, by
        rw [hres]
        intro a
        rw [Equiv.Perm.mul_apply, ρ.2 a (not_not.mpr a.property), hτ]⟩
      left_inv := fun σ => Subtype.ext (by simp)
      right_inv := fun ρ => Subtype.ext (by simp) }
  rw [Fintype.card_congr E, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm _),
    Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- Vary just the columns in a subset. The constant permanent forces its nonempty
subset coefficients to vanish, and each injection contributes the same factorial weight. -/
private theorem injZero {n : ℕ} (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (hp : ∀ t : Fin n × Fin n → ℂ, (∀ j, (fun i => t (i,j)) ∈ V j) →
      MvPolynomial.eval (fun p => 1+t p) (PEqualNP.Gct.permPoly ℂ n) = (n.factorial : ℂ))
    (A : Finset (Fin n)) (hA : A.Nonempty) (s : Fin n → Fin n → ℂ)
    (hs : ∀ j ∈ A, s j ∈ V j) :
    ∑ f : ↥A ↪ Fin n, ∏ r : ↥A, s (r : Fin n) (f r) = 0 := by
  classical
  let W (B : Finset (Fin n)) : ℂ := ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ B, s j (σ j)
  have he : W ∅ = (n.factorial : ℂ) := by simp [W, Fintype.card_perm]
  have hex (B : Finset (Fin n)) (hB : B ⊆ A) : ∑ C ∈ B.powerset, W C = (n.factorial : ℂ) := by
    let t : Fin n × Fin n → ℂ := fun p => if p.2 ∈ B then s p.2 p.1 else 0
    have h := hp t (fun j => by
      by_cases hj : j ∈ B
      · simp only [t, hj, ↓reduceIte]
        exact hs j (hB hj)
      · simp only [t, hj, ↓reduceIte]
        exact (V j).zero_mem)
    have hprod (σ : Equiv.Perm (Fin n)) :
        ∏ j, (1 + t (σ j, j)) = ∑ C ∈ B.powerset, ∏ j ∈ C, s j (σ j) := by
      rw [← Finset.prod_one_add, ← Finset.prod_ite_mem_eq B]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ B <;> simp [t, hj]
    rw [show (∑ C ∈ B.powerset, W C) =
        ∑ σ : Equiv.Perm (Fin n), ∑ C ∈ B.powerset, ∏ j ∈ C, s j (σ j) from Finset.sum_comm]
    simp_rw [← hprod]
    simpa only [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_prod,
      Matrix.mvPolynomialX_apply, MvPolynomial.eval_X] using h
  have hz (B : Finset (Fin n)) : B ⊆ A → B.Nonempty → W B = 0 := by
    induction B using Finset.strongInductionOn with
    | _ B ih =>
      intro hB hn
      have hsum : ∑ C ∈ B.ssubsets, W C = W ∅ := by
        apply Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_ssubsets hn)
        intro C hC hne
        have hCB := Finset.mem_ssubsets.mp hC
        exact ih C hCB (hCB.le.trans hB) (Finset.nonempty_iff_ne_empty.mpr hne)
      have hall := Finset.add_sum_erase B.powerset W (a := B) (by simp)
      change W B + ∑ C ∈ B.ssubsets, W C = _ at hall
      rw [hsum, he, hex B hB] at hall
      exact add_right_cancel (hall.trans (zero_add _).symm)
  let F (f : A ↪ Fin n) : ℂ := ∏ r : A, s (r : Fin n) (f r)
  have hperm : W A = ∑ σ : Equiv.Perm (Fin n), F (restrictPerm A σ) :=
    Finset.sum_congr rfl fun σ _ => (Finset.prod_coe_sort A (fun j => s j (σ j))).symm
  have hfiber : ∑ σ : Equiv.Perm (Fin n), F (restrictPerm A σ) =
      ((n - A.card).factorial : ℂ) * ∑ f, F f := by
    rw [← Fintype.sum_fiberwise' (restrictPerm A) F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_const, Finset.card_univ, cardRestrict, nsmul_eq_mul]
  have h := hz A (Subset.rfl) hA
  rw [hperm, hfiber, mul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)

end Gap114

namespace Gap114

open Gap114.Core

/-- Expand the products of `c + x` and apply the dimension bound to the product space. -/
private theorem dimBound {n : ℕ} (hn : 0 < n) (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (hd : ∀ A : Finset (Fin n), A.Nonempty → ∀ s : Fin n → Fin n → ℂ,
      (∀ i ∈ A, s i ∈ V i) → ∑ j : Fin n, ∏ i ∈ A, s i j = 0) :
    (∑ i : Fin n, Module.finrank ℂ (V i)) < n := by
  classical
  let E : (∀ i, V i) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
    LinearMap.pi fun p => LinearMap.proj p.2 ∘ₗ (V p.1).subtype ∘ₗ LinearMap.proj p.1
  have hE : Function.Injective E := by
    intro a b h
    funext i
    apply Subtype.ext
    funext j
    exact congrFun h (i, j)
  have hg : Good (LinearMap.range E) Finset.univ := by
    rintro _ ⟨x, rfl⟩
    refine ⟨by simp, ?_⟩
    intro c
    let s : Fin n → Fin n → ℂ := fun i => (x i).val
    change ∑ j : Fin n, ∏ i : Fin n, (c + s i j) =
      ((Finset.univ : Finset (Fin n)).card : ℂ) * c ^ Fintype.card (Fin n)
    have expand (j : Fin n) : ∏ i : Fin n, (c + s i j) =
        ∑ A : Finset (Fin n), (∏ i ∈ A, s i j) * c ^ Aᶜ.card := by
      simpa only [add_comm, Finset.prod_const] using
        (Fintype.prod_add (fun i => s i j) (fun _ => c))
    simp_rw [expand]
    rw [Finset.sum_comm, Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp
    · intro A _ hA
      rw [← Finset.sum_mul, hd A (Finset.nonempty_iff_ne_empty.mpr hA) s (fun i _ => (x i).prop),
        zero_mul]
    · simp
  have h := bound n Finset.univ (LinearMap.range E) (by simp)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ hg
  rwa [LinearMap.finrank_range_of_inj hE, Module.finrank_pi_fintype] at h

end Gap114

namespace Gap114

/-- The one-sided estimate, applied below in both orientations. -/
private theorem colBound {n : ℕ} (hn : 0 < n) (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (h : ∀ t : Fin n × Fin n → ℂ, (∀ j, (fun i => t (i, j)) ∈ V j) →
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (n.factorial : ℂ)) :
    (∑ i, Module.finrank ℂ (V i)) < n :=
  dimBound hn V (Moments.diag_of_inj V (injZero V h))

private theorem evalPerm {n : ℕ} (z : Fin n × Fin n → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

end Gap114

theorem PEqualNP.Outside.L_gct_114 : ∀ (n : ℕ) (V S : Fin n → Submodule ℂ (Fin n → ℂ)), (∀ r c : Fin n × Fin n → ℂ, (∀ i : Fin n, (fun j : Fin n => r (i, j)) ∈ V i) → (∀ j : Fin n, (fun i : Fin n => c (i, j)) ∈ S j) → MvPolynomial.eval (fun p => 1 + (r p + c p)) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → ∑ i : Fin n, Module.finrank ℂ (V i) + ∑ j : Fin n, Module.finrank ℂ (S j) ≤ 2 * n - 2 := by
  intro n V S h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have col := Gap114.colBound hn S (fun t ht => by
    simpa using h 0 t (fun i => (V i).zero_mem) ht)
  have row := Gap114.colBound hn V (fun t ht => by
    have hr := h (fun p => t (p.2, p.1)) 0 ht (fun j => (S j).zero_mem)
    simp only [Pi.zero_apply, add_zero] at hr
    rw [Gap114.evalPerm] at hr ⊢
    exact (Matrix.permanent_transpose (Matrix.of fun i j => 1 + t (i, j))).symm.trans hr)
  omega
