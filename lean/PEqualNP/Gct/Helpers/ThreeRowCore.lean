import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! Helper module, proofs only. The three-row core: a linear space `V` of complex `3 × q`
matrices containing the all ones matrix `J`, with a functional `lam` satisfying `lam J = 1` and
`∑_j x_{0j} x_{1j} x_{2j} = q · lam(x)^3` on `V`, has dimension at most `q`.

Proof: pass to `W = V ⊓ ker lam` and induct on the number of columns. A proper nonempty column
set `U` gives, by restriction to the other columns, a smaller instance; so the part of `W`
vanishing on `U` is small (a strict surplus condition). The transversal theorem for independent
sets, in the abstract form `transversal` below (an antitone supermodular corank function), then
picks one entry per column such that `W` maps onto the chosen entries; a `w ∈ W` with every
chosen entry `-1` makes `w + J` have a zero in every column, so the column product sum of
`w + J` is `0`, while the hypothesis says it is `q`. -/

namespace PEqualNP.Gct.Helpers.ThreeRowCore

open Module

section Transversal

variable {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The transversal theorem in corank form. `z` is antitone and supermodular with `d ≤ z ∅`;
if every set `U` of indices satisfies `|U| + z(⋃_{j ∈ U} A j) ≤ d`, there is a choice
`σ j ∈ A j` with `|ι| + z(image σ) ≤ d`. -/
theorem transversal (z : Finset α → ℕ) (d : ℕ)
    (hanti : ∀ X Y : Finset α, X ⊆ Y → z Y ≤ z X)
    (hsup : ∀ X Y : Finset α, z X + z Y ≤ z (X ∪ Y) + z (X ∩ Y))
    (h0 : d ≤ z ∅) :
    ∀ (n : ℕ) (A : ι → Finset α), ∑ j, (A j).card = n →
      (∀ U : Finset ι, U.card + z (U.biUnion A) ≤ d) →
      ∃ σ : ι → α, (∀ j, σ j ∈ A j) ∧ Fintype.card ι + z (Finset.univ.image σ) ≤ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hall
  by_cases hbig : ∃ j, 1 < (A j).card
  · obtain ⟨j, hj⟩ := hbig
    obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp hj
    let A1 : ι → Finset α := fun i => if i = j then (A j).erase a1 else A i
    let A2 : ι → Finset α := fun i => if i = j then (A j).erase a2 else A i
    have hsub1 : ∀ i, A1 i ⊆ A i := by
      intro i; by_cases h : i = j
      · subst h; simp [A1, Finset.erase_subset]
      · simp [A1, h]
    have hsub2 : ∀ i, A2 i ⊆ A i := by
      intro i; by_cases h : i = j
      · subst h; simp [A2, Finset.erase_subset]
      · simp [A2, h]
    have hlt1 : ∑ i, (A1 i).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun i _ => Finset.card_le_card (hsub1 i))
        ⟨j, Finset.mem_univ _, ?_⟩
      simp only [A1, if_pos rfl]
      exact Finset.card_erase_lt_of_mem ha1
    have hlt2 : ∑ i, (A2 i).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun i _ => Finset.card_le_card (hsub2 i))
        ⟨j, Finset.mem_univ _, ?_⟩
      simp only [A2, if_pos rfl]
      exact Finset.card_erase_lt_of_mem ha2
    by_cases hall1 : ∀ U : Finset ι, U.card + z (U.biUnion A1) ≤ d
    · obtain ⟨σ, hσ, hc⟩ := ih _ hlt1 A1 rfl hall1
      exact ⟨σ, fun i => hsub1 i (hσ i), hc⟩
    by_cases hall2 : ∀ U : Finset ι, U.card + z (U.biUnion A2) ≤ d
    · obtain ⟨σ, hσ, hc⟩ := ih _ hlt2 A2 rfl hall2
      exact ⟨σ, fun i => hsub2 i (hσ i), hc⟩
    exfalso
    push Not at hall1 hall2
    obtain ⟨U1, hU1⟩ := hall1
    obtain ⟨U2, hU2⟩ := hall2
    have hj1 : j ∈ U1 := by
      by_contra hn1
      have he : U1.biUnion A1 = U1.biUnion A := Finset.biUnion_congr rfl (fun i hi => by
        have : i ≠ j := fun h => hn1 (h ▸ hi)
        simp [A1, this])
      have := hall U1
      rw [he] at hU1
      omega
    have hj2 : j ∈ U2 := by
      by_contra hn2
      have he : U2.biUnion A2 = U2.biUnion A := Finset.biUnion_congr rfl (fun i hi => by
        have : i ≠ j := fun h => hn2 (h ▸ hi)
        simp [A2, this])
      have := hall U2
      rw [he] at hU2
      omega
    have hU : (U1 ∪ U2).biUnion A ⊆ U1.biUnion A1 ∪ U2.biUnion A2 := by
      intro p hp
      simp only [Finset.mem_biUnion, Finset.mem_union] at hp
      obtain ⟨k, hk, hpk⟩ := hp
      rw [Finset.mem_union]
      by_cases hkj : k = j
      · subst hkj
        by_cases hpa : p = a1
        · right
          subst hpa
          exact Finset.mem_biUnion.mpr ⟨k, hj2, by simp [A2, Finset.mem_erase, hne, hpk]⟩
        · left
          exact Finset.mem_biUnion.mpr ⟨k, hj1, by simp [A1, Finset.mem_erase, hpa, hpk]⟩
      · rcases hk with hk | hk
        · left; exact Finset.mem_biUnion.mpr ⟨k, hk, by simp [A1, hkj, hpk]⟩
        · right; exact Finset.mem_biUnion.mpr ⟨k, hk, by simp [A2, hkj, hpk]⟩
    have hI : ((U1 ∩ U2).erase j).biUnion A ⊆ U1.biUnion A1 ∩ U2.biUnion A2 := by
      intro p hp
      simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_inter] at hp
      obtain ⟨k, ⟨hkj, hk1, hk2⟩, hpk⟩ := hp
      rw [Finset.mem_inter]
      exact ⟨Finset.mem_biUnion.mpr ⟨k, hk1, by simp [A1, hkj, hpk]⟩,
        Finset.mem_biUnion.mpr ⟨k, hk2, by simp [A2, hkj, hpk]⟩⟩
    have e1 := hall (U1 ∪ U2)
    have e2 := hall ((U1 ∩ U2).erase j)
    have a1' := hanti _ _ hU
    have a2' := hanti _ _ hI
    have s := hsup (U1.biUnion A1) (U2.biUnion A2)
    have c1 := Finset.card_union_add_card_inter U1 U2
    have c2 := Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hj1, hj2⟩)
    have c3 : 1 ≤ (U1 ∩ U2).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨hj1, hj2⟩⟩
    omega
  · push Not at hbig
    have hone : ∀ j, ∃ a, A j = {a} := by
      intro j
      apply Finset.card_eq_one.mp
      have hne : (A j).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        have := hall {j}
        rw [Finset.singleton_biUnion, he, Finset.card_singleton] at this
        omega
      have := hbig j
      have := hne.card_pos
      omega
    choose σ hσ using hone
    refine ⟨σ, fun j => by simp [hσ j], ?_⟩
    have hsub : Finset.univ.biUnion A ⊆ Finset.univ.image σ := by
      intro p hp
      simp only [Finset.mem_biUnion, hσ, Finset.mem_singleton] at hp
      obtain ⟨k, _, rfl⟩ := hp
      exact Finset.mem_image_of_mem σ (Finset.mem_univ k)
    have h1 := hall Finset.univ
    have h2 := hanti _ _ hsub
    rw [Finset.card_univ] at h1
    omega

end Transversal

section Linear

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- Rank and nullity on a subspace. -/
lemma finrank_map_add_finrank_inf_ker (f : E →ₗ[ℂ] F) (p : Submodule ℂ E) :
    finrank ℂ (p.map f) + finrank ℂ (p ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, (Submodule.equivSubtypeMap p _).finrank_eq, Submodule.map_comap_subtype]

end Linear

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The functions vanishing on a set of entries. -/
def Z (P : Finset (Fin 3 × ι)) : Submodule ℂ (Fin 3 × ι → ℂ) where
  carrier := {x | ∀ p ∈ P, x p = 0}
  add_mem' := by
    intro a b ha hb p hp
    simp [ha p hp, hb p hp]
  zero_mem' := by
    intro p _
    rfl
  smul_mem' := by
    intro c x hx p hp
    simp [hx p hp]

lemma mem_Z {P : Finset (Fin 3 × ι)} {x : Fin 3 × ι → ℂ} : x ∈ Z P ↔ ∀ p ∈ P, x p = 0 :=
  Iff.rfl

/-- The entries of a column. -/
def cols (j : ι) : Finset (Fin 3 × ι) := Finset.univ.filter fun p => p.2 = j

lemma mem_biUnion_cols {U : Finset ι} {p : Fin 3 × ι} : p ∈ U.biUnion cols ↔ p.2 ∈ U := by
  simp [cols]

/-- The product of a column. -/
def col (x : Fin 3 × ι → ℂ) (j : ι) : ℂ := x (0, j) * x (1, j) * x (2, j)

/-- The sum of the column products. -/
def N (x : Fin 3 × ι → ℂ) : ℂ := ∑ j, col x j

/-- The all ones matrix. -/
def J : Fin 3 × ι → ℂ := fun _ => 1

/-- The hypothesis of the core form. -/
def Hyp (W : Submodule ℂ (Fin 3 × ι → ℂ)) : Prop :=
  (J : Fin 3 × ι → ℂ) ∉ W ∧ ∀ w ∈ W, ∀ t : ℂ, N (w + t • J) = (Fintype.card ι : ℂ) * t ^ 3

/-- The corank function on entry sets. -/
noncomputable def zf (W : Submodule ℂ (Fin 3 × ι → ℂ)) (P : Finset (Fin 3 × ι)) : ℕ :=
  finrank ℂ (W ⊓ Z P : Submodule ℂ (Fin 3 × ι → ℂ))

lemma zf_anti (W : Submodule ℂ (Fin 3 × ι → ℂ)) (X Y : Finset (Fin 3 × ι)) (h : X ⊆ Y) :
    zf W Y ≤ zf W X :=
  Submodule.finrank_mono (inf_le_inf_left _ fun x hx p hp => hx p (h hp))

lemma zf_sup (W : Submodule ℂ (Fin 3 × ι → ℂ)) (X Y : Finset (Fin 3 × ι)) :
    zf W X + zf W Y ≤ zf W (X ∪ Y) + zf W (X ∩ Y) := by
  unfold zf
  rw [← Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ Z X) (W ⊓ Z Y), add_comm]
  apply add_le_add
  · apply Submodule.finrank_mono
    intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    obtain ⟨⟨hW, hX⟩, -, hY⟩ := hx
    refine ⟨hW, fun p hp => ?_⟩
    rcases Finset.mem_union.mp hp with h | h
    · exact hX p h
    · exact hY p h
  · apply Submodule.finrank_mono
    refine sup_le (inf_le_inf_left _ fun x hx p hp => hx p (Finset.mem_inter.mp hp).1)
      (inf_le_inf_left _ fun x hx p hp => hx p (Finset.mem_inter.mp hp).2)

lemma zf_empty (W : Submodule ℂ (Fin 3 × ι → ℂ)) : zf W ∅ = finrank ℂ W := by
  unfold zf
  rw [show W ⊓ Z ∅ = W from inf_eq_left.mpr fun x _ p hp => absurd hp (Finset.notMem_empty p)]

lemma zf_le (W : Submodule ℂ (Fin 3 × ι → ℂ)) (P : Finset (Fin 3 × ι)) :
    zf W P ≤ finrank ℂ W :=
  Submodule.finrank_mono inf_le_left

/-- Restriction to the columns outside `U`. -/
noncomputable def R (U : Finset ι) :
    (Fin 3 × ι → ℂ) →ₗ[ℂ] (Fin 3 × {j // j ∉ U} → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun p => (p.1, p.2.1)

lemma R_apply (U : Finset ι) (x : Fin 3 × ι → ℂ) (p : Fin 3 × {j // j ∉ U}) :
    R U x p = x (p.1, p.2.1) := rfl

lemma N_split (U : Finset ι) (x : Fin 3 × ι → ℂ) :
    N x = (∑ j : {j // j ∈ U}, col x j) + N (R U x) := by
  unfold N
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ U) (col x)]
  congr 1
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

lemma R_J (U : Finset ι) : R U (J : Fin 3 × ι → ℂ) = J := rfl

lemma card_out (U : Finset ι) : Fintype.card {j // j ∉ U} = Fintype.card ι - U.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- Strict surplus: from the induction hypothesis on fewer columns, the part of `W` vanishing on a
proper nonempty column set `U` is small. -/
lemma strict_hall
    (IH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ W' : Submodule ℂ (Fin 3 × κ → ℂ), Hyp W' → finrank ℂ W' + 1 ≤ Fintype.card κ)
    (W : Submodule ℂ (Fin 3 × ι → ℂ)) (hW : Hyp W) (U : Finset ι) (hU0 : U.Nonempty)
    (hU1 : U ≠ Finset.univ) :
    zf W (U.biUnion cols) + 1 ≤ Fintype.card ι - U.card := by
  set K0 : Submodule ℂ (Fin 3 × ι → ℂ) := W ⊓ Z (U.biUnion cols) with hK0
  have hvan : ∀ x ∈ K0, ∀ r : Fin 3, ∀ j ∈ U, x (r, j) = 0 := by
    intro x hx r j hj
    exact (Submodule.mem_inf.mp hx).2 (r, j) (mem_biUnion_cols.mpr hj)
  have hdisj : K0 ⊓ LinearMap.ker (R U) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    funext ⟨r, j⟩
    by_cases hj : j ∈ U
    · exact hvan x hx.1 r j hj
    · exact congrFun hx.2 (r, ⟨j, hj⟩)
  have hrank := finrank_map_add_finrank_inf_ker (R U) K0
  rw [hdisj, finrank_bot, add_zero] at hrank
  have hUc : U.card ≤ Fintype.card ι := Finset.card_le_univ U
  have hUpos : 0 < U.card := hU0.card_pos
  have hUlt : U.card < Fintype.card ι := by
    rcases lt_or_eq_of_le hUc with h | h
    · exact h
    · exact absurd ((Finset.card_eq_iff_eq_univ U).mp h) hU1
  -- the column products over `U` of `w + t J` for `w` in `K0`
  have hcolU : ∀ w ∈ K0, ∀ t : ℂ,
      (∑ j : {j // j ∈ U}, col (w + t • (J : Fin 3 × ι → ℂ)) j) = (U.card : ℂ) * t ^ 3 := by
    intro w hw t
    have : ∀ j : {j // j ∈ U}, col (w + t • (J : Fin 3 × ι → ℂ)) j = t ^ 3 := by
      intro j
      simp only [col, Pi.add_apply, Pi.smul_apply, J, smul_eq_mul, mul_one,
        hvan w hw _ j.1 j.2, zero_add]
      ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul]
  have hW' : Hyp (K0.map (R U)) := by
    constructor
    · intro hJ
      obtain ⟨w, hw, hRw⟩ := Submodule.mem_map.mp hJ
      have h1 := hW.2 w (Submodule.mem_inf.mp hw).1 (-1)
      rw [N_split U, hcolU w hw, map_add, map_smul, hRw, R_J] at h1
      have h0 : (J : Fin 3 × {j // j ∉ U} → ℂ) + (-1 : ℂ) • J = 0 := by
        funext p; simp [J]
      rw [h0] at h1
      have hN0 : N (0 : Fin 3 × {j // j ∉ U} → ℂ) = 0 := by simp [N, col]
      rw [hN0, add_zero] at h1
      have : (U.card : ℂ) = Fintype.card ι := by
        have h3 : ((-1 : ℂ)) ^ 3 = -1 := by norm_num
        rw [h3] at h1
        linear_combination -h1
      exact absurd (Nat.cast_injective this) (Nat.ne_of_lt hUlt)
    · intro w' hw' t
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hw'
      have h1 := hW.2 w (Submodule.mem_inf.mp hw).1 t
      rw [N_split U, hcolU w hw, map_add, map_smul, R_J] at h1
      rw [card_out, Nat.cast_sub hUc]
      linear_combination h1
  have hcard : Fintype.card {j // j ∉ U} < Fintype.card ι := by
    rw [card_out]; omega
  have := IH {j // j ∉ U} hcard _ hW'
  rw [hrank, card_out] at this
  exact this

/-- The core form, by strong induction on the number of columns. -/
theorem core : ∀ (n : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ = n →
    ∀ W : Submodule ℂ (Fin 3 × κ → ℂ), Hyp W → finrank ℂ W + 1 ≤ Fintype.card κ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hn W hW
  by_contra hcon
  push Not at hcon
  have hd : Fintype.card ι ≤ finrank ℂ W := by omega
  have IH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ W' : Submodule ℂ (Fin 3 × κ → ℂ), Hyp W' → finrank ℂ W' + 1 ≤ Fintype.card κ := by
    intro κ _ _ hκ W' hW'
    exact ih _ (hn ▸ hκ) κ rfl W' hW'
  have hall : ∀ U : Finset ι, U.card + zf W (U.biUnion cols) ≤ finrank ℂ W := by
    intro U
    rcases U.eq_empty_or_nonempty with h | h
    · subst h
      simp only [Finset.card_empty, Finset.biUnion_empty, zero_add]
      exact zf_le W _
    by_cases hu : U = Finset.univ
    · subst hu
      have : zf W (Finset.univ.biUnion cols) = 0 := by
        unfold zf
        have : (W ⊓ Z (Finset.univ.biUnion cols) : Submodule ℂ (Fin 3 × ι → ℂ)) = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [Submodule.mem_bot]
          funext p
          exact (Submodule.mem_inf.mp hx).2 p (mem_biUnion_cols.mpr (Finset.mem_univ _))
        rw [this, finrank_bot]
      rw [this, Finset.card_univ]
      omega
    · have := strict_hall IH W hW U h hu
      have := Finset.card_le_univ U
      omega
  obtain ⟨σ, hσ, hc⟩ := transversal (zf W) (finrank ℂ W) (zf_anti W) (zf_sup W)
    (zf_empty W).ge _ cols rfl hall
  have hσ2 : ∀ j, (σ j).2 = j := fun j => by simpa [cols] using hσ j
  let Φ : (Fin 3 × ι → ℂ) →ₗ[ℂ] (ι → ℂ) := LinearMap.funLeft ℂ ℂ σ
  have hker : finrank ℂ (W ⊓ LinearMap.ker Φ : Submodule ℂ (Fin 3 × ι → ℂ)) ≤
      zf W (Finset.univ.image σ) := by
    apply Submodule.finrank_mono
    apply inf_le_inf_left
    intro x hx p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact congrFun (LinearMap.mem_ker.mp hx) j
  have hrn := finrank_map_add_finrank_inf_ker Φ W
  have htop : W.map Φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (W.map Φ)
    rw [Module.finrank_fintype_fun_eq_card] at this ⊢
    omega
  have hmem : (fun _ => (-1 : ℂ)) ∈ W.map Φ := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, hΦ⟩ := Submodule.mem_map.mp hmem
  have hwσ : ∀ j, w (σ j) = -1 := fun j => congrFun hΦ j
  have h1 := hW.2 w hw 1
  have hN0 : N (w + (1 : ℂ) • J) = 0 := by
    unfold N
    refine Finset.sum_eq_zero fun j _ => ?_
    have hp : σ j = ((σ j).1, j) := Prod.ext rfl (hσ2 j)
    have hz : w ((σ j).1, j) = -1 := by rw [← hp]; exact hwσ j
    unfold col
    simp only [Pi.add_apply, Pi.smul_apply, J, smul_eq_mul, mul_one]
    generalize (σ j).1 = r at hz
    fin_cases r <;> simp at hz ⊢ <;> simp [hz]
  rw [hN0, one_pow, mul_one] at h1
  have hc0 : Fintype.card ι = 0 := by exact_mod_cast h1.symm
  have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc0
  apply hW.1
  have : (J : Fin 3 × ι → ℂ) = 0 := funext fun p => isEmptyElim p.2
  rw [this]
  exact W.zero_mem

end Core

/-- The three-row core. -/
theorem three_row_core : ∀ (q : ℕ) (V : Submodule ℂ (Fin 3 × Fin q → ℂ))
    (lam : (Fin 3 × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V → lam (fun _ => (1 : ℂ)) = 1 →
    (∀ x ∈ V, (∑ j, x (0, j) * x (1, j) * x (2, j)) = (q : ℂ) * lam x ^ 3) →
    Module.finrank ℂ V ≤ q := by
  intro q V lam hJ hlam hN
  set W : Submodule ℂ (Fin 3 × Fin q → ℂ) := V ⊓ LinearMap.ker lam with hWdef
  have hW : Hyp W := by
    constructor
    · intro h
      have := LinearMap.mem_ker.mp (Submodule.mem_inf.mp h).2
      rw [show (J : Fin 3 × Fin q → ℂ) = fun _ => (1 : ℂ) from rfl, hlam] at this
      exact one_ne_zero this
    · intro w hw t
      obtain ⟨hwV, hwk⟩ := Submodule.mem_inf.mp hw
      have hx : w + t • J ∈ V := V.add_mem hwV (V.smul_mem t hJ)
      have := hN _ hx
      rw [map_add, map_smul, LinearMap.mem_ker.mp hwk,
        show (J : Fin 3 × Fin q → ℂ) = fun _ => (1 : ℂ) from rfl, hlam] at this
      simpa [N, col, J, Fintype.card_fin] using this
  have h1 := core _ (Fin q) rfl W hW
  rw [Fintype.card_fin] at h1
  change finrank ℂ ↥(V ⊓ LinearMap.ker lam) + 1 ≤ q at h1
  have h2 := finrank_map_add_finrank_inf_ker lam V
  have h3 := Submodule.finrank_le (V.map lam)
  rw [Module.finrank_self] at h3
  omega

end PEqualNP.Gct.Helpers.ThreeRowCore
