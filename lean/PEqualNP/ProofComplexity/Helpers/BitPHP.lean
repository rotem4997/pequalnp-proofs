import PEqualNP.Defs.ProofComplexityBit
import Mathlib

/-!
# Helpers: the rank of Res(⊕) refutations of the bit pigeonhole principle

Every Res(⊕) refutation of the bit pigeonhole formula with `2 ^ l` holes has a line whose
set of linear forms has rank at least `2 ^ l / 4`. This is Theorem 5.5 of Efremenko, Garlik
and Itsykson, "Lower bounds for regular resolution over parities" (STOC 2024, ECCC
TR23-187).

The proof follows the plan of that paper (walk from the empty clause towards the axioms and
keep the negation of the current line "locally consistent"), with the closure of a set of
linear forms replaced by a lighter notion that needs no uniqueness statement:

* for a space `U` of linear forms and a set `T` of pigeons, `dimIn U T` is the dimension of
  the forms of `U` that mention only pigeons of `T`; it is supermodular in `T`;
* a set `S` of pigeons is `Good` for `U` when no larger set gains more dimension than
  pigeons. Good sets are closed under intersection, pass to subspaces, and a maximiser of
  `dimIn U T - |T|` is a good set of size at most the dimension of `U`;
* a line is locally consistent (`LC`) when some assignment falsifies it and is injective on
  some good set of its span of forms.

The matroid form of Hall's theorem used in the paper is replaced by a direct induction
(`exists_pivots`): for a good set `K` one can pick one bit in each pigeon outside `K` so that
every form of `U` that avoids the picked bits mentions only pigeons of `K`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-! ### Linear forms, falsifying assignments, and the two-element field -/

/-- The indicator vector of a linear form. -/
def ind {V : Type} [DecidableEq V] (f : Finset V) : V → ZMod 2 := fun v => if v ∈ f then 1 else 0

/-- The span of the linear forms of a linear clause. -/
def formSpan {V : Type} [DecidableEq V] (C : LinClause V) : Submodule (ZMod 2) (V → ZMod 2) :=
  Submodule.span (ZMod 2) ((fun q : LinEq V => ind q.1) '' (C : Set (LinEq V)))

theorem linRank_eq {V : Type} [DecidableEq V] (C : LinClause V) :
    linRank C = Module.finrank (ZMod 2) (formSpan C) := rfl

/-- A bit as an element of the two-element field. -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- A Boolean assignment as a vector. -/
def vec {V : Type} (a : V → Bool) : V → ZMod 2 := fun v => toZ (a v)

/-- The vector `x` falsifies every equation of the linear clause `C`. -/
def Fals {V : Type} [Fintype V] [DecidableEq V] (C : LinClause V) (x : V → ZMod 2) : Prop :=
  ∀ q ∈ C, ind q.1 ⬝ᵥ x ≠ toZ q.2

theorem ind_dot_vec {V : Type} [Fintype V] [DecidableEq V] (f : Finset V) (a : V → Bool) :
    ind f ⬝ᵥ vec a = ((f.filter (fun v => a v = true)).card : ZMod 2) := by
  have h : ∀ v, (if v ∈ f then (1 : ZMod 2) else 0) * (if a v = true then 1 else 0) =
      if v ∈ f then (if a v = true then 1 else 0) else 0 := by
    intro v
    split_ifs <;> simp
  simp only [dotProduct, ind, vec, toZ, h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.natCast_card_filter]

theorem linEqSat_iff {V : Type} [Fintype V] [DecidableEq V] (a : V → Bool) (q : LinEq V) :
    LinEqSat a q ↔ ind q.1 ⬝ᵥ vec a = toZ q.2 := by
  rw [ind_dot_vec]
  unfold LinEqSat toZ
  cases q.2 <;>
    simp [ZMod.natCast_eq_one_iff_odd, ZMod.natCast_eq_zero_iff_even, Nat.not_odd_iff_even]

theorem fals_vec {V : Type} [Fintype V] [DecidableEq V] (a : V → Bool) (C : LinClause V) :
    Fals C (vec a) ↔ ¬ LinClauseSat a C := by
  constructor
  · rintro h ⟨q, hq, hs⟩
    exact h q hq ((linEqSat_iff a q).1 hs)
  · intro h q hq hs
    exact h ⟨q, hq, (linEqSat_iff a q).2 hs⟩

theorem vec_surj {V : Type} (x : V → ZMod 2) : ∃ a : V → Bool, vec a = x := by
  have h : ∀ z : ZMod 2, toZ (decide (z = 1)) = z := by decide
  exact ⟨fun v => decide (x v = 1), funext fun v => h (x v)⟩

theorem fals_of_imp {V : Type} [Fintype V] [DecidableEq V] {C D : LinClause V}
    (h : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D) {x : V → ZMod 2}
    (hx : Fals D x) : Fals C x := by
  obtain ⟨a, rfl⟩ := vec_surj x
  exact (fals_vec a C).2 fun hC => (fals_vec a D).1 hx (h a hC)

theorem ind_mem_formSpan {V : Type} [DecidableEq V] {C : LinClause V} {q : LinEq V}
    (hq : q ∈ C) : ind q.1 ∈ formSpan C :=
  Submodule.subset_span ⟨q, Finset.mem_coe.2 hq, rfl⟩

theorem fals_add {V : Type} [Fintype V] [DecidableEq V] {C : LinClause V} {x w : V → ZMod 2}
    (hx : Fals C x) (hw : ∀ u ∈ formSpan C, u ⬝ᵥ w = 0) : Fals C (x + w) := by
  intro q hq
  rw [dotProduct_add, hw _ (ind_mem_formSpan hq), add_zero]
  exact hx q hq

/-! ### Duality over a finite set of variables -/

theorem dual_vec {V : Type} [Fintype V] [DecidableEq V]
    (φ : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2) : ∃ w : V → ZMod 2, ∀ g, φ g = g ⬝ᵥ w := by
  refine ⟨fun v => φ (fun j => if v = j then 1 else 0), fun g => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ φ g]
  simp [dotProduct]

/-- A form outside a space of forms is separated from it by a vector. -/
theorem exists_perp_of_notMem {V : Type} [Fintype V] [DecidableEq V]
    {U : Submodule (ZMod 2) (V → ZMod 2)} {g : V → ZMod 2} (hg : g ∉ U) :
    ∃ w : V → ZMod 2, (∀ u ∈ U, u ⬝ᵥ w = 0) ∧ g ⬝ᵥ w ≠ 0 := by
  obtain ⟨φ, hφ, hU⟩ := Submodule.exists_le_ker_of_notMem hg
  obtain ⟨w, hw⟩ := dual_vec φ
  exact ⟨w, fun u hu => by rw [← hw]; exact hU hu, by rwa [← hw]⟩

/-- If `δ` kills the forms common to `U` and `N`, some vector kills `U` and agrees with `δ`
on `N`. -/
theorem exists_perp_inf {V : Type} [Fintype V] [DecidableEq V]
    (U N : Submodule (ZMod 2) (V → ZMod 2)) (δ : V → ZMod 2)
    (h : ∀ g ∈ U ⊓ N, g ⬝ᵥ δ = 0) :
    ∃ w : V → ZMod 2, (∀ g ∈ U, g ⬝ᵥ w = 0) ∧ ∀ g ∈ N, g ⬝ᵥ w = g ⬝ᵥ δ := by
  let φδ : Module.Dual (ZMod 2) (V → ZMod 2) :=
    { toFun := fun g => g ⬝ᵥ δ
      map_add' := fun a b => add_dotProduct a b δ
      map_smul' := fun c a => smul_dotProduct c a δ }
  have hmem : φδ ∈ (U ⊓ N).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).2 fun g hg => h g hg
  rw [Subspace.dualAnnihilator_inf_eq] at hmem
  obtain ⟨φ, hφ, ψ, hψ, hsum⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨w, hw⟩ := dual_vec φ
  refine ⟨w, fun g hg => ?_, fun g hg => ?_⟩
  · rw [← hw]
    exact (Submodule.mem_dualAnnihilator _).1 hφ g hg
  · rw [← hw]
    have h1 : φ g + ψ g = g ⬝ᵥ δ := by
      have := congrArg (fun χ : Module.Dual (ZMod 2) (V → ZMod 2) => χ g) hsum
      simpa [φδ] using this
    have h2 : ψ g = 0 := (Submodule.mem_dualAnnihilator _).1 hψ g hg
    rw [← h1, h2, add_zero]

/-! ### Forms that mention only a given set of pigeons -/

section Pigeons

variable {m l : ℕ}

/-- The forms that mention only pigeons of `T`. -/
def suppIn (T : Finset (Fin m)) : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2) where
  carrier := {g | ∀ v : Fin m × Fin l, v.1 ∉ T → g v = 0}
  add_mem' := by
    intro a b ha hb v hv
    simp [ha v hv, hb v hv]
  zero_mem' := by
    intro v _
    rfl
  smul_mem' := by
    intro c a ha v hv
    simp [ha v hv]

/-- The forms that do not contain the variable `v`. -/
def vanishAt (v : Fin m × Fin l) : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2) where
  carrier := {g | g v = 0}
  add_mem' := by
    intro a b ha hb
    change a v = 0 at ha
    change b v = 0 at hb
    change a v + b v = 0
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c a ha
    change a v = 0 at ha
    change c * a v = 0
    rw [ha, mul_zero]

theorem suppIn_mono {A B : Finset (Fin m)} (h : A ⊆ B) :
    (suppIn A : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) ≤ suppIn B :=
  fun _ hg v hv => hg v fun hA => hv (h hA)

/-- The dimension of the forms of `U` that mention only pigeons of `T`. -/
noncomputable def dimIn (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2))
    (T : Finset (Fin m)) : ℕ :=
  Module.finrank (ZMod 2) ↥(U ⊓ suppIn T)

/-- `S` is good for `U`: no set of pigeons above `S` gains more dimension than pigeons. In
the language of Efremenko, Garlik and Itsykson, `U` with the pigeons of `S` deleted is
safe. -/
def Good (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) (S : Finset (Fin m)) : Prop :=
  ∀ T, S ⊆ T → dimIn U T + S.card ≤ dimIn U S + T.card

theorem dimIn_super (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) (A B : Finset (Fin m)) :
    dimIn U A + dimIn U B ≤ dimIn U (A ∩ B) + dimIn U (A ∪ B) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ suppIn A) (U ⊓ suppIn B)
  have h2 : Module.finrank (ZMod 2) ↥((U ⊓ suppIn A) ⊔ (U ⊓ suppIn B)) ≤ dimIn U (A ∪ B) :=
    Submodule.finrank_mono (sup_le (inf_le_inf_left _ (suppIn_mono Finset.subset_union_left))
      (inf_le_inf_left _ (suppIn_mono Finset.subset_union_right)))
  have h3 : Module.finrank (ZMod 2) ↥((U ⊓ suppIn A) ⊓ (U ⊓ suppIn B)) ≤ dimIn U (A ∩ B) :=
    Submodule.finrank_mono fun g hg => ⟨hg.1.1, fun v hv => by
      by_cases hA : v.1 ∈ A
      · exact hg.2.2 v fun hB => hv (Finset.mem_inter.2 ⟨hA, hB⟩)
      · exact hg.1.2 v hA⟩
  unfold dimIn at *
  omega

theorem good_mono {U U' : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)} (h : U ≤ U')
    {S : Finset (Fin m)} (hG : Good U' S) : Good U S := by
  intro T hT
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ suppIn T) (U' ⊓ suppIn S)
  have h2 : Module.finrank (ZMod 2) ↥((U ⊓ suppIn T) ⊔ (U' ⊓ suppIn S)) ≤ dimIn U' T :=
    Submodule.finrank_mono (sup_le (inf_le_inf_right _ h) (inf_le_inf_left _ (suppIn_mono hT)))
  have h3 : Module.finrank (ZMod 2) ↥((U ⊓ suppIn T) ⊓ (U' ⊓ suppIn S)) ≤ dimIn U S :=
    Submodule.finrank_mono fun g hg => ⟨hg.1.1, hg.2.2⟩
  have h4 := hG T hT
  unfold dimIn at *
  omega

theorem good_inter_le {U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)} {S : Finset (Fin m)}
    (hG : Good U S) (T : Finset (Fin m)) :
    dimIn U T + (T ∩ S).card ≤ dimIn U (T ∩ S) + T.card := by
  have h1 := dimIn_super U T S
  have h2 := hG (T ∪ S) Finset.subset_union_right
  have h3 := Finset.card_union_add_card_inter T S
  omega

theorem good_inter {U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)} {S₁ S₂ : Finset (Fin m)}
    (h₁ : Good U S₁) (h₂ : Good U S₂) : Good U (S₁ ∩ S₂) := by
  intro T hT
  have h3 := good_inter_le h₁ T
  have h4 := good_inter_le h₂ (T ∩ S₁)
  have h5 : T ∩ S₁ ∩ S₂ = S₁ ∩ S₂ := by
    rw [Finset.inter_assoc]
    exact Finset.inter_eq_right.2 hT
  rw [h5] at h4
  omega

theorem exists_good (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) :
    ∃ S : Finset (Fin m), Good U S ∧ S.card ≤ Module.finrank (ZMod 2) U := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin m)))
    (fun T => (dimIn U T : ℤ) - T.card) ⟨∅, Finset.mem_univ _⟩
  refine ⟨S, fun T _ => ?_, ?_⟩
  · have := hS T (Finset.mem_univ _)
    omega
  · have h1 := hS ∅ (Finset.mem_univ _)
    have h2 : dimIn U S ≤ Module.finrank (ZMod 2) U := Submodule.finrank_mono inf_le_left
    simp only [Finset.card_empty] at h1
    omega

theorem dimIn_mono_left {U U' : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)} (h : U ≤ U')
    (T : Finset (Fin m)) : dimIn U T ≤ dimIn U' T :=
  Submodule.finrank_mono (inf_le_inf_right _ h)

/-! ### Pivots: one bit per pigeon outside a good set -/

/-- One step of the choice of pivots. For a pigeon `i` outside the good set `K` there is a
bit `b` of `i` such that, once the forms containing `(i, b)` are discarded, every set above
`K ∪ {i}` gains strictly less dimension over `K` than pigeons. -/
theorem exists_pivot (hl : 0 < l) {U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)}
    {K : Finset (Fin m)} (hG : Good U K) {i : Fin m} (hi : i ∉ K) :
    ∃ b : Fin l, ∀ T, insert i K ⊆ T →
      dimIn (U ⊓ vanishAt (i, b)) T + K.card + 1 ≤ dimIn U K + T.card := by
  classical
  have hK : ∀ T, insert i K ⊆ T → K ⊆ T := fun T hT => (Finset.subset_insert i K).trans hT
  by_cases htight : ∃ T, insert i K ⊆ T ∧ dimIn U T + K.card = dimIn U K + T.card
  · obtain ⟨T₀, hT₀mem, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun T => insert i K ⊆ T ∧ dimIn U T + K.card = dimIn U K + T.card)
      Finset.card
      (by
        obtain ⟨T, hT⟩ := htight
        exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩⟩)
    obtain ⟨hT₀, hT₀eq⟩ := (Finset.mem_filter.1 hT₀mem).2
    have hiT₀ : i ∈ T₀ := hT₀ (Finset.mem_insert_self i K)
    have hlt : dimIn U (T₀.erase i) < dimIn U T₀ := by
      have h1 := hG (T₀.erase i)
        (fun j hj => Finset.mem_erase.2 ⟨fun h => hi (h ▸ hj), hK T₀ hT₀ hj⟩)
      have h2 := Finset.card_erase_add_one hiT₀
      omega
    have hnle : ¬ (U ⊓ suppIn T₀ ≤ U ⊓ suppIn (T₀.erase i)) := fun hle => by
      have := Submodule.finrank_mono hle
      unfold dimIn at hlt
      omega
    obtain ⟨g₀, hg₀, hg₀n⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have hex : ∃ b, g₀ (i, b) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hg₀n ⟨hg₀.1, fun v hv => ?_⟩
      by_cases hv1 : v.1 = i
      · obtain ⟨v1, v2⟩ := v
        simp only at hv1
        subst hv1
        exact hcon v2
      · exact hg₀.2 v fun hvT => hv (Finset.mem_erase.2 ⟨hv1, hvT⟩)
    obtain ⟨b, hb⟩ := hex
    refine ⟨b, fun T hT => ?_⟩
    have hmono := dimIn_mono_left (inf_le_left : U ⊓ vanishAt (i, b) ≤ U) T
    have hGT := hG T (hK T hT)
    by_cases htT : dimIn U T + K.card = dimIn U K + T.card
    · have hsub : T₀ ⊆ T := by
        have h1 := dimIn_super U T₀ T
        have h2 := hG (T₀ ∪ T) ((hK T₀ hT₀).trans Finset.subset_union_left)
        have h3 := hG (T₀ ∩ T) (Finset.subset_inter (hK T₀ hT₀) (hK T hT))
        have h4 := Finset.card_union_add_card_inter T₀ T
        have h5 : T₀.card ≤ (T₀ ∩ T).card := hmin (T₀ ∩ T)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.subset_inter hT₀ hT, by omega⟩)
        have h6 : T₀ ∩ T = T₀ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left h5
        exact Finset.inter_eq_left.1 h6
      have hstrict : (U ⊓ vanishAt (i, b)) ⊓ suppIn T < U ⊓ suppIn T := by
        refine lt_of_le_of_ne (inf_le_inf_right _ inf_le_left) fun heq => ?_
        have hg : g₀ ∈ U ⊓ suppIn T := ⟨hg₀.1, suppIn_mono hsub hg₀.2⟩
        rw [← heq] at hg
        exact hb hg.1.2
      have := Submodule.finrank_lt_finrank_of_lt hstrict
      unfold dimIn at *
      omega
    · omega
  · refine ⟨⟨0, hl⟩, fun T hT => ?_⟩
    have hmono := dimIn_mono_left (inf_le_left : U ⊓ vanishAt (i, ⟨0, hl⟩) ≤ U) T
    have hGT := hG T (hK T hT)
    have hne : dimIn U T + K.card ≠ dimIn U K + T.card := fun h => htight ⟨T, hT, h⟩
    omega

/-- For a good set `K` of `U` one can pick one bit `zf i` in each pigeon `i` so that every
form of `U` that contains no picked bit of a pigeon outside `K` mentions only pigeons of `K`.
This plays the role of the matroid form of Hall's theorem in the paper. -/
theorem exists_pivots (hl : 0 < l) : ∀ (n : ℕ) (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2))
    (K : Finset (Fin m)), m ≤ K.card + n → Good U K →
    ∃ zf : Fin m → Fin l, ∀ g ∈ U, (∀ i, i ∉ K → g (i, zf i) = 0) → g ∈ suppIn K := by
  have triv : ∀ (U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) (K : Finset (Fin m)),
      K = Finset.univ →
      ∃ zf : Fin m → Fin l, ∀ g ∈ U, (∀ i, i ∉ K → g (i, zf i) = 0) → g ∈ suppIn K :=
    fun U K hK => ⟨fun _ => ⟨0, hl⟩, fun g _ _ v hv => absurd (hK ▸ Finset.mem_univ v.1) hv⟩
  intro n
  induction n with
  | zero =>
    intro U K hcard _
    refine triv U K (Finset.eq_univ_of_card K ?_)
    have := Finset.card_le_univ K
    rw [Fintype.card_fin] at this ⊢
    omega
  | succ n ih =>
    intro U K hcard hG
    by_cases hKu : K = Finset.univ
    · exact triv U K hKu
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ K := by
        by_contra h
        push Not at h
        exact hKu (Finset.eq_univ_iff_forall.2 h)
      obtain ⟨b, hb⟩ := exists_pivot hl hG hi
      have hle : U ⊓ suppIn K ≤ (U ⊓ vanishAt (i, b)) ⊓ suppIn (insert i K) :=
        fun g hg => ⟨⟨hg.1, hg.2 (i, b) hi⟩, suppIn_mono (Finset.subset_insert i K) hg.2⟩
      have hd : dimIn U K ≤ dimIn (U ⊓ vanishAt (i, b)) (insert i K) :=
        Submodule.finrank_mono hle
      have hcardK : (insert i K).card = K.card + 1 := Finset.card_insert_of_notMem hi
      have hG' : Good (U ⊓ vanishAt (i, b)) (insert i K) := fun T hT => by
        have := hb T hT
        omega
      obtain ⟨zf', hzf'⟩ := ih _ (insert i K) (by omega) hG'
      have heq : U ⊓ suppIn K = (U ⊓ vanishAt (i, b)) ⊓ suppIn (insert i K) :=
        Submodule.eq_of_le_of_finrank_le hle (by
          have := hb _ (Finset.Subset.refl _)
          unfold dimIn at this
          omega)
      refine ⟨Function.update zf' i b, fun g hg hz => ?_⟩
      have hgi : g (i, b) = 0 := by simpa using hz i hi
      have hmem : g ∈ (U ⊓ vanishAt (i, b)) ⊓ suppIn (insert i K) := by
        refine ⟨⟨hg, hgi⟩, hzf' g ⟨hg, hgi⟩ fun j hj => ?_⟩
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i K)
        have := hz j (fun h => hj (Finset.mem_insert_of_mem h))
        rwa [Function.update_of_ne hji] at this
      rw [← heq] at hmem
      exact hmem.2

/-- A set is not good if some pigeon outside it has two of its bits in `U`. -/
theorem not_good_of_two (hl : 2 ≤ l) {U : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)}
    {S : Finset (Fin m)} (hG : Good U S) {j : Fin m} (hj : j ∉ S)
    (hU : ∀ b : Fin l, Pi.single (j, b) (1 : ZMod 2) ∈ U) : False := by
  obtain ⟨b0, hb0⟩ : ∃ b : Fin l, b = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b : Fin l, b = ⟨1, by omega⟩ := ⟨_, rfl⟩
  have hb : (j, b0) ≠ (j, b1) := by
    rw [hb0, hb1]
    simp [Fin.ext_iff]
  have hsupp : ∀ b : Fin l, Pi.single (j, b) (1 : ZMod 2) ∈
      (suppIn (insert j S) : Submodule (ZMod 2) (Fin m × Fin l → ZMod 2)) := fun b v hv =>
    Pi.single_eq_of_ne (fun h => hv (by rw [h]; exact Finset.mem_insert_self j S)) _
  obtain ⟨A0, hA0⟩ : ∃ A, A = U ⊓ suppIn S := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A, A = A0 ⊔ Submodule.span (ZMod 2) {Pi.single (j, b0) (1 : ZMod 2)} :=
    ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A, A = A1 ⊔ Submodule.span (ZMod 2) {Pi.single (j, b1) (1 : ZMod 2)} :=
    ⟨_, rfl⟩
  have h01 : A0 < A1 := by
    refine lt_of_le_of_ne (hA1 ▸ le_sup_left) fun h => ?_
    have hmem : Pi.single (j, b0) (1 : ZMod 2) ∈ A0 := by
      rw [h, hA1]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    rw [hA0] at hmem
    have := hmem.2 (j, b0) hj
    simp at this
  have hA1le : A1 ≤ vanishAt (j, b1) := by
    rw [hA1, hA0]
    refine sup_le (fun g hg => hg.2 (j, b1) hj) ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Pi.single_eq_of_ne hb.symm _
  have h12 : A1 < A2 := by
    refine lt_of_le_of_ne (hA2 ▸ le_sup_left) fun h => ?_
    have hmem : Pi.single (j, b1) (1 : ZMod 2) ∈ A1 := by
      rw [h, hA2]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have : Pi.single (j, b1) (1 : ZMod 2) (j, b1) = 0 := hA1le hmem
    simp at this
  have hA2le : A2 ≤ U ⊓ suppIn (insert j S) := by
    rw [hA2, hA1, hA0]
    refine sup_le (sup_le (inf_le_inf_left _ (suppIn_mono (Finset.subset_insert j S))) ?_) ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hU b0, hsupp b0⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hU b1, hsupp b1⟩
  have f1 := Submodule.finrank_lt_finrank_of_lt h01
  have f2 := Submodule.finrank_lt_finrank_of_lt h12
  have f3 := Submodule.finrank_mono hA2le
  have f4 := hG (insert j S) (Finset.subset_insert j S)
  rw [Finset.card_insert_of_notMem hj] at f4
  unfold dimIn at f4
  rw [← hA0] at f4
  omega

/-! ### Spreading pigeons over holes -/

/-- The hole of pigeon `i` under the vector `x`. -/
def hole (x : Fin m × Fin l → ZMod 2) (i : Fin m) : Fin l → ZMod 2 := fun b => x (i, b)

/-- The vector `x` sends the pigeons of `S` to different holes. -/
def InjOn (x : Fin m × Fin l → ZMod 2) (S : Finset (Fin m)) : Prop :=
  ∀ i ∈ S, ∀ i' ∈ S, hole x i = hole x i' → i = i'

/-- Flip one bit of a hole. -/
def flipAt (h : Fin l → ZMod 2) (b : Fin l) : Fin l → ZMod 2 := Function.update h b (h b + 1)

theorem flipAt_flipAt (h : Fin l → ZMod 2) (b : Fin l) : flipAt (flipAt h b) b = h := by
  have hz : ∀ z : ZMod 2, z + 1 + 1 = z := by decide
  unfold flipAt
  rw [Function.update_self, Function.update_idem, hz, Function.update_eq_self]

/-- The holes pigeon `i` may end in when its hole is `h` and its pivot bit is not under
control: pigeons of `S₀` stay put, the others may have their pivot bit flipped. -/
def posSet (S₀ : Finset (Fin m)) (zf : Fin m → Fin l) (i : Fin m) (h : Fin l → ZMod 2) :
    Finset (Fin l → ZMod 2) :=
  if i ∈ S₀ then {h} else {h, flipAt h (zf i)}

theorem posSet_card_le (S₀ : Finset (Fin m)) (zf : Fin m → Fin l) (i : Fin m)
    (h : Fin l → ZMod 2) : (posSet S₀ zf i h).card ≤ 2 := by
  unfold posSet
  split_ifs
  · simp
  · exact Finset.card_le_two

theorem hole_mem_posSet (S₀ : Finset (Fin m)) (zf : Fin m → Fin l)
    (y y' : Fin m × Fin l → ZMod 2) (i : Fin m)
    (h : ∀ v : Fin m × Fin l, v.1 ∈ S₀ ∨ v.2 ≠ zf v.1 → y' v = y v) :
    hole y' i ∈ posSet S₀ zf i (hole y i) := by
  unfold posSet
  by_cases hi : i ∈ S₀
  · simp only [hi, ↓reduceIte, Finset.mem_singleton]
    funext b
    exact h (i, b) (Or.inl hi)
  · simp only [hi, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
    have hz : ∀ a c : ZMod 2, a = c ∨ a = c + 1 := by decide
    rcases hz (y' (i, zf i)) (y (i, zf i)) with e | e
    · left
      funext b
      by_cases hb : b = zf i
      · rw [hb]
        exact e
      · exact h (i, b) (Or.inr hb)
    · right
      funext b
      by_cases hb : b = zf i
      · rw [hb]
        simpa [flipAt, hole] using e
      · have := h (i, b) (Or.inr hb)
        simpa [flipAt, hole, Function.update_of_ne hb] using this

/-- If `x` is injective on `S₀ ⊆ S` and `S` has at most a quarter as many pigeons as there
are holes, the pigeons of `S` outside `S₀` can be moved so that the sets of possible holes of
the pigeons of `S` are pairwise disjoint. -/
theorem exists_spread (S₀ S : Finset (Fin m)) (zf : Fin m → Fin l)
    (x : Fin m × Fin l → ZMod 2) (hS : S₀ ⊆ S) (hinj : InjOn x S₀)
    (hcard : 4 * S.card ≤ 2 ^ l) :
    ∃ y : Fin m × Fin l → ZMod 2, (∀ v : Fin m × Fin l, v.1 ∈ S₀ → y v = x v) ∧
      ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' →
        Disjoint (posSet S₀ zf i (hole y i)) (posSet S₀ zf i' (hole y i')) := by
  classical
  have key : ∀ J : Finset (Fin m), J ⊆ S \ S₀ →
      ∃ y : Fin m × Fin l → ZMod 2, (∀ v : Fin m × Fin l, v.1 ∈ S₀ → y v = x v) ∧
        ∀ i ∈ S₀ ∪ J, ∀ i' ∈ S₀ ∪ J, i ≠ i' →
          Disjoint (posSet S₀ zf i (hole y i)) (posSet S₀ zf i' (hole y i')) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨x, fun _ _ => rfl, fun i hi i' hi' hne => ?_⟩
      rw [Finset.union_empty] at hi hi'
      unfold posSet
      simp only [hi, hi', ↓reduceIte, Finset.disjoint_singleton]
      exact fun h => hne (hinj i hi i' hi' h)
    | insert i₀ J hi₀ ih =>
      intro hJ
      obtain ⟨y, hyx, hy⟩ := ih ((Finset.subset_insert _ _).trans hJ)
      obtain ⟨hi₀S, hi₀S₀⟩ := Finset.mem_sdiff.1 (hJ (Finset.mem_insert_self _ _))
      obtain ⟨P, hP⟩ : ∃ P, P = (S₀ ∪ J).biUnion (fun i => posSet S₀ zf i (hole y i)) :=
        ⟨_, rfl⟩
      have hPcard : P.card ≤ (S₀ ∪ J).card * 2 := by
        rw [hP]
        exact Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => posSet_card_le S₀ zf i _)
      have hsub : S₀ ∪ J ⊆ S.erase i₀ := by
        intro j hj
        rcases Finset.mem_union.1 hj with hj | hj
        · exact Finset.mem_erase.2 ⟨fun h => hi₀S₀ (h ▸ hj), hS hj⟩
        · exact Finset.mem_erase.2 ⟨fun h => hi₀ (h ▸ hj),
            (Finset.mem_sdiff.1 (hJ (Finset.mem_insert_of_mem hj))).1⟩
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.card_erase_add_one hi₀S
      obtain ⟨Bad, hBad⟩ : ∃ B, B = P ∪ P.image (fun h => flipAt h (zf i₀)) := ⟨_, rfl⟩
      have hBadcard : Bad.card < 2 ^ l := by
        have h1 := Finset.card_union_le P (P.image fun h => flipAt h (zf i₀))
        have h2 := Finset.card_image_le (s := P) (f := fun h => flipAt h (zf i₀))
        rw [hBad]
        omega
      obtain ⟨h, hh⟩ : ∃ h, h ∉ Bad := by
        by_contra hcon
        push Not at hcon
        have hu : Bad = Finset.univ := Finset.eq_univ_iff_forall.2 hcon
        rw [hu, Finset.card_univ] at hBadcard
        simp at hBadcard
      have hhP : h ∉ P := fun hm => hh (hBad ▸ Finset.mem_union_left _ hm)
      have hhP' : flipAt h (zf i₀) ∉ P := fun hm =>
        hh (hBad ▸ Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, hm, flipAt_flipAt h _⟩))
      obtain ⟨y₁, hy₁def⟩ : ∃ y₁ : Fin m × Fin l → ZMod 2,
          y₁ = fun v => if v.1 = i₀ then h v.2 else y v := ⟨_, rfl⟩
      have hy₁i₀ : hole y₁ i₀ = h := by
        funext b
        simp [hole, hy₁def]
      have hy₁ : ∀ i, i ≠ i₀ → hole y₁ i = hole y i := by
        intro i hi
        funext b
        simp [hole, hy₁def, hi]
      have hnew : ∀ i' ∈ S₀ ∪ J,
          Disjoint (posSet S₀ zf i₀ h) (posSet S₀ zf i' (hole y i')) := by
        intro i' hi'
        rw [Finset.disjoint_left]
        intro k hk hk'
        have hkP : k ∈ P := hP ▸ Finset.mem_biUnion.2 ⟨i', hi', hk'⟩
        unfold posSet at hk
        simp only [hi₀S₀, ↓reduceIte] at hk
        rcases Finset.mem_insert.1 hk with e | hk
        · exact hhP (e ▸ hkP)
        · rw [Finset.mem_singleton] at hk
          exact hhP' (hk ▸ hkP)
      have hne₀ : ∀ i ∈ S₀ ∪ J, i ≠ i₀ := fun i hi => (Finset.mem_erase.1 (hsub hi)).1
      have hmem : ∀ i, i ∈ S₀ ∪ insert i₀ J → i = i₀ ∨ i ∈ S₀ ∪ J := by
        intro i hi
        simp only [Finset.mem_union, Finset.mem_insert] at hi ⊢
        tauto
      refine ⟨y₁, fun v hv => ?_, fun i hi i' hi' hne => ?_⟩
      · have hv' : v.1 ≠ i₀ := fun h => hi₀S₀ (h ▸ hv)
        rw [hy₁def]
        simp [hv', hyx v hv]
      · rcases hmem i hi with e | hi <;> rcases hmem i' hi' with e' | hi'
        · exact absurd (e.trans e'.symm) hne
        · rw [e, hy₁i₀, hy₁ i' (hne₀ i' hi')]
          exact hnew i' hi'
        · rw [e', hy₁i₀, hy₁ i (hne₀ i hi)]
          exact (hnew i hi).symm
        · rw [hy₁ i (hne₀ i hi), hy₁ i' (hne₀ i' hi')]
          exact hy i hi i' hi' hne
  obtain ⟨y, hyx, hy⟩ := key (S \ S₀) (Finset.Subset.refl _)
  rw [Finset.union_sdiff_of_subset hS] at hy
  exact ⟨y, hyx, hy⟩

/-! ### Local consistency -/

/-- The forms that contain no pivot bit of a pigeon outside `K`. -/
def vanishPivots (K : Finset (Fin m)) (zf : Fin m → Fin l) :
    Submodule (ZMod 2) (Fin m × Fin l → ZMod 2) where
  carrier := {g | ∀ i, i ∉ K → g (i, zf i) = 0}
  add_mem' := by
    intro a b ha hb i hi
    change a (i, zf i) + b (i, zf i) = 0
    rw [ha i hi, hb i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    change c * a (i, zf i) = 0
    rw [ha i hi, mul_zero]

/-- A linear clause is locally consistent: some vector falsifies it and sends the pigeons of
some good set of its span of forms to different holes. -/
def LC (C : LinClause (Fin m × Fin l)) : Prop :=
  ∃ S : Finset (Fin m), Good (formSpan C) S ∧
    ∃ x : Fin m × Fin l → ZMod 2, Fals C x ∧ InjOn x S

theorem formSpan_insert {V : Type} [DecidableEq V] (q : LinEq V) (C : LinClause V) :
    formSpan (insert q C) = Submodule.span (ZMod 2) {ind q.1} ⊔ formSpan C := by
  unfold formSpan
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]

theorem lc_empty : LC (∅ : LinClause (Fin m × Fin l)) := by
  refine ⟨∅, fun T _ => ?_, 0, fun q hq => absurd hq (Finset.notMem_empty q),
    fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have h : formSpan (∅ : LinClause (Fin m × Fin l)) = ⊥ := by simp [formSpan]
  unfold dimIn
  rw [h, bot_inf_eq, bot_inf_eq, finrank_bot, Finset.card_empty]
  omega

/-- Local consistency passes from a line to any line that semantically implies it. -/
theorem lc_of_imp {C D : LinClause (Fin m × Fin l)}
    (h : ∀ a : Fin m × Fin l → Bool, LinClauseSat a C → LinClauseSat a D) (hD : LC D) :
    LC C := by
  obtain ⟨S, hG, x, hx, hinj⟩ := hD
  have hle : formSpan C ≤ formSpan D := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    by_contra hmem
    obtain ⟨w, hw, hne⟩ := exists_perp_of_notMem hmem
    have h1 := fals_of_imp h hx q (Finset.mem_coe.1 hq)
    have h2 := fals_of_imp h (fals_add hx hw) q (Finset.mem_coe.1 hq)
    rw [dotProduct_add] at h2
    have hz : ∀ a c d : ZMod 2, a ≠ d → c ≠ 0 → a + c ≠ d → False := by decide
    exact hz _ _ _ h1 hne h2
  exact ⟨S, good_mono hle hG, x, fals_of_imp h hx, hinj⟩

/-- The splitting step: a locally consistent line of small rank stays locally consistent
after adding one of the two equations on any linear form. -/
theorem lc_split (hl : 0 < l) (R : LinClause (Fin m × Fin l)) (f : Finset (Fin m × Fin l))
    (hLC : LC R) (hsmall : 4 * (linRank R + 1) ≤ 2 ^ l) :
    ∃ a : Bool, LC (insert (f, a) R) := by
  classical
  obtain ⟨S, hGS, x, hx, hinj⟩ := hLC
  obtain ⟨U'', hU''⟩ : ∃ U'', U'' = Submodule.span (ZMod 2) {ind f} ⊔ formSpan R := ⟨_, rfl⟩
  have hspan : ∀ a : Bool, formSpan (insert (f, a) R) = U'' := fun a => by
    rw [hU'', formSpan_insert]
  have hle : formSpan R ≤ U'' := hU'' ▸ le_sup_right
  have hdim : Module.finrank (ZMod 2) U'' ≤ linRank R + 1 := by
    rw [hU'', linRank_eq]
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span (ZMod 2) {ind f}) (formSpan R)
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {ind f}) ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 2) ({ind f} : Set (Fin m × Fin l → ZMod 2))
      simpa using this
    omega
  obtain ⟨S'', hGS'', hS''card⟩ := exists_good U''
  have hG0 : Good (formSpan R) (S ∩ S'') := good_inter hGS (good_mono hle hGS'')
  have hinj0 : InjOn x (S ∩ S'') := fun i hi i' hi' h =>
    hinj i (Finset.mem_inter.1 hi).1 i' (Finset.mem_inter.1 hi').1 h
  obtain ⟨zf, hzf⟩ := exists_pivots hl m (formSpan R) (S ∩ S'') (by omega) hG0
  obtain ⟨y, hyx, hy⟩ := exists_spread (S ∩ S'') S'' zf x Finset.inter_subset_right hinj0
    (by omega)
  obtain ⟨w, hwU, hwN⟩ := exists_perp_inf (formSpan R) (vanishPivots (S ∩ S'') zf) (y - x) (by
    intro g hg
    have hgs := hzf g hg.1 hg.2
    unfold dotProduct
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 ∈ S ∩ S''
    · simp [hyx v hv]
    · rw [hgs v hv, zero_mul])
  have hy' : ∀ v : Fin m × Fin l, v.1 ∈ S ∩ S'' ∨ v.2 ≠ zf v.1 → (x + w) v = y v := by
    intro v hv
    have hmem : Pi.single v (1 : ZMod 2) ∈ vanishPivots (S ∩ S'') zf := by
      intro i hi
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      rcases hv with h | h
      · exact hi h
      · exact h rfl
    have := hwN _ hmem
    rw [single_one_dotProduct, single_one_dotProduct] at this
    simp [this]
  have hfals : Fals R (x + w) := fals_add hx hwU
  have hinj' : InjOn (x + w) S'' := by
    intro i hi i' hi' heq
    by_contra hne
    have h1 := hole_mem_posSet (S ∩ S'') zf y (x + w) i hy'
    have h2 := hole_mem_posSet (S ∩ S'') zf y (x + w) i' hy'
    rw [heq] at h1
    exact Finset.disjoint_left.1 (hy i hi i' hi' hne) h1 h2
  by_cases h0 : ind f ⬝ᵥ (x + w) = 0
  · refine ⟨true, S'', by rw [hspan]; exact hGS'', x + w, ?_, hinj'⟩
    intro q hq
    rcases Finset.mem_insert.1 hq with e | hq
    · rw [e]
      simp [toZ, h0]
    · exact hfals q hq
  · refine ⟨false, S'', by rw [hspan]; exact hGS'', x + w, ?_, hinj'⟩
    intro q hq
    rcases Finset.mem_insert.1 hq with e | hq
    · rw [e]
      simpa [toZ] using h0
    · exact hfals q hq

/-! ### The axioms and the walk through a refutation -/

theorem ind_singleton {V : Type} [DecidableEq V] (v : V) :
    ind ({v} : Finset V) = Pi.single v (1 : ZMod 2) := by
  funext u
  by_cases h : u = v
  · simp [ind, h]
  · simp [ind, h]

theorem bphp_axiom_mem {i i' : Fin m} {α : Fin l → Bool} (j : Fin m) (hj : j = i ∨ j = i')
    (b : Fin l) :
    (({(j, b)} : Finset (Fin m × Fin l)), !α b) ∈
      linOfClause (Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
        Finset.univ.image (fun b : Fin l => ((i', b), !α b))) := by
  refine Finset.mem_image.2 ⟨((j, b), !α b), ?_, rfl⟩
  rcases hj with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)

/-- No axiom of the bit pigeonhole formula is locally consistent, when holes have at least
two bits. -/
theorem not_lc_axiom (hl : 2 ≤ l) {C : Clause (Fin m × Fin l)} (hC : C ∈ BPHP m l) :
    ¬ LC (linOfClause C) := by
  obtain ⟨i, i', α, hne, rfl⟩ := hC
  rintro ⟨S, hG, x, hx, hinj⟩
  have hval : ∀ j, (j = i ∨ j = i') → ∀ b, x (j, b) ≠ toZ (!α b) := by
    intro j hj b
    have := hx _ (bphp_axiom_mem (α := α) j hj b)
    dsimp only at this
    rwa [ind_singleton, single_one_dotProduct] at this
  have hU : ∀ j, (j = i ∨ j = i') → ∀ b, Pi.single (j, b) (1 : ZMod 2) ∈ formSpan (linOfClause
      (Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
        Finset.univ.image (fun b : Fin l => ((i', b), !α b)))) := by
    intro j hj b
    have := ind_mem_formSpan (bphp_axiom_mem (α := α) j hj b)
    dsimp only at this
    rwa [ind_singleton] at this
  have hz : ∀ a c d : ZMod 2, a ≠ d → c ≠ d → a = c := by decide
  have hsame : hole x i = hole x i' :=
    funext fun b => hz _ _ _ (hval i (Or.inl rfl) b) (hval i' (Or.inr rfl) b)
  by_cases hi : i ∈ S
  · by_cases hi' : i' ∈ S
    · exact hne (hinj i hi i' hi' hsame)
    · exact not_good_of_two hl hG hi' (hU i' (Or.inr rfl))
  · exact not_good_of_two hl hG hi (hU i (Or.inl rfl))

/-- Walking a derivation from the bit pigeonhole axioms: either some line has large rank, or
no line is locally consistent. -/
theorem lc_or_big (hl : 2 ≤ l) {π : List (LinClause (Fin m × Fin l))}
    (h : IsLinDerivation ((fun C => linOfClause C) '' BPHP m l) π) :
    (∃ C ∈ π, 2 ^ l ≤ 4 * linRank C) ∨ ∀ C ∈ π, ¬ LC C := by
  induction h with
  | nil => exact Or.inr (by simp)
  | @ax π C _ hC ih =>
    rcases ih with ⟨E, hE, hbig⟩ | hno
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hbig⟩
    · obtain ⟨C₀, hC₀, rfl⟩ := hC
      refine Or.inr fun E hE => ?_
      rcases List.mem_cons.1 hE with rfl | hE
      · exact not_lc_axiom hl hC₀
      · exact hno E hE
  | @res π C D R _ hC hD hR ih =>
    rcases ih with ⟨E, hE, hbig⟩ | hno
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hbig⟩
    · by_cases hbig : 2 ^ l ≤ 4 * linRank R
      · exact Or.inl ⟨R, List.mem_cons_self, hbig⟩
      · refine Or.inr fun E hE => ?_
        rcases List.mem_cons.1 hE with rfl | hE
        · intro hLC
          obtain ⟨f, hfC, hfD, hRe⟩ := hR
          have h4 : 4 * (linRank E + 1) ≤ 2 ^ l := by
            obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
            rw [pow_add] at hbig ⊢
            omega
          obtain ⟨a, ha⟩ := lc_split (by omega) E f hLC h4
          cases a
          · refine hno C hC (lc_of_imp (fun a' hs => ?_) ha)
            obtain ⟨q, hq, hqs⟩ := hs
            refine ⟨q, ?_, hqs⟩
            by_cases hqf : q = (f, false)
            · rw [hqf]
              exact Finset.mem_insert_self _ _
            · rw [hRe]
              exact Finset.mem_insert_of_mem
                (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hqf, hq⟩))
          · refine hno D hD (lc_of_imp (fun a' hs => ?_) ha)
            obtain ⟨q, hq, hqs⟩ := hs
            refine ⟨q, ?_, hqs⟩
            by_cases hqf : q = (f, true)
            · rw [hqf]
              exact Finset.mem_insert_self _ _
            · rw [hRe]
              exact Finset.mem_insert_of_mem
                (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hqf, hq⟩))
        · exact hno E hE
  | @weak π C D _ hC hw ih =>
    rcases ih with ⟨E, hE, hbig⟩ | hno
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hbig⟩
    · refine Or.inr fun E hE => ?_
      rcases List.mem_cons.1 hE with rfl | hE
      · exact fun hLC => hno C hC (lc_of_imp hw hLC)
      · exact hno E hE

/-! ### Holes with one bit -/

theorem linRank_axiom_pos (hl : 0 < l) {C : Clause (Fin m × Fin l)} (hC : C ∈ BPHP m l) :
    0 < linRank (linOfClause C) := by
  obtain ⟨i, i', α, hne, rfl⟩ := hC
  rw [linRank_eq, Nat.pos_iff_ne_zero]
  intro h0
  rw [Submodule.finrank_eq_zero] at h0
  have hmem := ind_mem_formSpan (bphp_axiom_mem (i' := i') (α := α) i (Or.inl rfl) ⟨0, hl⟩)
  rw [h0, Submodule.mem_bot] at hmem
  have := congrFun hmem (i, ⟨0, hl⟩)
  simp [ind] at this

theorem nil_of_rank_zero (hl : 0 < l) {π : List (LinClause (Fin m × Fin l))}
    (h : IsLinDerivation ((fun C => linOfClause C) '' BPHP m l) π)
    (h0 : ∀ C ∈ π, linRank C = 0) : π = [] := by
  induction h with
  | nil => rfl
  | @ax π C _ hC _ =>
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    have h1 := linRank_axiom_pos hl hC₀
    have h2 : linRank (linOfClause C₀) = 0 := h0 _ List.mem_cons_self
    omega
  | @res π C D R _ hC _ _ ih =>
    have := ih fun E hE => h0 E (List.mem_cons_of_mem _ hE)
    subst this
    simp at hC
  | @weak π C D _ hC _ ih =>
    have := ih fun E hE => h0 E (List.mem_cons_of_mem _ hE)
    subst this
    simp at hC

end Pigeons

/-- **Efremenko, Garlik, Itsykson (STOC 2024), Theorem 5.5.** Every Res(⊕) refutation of the
bit pigeonhole formula with `m` pigeons and `2 ^ l` holes, `l ≥ 1`, has a line whose set of
linear forms has rank at least a quarter of the number of holes. -/
theorem bphp_rank : ∀ (m l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin l))),
    0 < l → 2 ^ l < m →
    PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP m l) π →
    ∃ C ∈ π, 2 ^ l ≤ 4 * PEqualNP.ProofComplexity.linRank C := by
  intro m l π hl _ hπ
  by_cases h2 : 2 ≤ l
  · rcases lc_or_big h2 hπ.1 with h | h
    · exact h
    · exact absurd lc_empty (h ∅ hπ.2)
  · have hl1 : l = 1 := by omega
    subst hl1
    by_contra hcon
    push Not at hcon
    have h0 : ∀ C ∈ π, linRank C = 0 := fun C hC => by
      have := hcon C hC
      omega
    have hnil := nil_of_rank_zero hl hπ.1 h0
    have hmem := hπ.2
    rw [hnil] at hmem
    simp at hmem

end PEqualNP.ProofComplexity.Helpers
