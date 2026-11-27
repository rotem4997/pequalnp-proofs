import Mathlib

/-!
# Helpers: extending consistent moment families on partial matchings

Rows `ι`, columns `κ`. A partial matching is a finite set of cells with distinct rows and
distinct columns. This file proves, with no topology, the filling statement behind the
extension of `k`-consistent families of `ZMod 2` values on partial matchings.

Plan (all sums are over `ZMod 2`):

* `bd c T = ∑ v ∉ T, c (insert v T)` for any function `c` on finite sets, `bd_bd`;
* `Exact K k`: every function supported on the `k`-element members of `K` with `bd c = 0`
  is `bd g` for a `g` supported on the `(k+1)`-element members of `K`;
* `exact_of_cone` (a family closed under inserting one fixed vertex is exact everywhere),
  `exact_union` (two-piece gluing), `exact_zero_of_vertex`;
* three families of matchings: `D R C` (cells in `R × C`), `G R C A` (in `R × C`, missing a
  column of `A`), `S R C i B` (in `R × C`, extendable by a cell `(i, j)` with `j ∈ B`);
* `exact_D`: `Exact (D R C) k` when `k + 1 ≤ |R|` and `|R| + k ≤ |C|`;
* `consistent_extend`: the extension statement for `2 * k + 1 ≤ N`.
-/

namespace PEqualNP.ProofComplexity.Helpers.MomentExt

open Finset

set_option linter.unusedSectionVars false

section Generic

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The boundary of a function on finite sets: sum over the ways to add one new element. -/
def bd (c : Finset V → ZMod 2) (T : Finset V) : ZMod 2 := ∑ v ∈ Tᶜ, c (insert v T)

theorem bd_add (c d : Finset V → ZMod 2) : bd (c + d) = bd c + bd d := by
  funext T
  simp [bd, Finset.sum_add_distrib]

theorem bd_zero : bd (0 : Finset V → ZMod 2) = 0 := by
  funext T
  simp [bd]

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem bd_bd (c : Finset V → ZMod 2) : bd (bd c) = 0 := by
  funext T
  have h1 : bd (bd c) T
      = ∑ p ∈ (Tᶜ ×ˢ Tᶜ).filter (fun p => p.2 ≠ p.1), c (insert p.2 (insert p.1 T)) := by
    rw [Finset.sum_filter, Finset.sum_product]
    unfold bd
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [mem_compl, mem_insert, not_or, mem_filter]
    tauto
  rw [h1]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    rw [Finset.insert_comm p.1 p.2 T]
    exact zmod2_add_self _
  · intro p hp _ h
    have := (mem_filter.mp hp).2
    exact this (congrArg Prod.fst h)
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, fun h => hp.2 h.symm⟩
  · intro p _
    rfl

/-- `c` is supported on the members of `K` with exactly `k` elements. -/
def IsChain (K : Finset V → Prop) (k : ℕ) (c : Finset V → ZMod 2) : Prop :=
  ∀ T, c T ≠ 0 → K T ∧ T.card = k

/-- Every `k`-chain of `K` with zero boundary is the boundary of a `(k+1)`-chain of `K`. -/
def Exact (K : Finset V → Prop) (k : ℕ) : Prop :=
  ∀ c, IsChain K k c → bd c = 0 → ∃ g, IsChain K (k + 1) g ∧ bd g = c

/-- Closed under subsets. -/
def DownClosed (K : Finset V → Prop) : Prop := ∀ S T, S ⊆ T → K T → K S

theorem IsChain.add {K : Finset V → Prop} {k : ℕ} {c d : Finset V → ZMod 2}
    (hc : IsChain K k c) (hd : IsChain K k d) : IsChain K k (c + d) := by
  intro T hT
  by_cases h : c T = 0
  · apply hd T
    intro h'
    apply hT
    simp [h, h']
  · exact hc T h

theorem IsChain.mono {K L : Finset V → Prop} {k : ℕ} {c : Finset V → ZMod 2}
    (hc : IsChain K k c) (h : ∀ T, K T → L T) : IsChain L k c :=
  fun T hT => ⟨h T (hc T hT).1, (hc T hT).2⟩

theorem IsChain.bd {K : Finset V → Prop} {k : ℕ} {c : Finset V → ZMod 2}
    (hK : DownClosed K) (hc : IsChain K (k + 1) c) : IsChain K k (bd c) := by
  intro T hT
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨h1, h2⟩ := hc _ hne
  refine ⟨hK _ _ (Finset.subset_insert v T) h1, ?_⟩
  rw [Finset.card_insert_of_notMem (mem_compl.mp hv)] at h2
  omega

theorem exact_congr {K L : Finset V → Prop} {k : ℕ} (h : ∀ T, K T ↔ L T) (hK : Exact K k) :
    Exact L k := by
  have : K = L := funext fun T => propext (h T)
  rwa [← this]

/-- A family closed under inserting a fixed element `v` is exact at every size. -/
theorem exact_of_cone {K : Finset V → Prop} (v : V) (hv : ∀ T, K T → K (insert v T)) (k : ℕ) :
    Exact K k := by
  intro c hc hbd
  refine ⟨fun U => if v ∈ U then c (U.erase v) else 0, ?_, ?_⟩
  · intro U hU
    by_cases hvU : v ∈ U
    · simp only [hvU, ite_true] at hU
      obtain ⟨h1, h2⟩ := hc _ hU
      have := hv _ h1
      rw [Finset.insert_erase hvU] at this
      refine ⟨this, ?_⟩
      rw [Finset.card_erase_of_mem hvU] at h2
      have := Finset.card_pos.mpr ⟨v, hvU⟩
      omega
    · simp [hvU] at hU
  · funext T
    by_cases hvT : v ∈ T
    · have h0 : bd c (T.erase v) = 0 := by rw [hbd]; rfl
      unfold bd at h0 ⊢
      have hc' : (T.erase v)ᶜ = insert v Tᶜ := by
        ext x
        simp only [mem_compl, mem_erase, mem_insert]
        by_cases hx : x = v
        · simp [hx]
        · simp [hx]
      rw [hc', Finset.sum_insert (by simpa using hvT), Finset.insert_erase hvT] at h0
      have h2 : ∑ u ∈ Tᶜ, (if v ∈ insert u T then c ((insert u T).erase v) else 0)
          = ∑ u ∈ Tᶜ, c (insert u (T.erase v)) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        have huv : u ≠ v := fun h => (mem_compl.mp hu) (h ▸ hvT)
        rw [Finset.erase_insert_of_ne huv]
        simp [hvT]
      rw [h2]
      have h3 := zmod2_add_self (c T)
      linear_combination h0 - h3
    · unfold bd
      rw [Finset.sum_eq_single v]
      · simp [hvT]
      · intro u _ huv
        have : v ∉ insert u T := by
          simp only [mem_insert, not_or]
          exact ⟨fun h => huv h.symm, hvT⟩
        simp [this]
      · intro h
        exact absurd (mem_compl.mpr hvT) h

/-- A family with a one-element member is exact at size zero. -/
theorem exact_zero_of_vertex {K : Finset V → Prop} (v : V) (hv : K {v}) : Exact K 0 := by
  intro c hc _
  refine ⟨fun U => if U = {v} then c ∅ else 0, ?_, ?_⟩
  · intro U hU
    by_cases h : U = {v}
    · subst h
      exact ⟨hv, by simp⟩
    · simp [h] at hU
  · funext T
    by_cases hT : T = ∅
    · subst hT
      unfold bd
      rw [Finset.sum_eq_single v]
      · simp
      · intro u _ huv
        have : ({u} : Finset V) ≠ {v} := fun h => huv (Finset.singleton_injective h)
        simp [this]
      · intro h
        simp at h
    · have hcT : c T = 0 := by
        by_contra h
        exact hT (Finset.card_eq_zero.mp (hc T h).2)
      rw [hcT]
      unfold bd
      refine Finset.sum_eq_zero fun u hu => ?_
      have : insert u T ≠ {v} := by
        intro h
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hT
        have h1 : x ∈ insert u T := mem_insert_of_mem hx
        have h2 : u ∈ insert u T := mem_insert_self u T
        rw [h] at h1 h2
        rw [mem_singleton] at h1 h2
        exact (mem_compl.mp hu) (h2 ▸ h1 ▸ hx)
      simp [this]

/-- Two-piece gluing: exactness of the pieces and of their intersection one size lower. -/
theorem exact_union {A B : Finset V → Prop} (hA : DownClosed A) (hB : DownClosed B) {k : ℕ}
    (hAB : Exact (fun T => A T ∧ B T) k) (hAe : Exact A (k + 1)) (hBe : Exact B (k + 1)) :
    Exact (fun T => A T ∨ B T) (k + 1) := by
  classical
  intro c hc hbd
  set cA : Finset V → ZMod 2 := fun T => if A T then c T else 0 with hcA
  set cB : Finset V → ZMod 2 := fun T => if A T then 0 else c T with hcB
  have hsum : c = cA + cB := by
    funext T
    by_cases h : A T <;> simp [hcA, hcB, h]
  have hchA : IsChain A (k + 1) cA := by
    intro T hT
    by_cases h : A T
    · simp only [hcA, h, ite_true] at hT
      exact ⟨h, (hc T hT).2⟩
    · simp [hcA, h] at hT
  have hchB : IsChain B (k + 1) cB := by
    intro T hT
    by_cases h : A T
    · simp [hcB, h] at hT
    · simp only [hcB, h, ite_false] at hT
      obtain ⟨h1, h2⟩ := hc T hT
      exact ⟨h1.resolve_left h, h2⟩
  have hbdeq : bd cB = bd cA := by
    have h1 : bd cA + bd cB = 0 := by rw [← bd_add, ← hsum, hbd]
    funext T
    have h2 := congrFun h1 T
    have h3 := zmod2_add_self (bd cA T)
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    linear_combination h2 - h3
  have hche : IsChain (fun T => A T ∧ B T) k (bd cA) := by
    intro T hT
    have h1 := IsChain.bd hA hchA T hT
    have h2 := IsChain.bd hB hchB T (by rw [hbdeq]; exact hT)
    exact ⟨⟨h1.1, h2.1⟩, h1.2⟩
  obtain ⟨f, hf, hbf⟩ := hAB (bd cA) hche (bd_bd cA)
  have hself : ∀ x : Finset V → ZMod 2, x + x = 0 := fun x => by
    funext T
    exact zmod2_add_self (x T)
  obtain ⟨gA, hgA, hbgA⟩ := hAe (cA + f) (hchA.add (hf.mono fun T h => h.1))
    (by rw [bd_add, hbf]; exact hself _)
  obtain ⟨gB, hgB, hbgB⟩ := hBe (cB + f) (hchB.add (hf.mono fun T h => h.2))
    (by rw [bd_add, hbf, hbdeq]; exact hself _)
  refine ⟨gA + gB, (hgA.mono fun T h => Or.inl h).add (hgB.mono fun T h => Or.inr h), ?_⟩
  rw [bd_add, hbgA, hbgB, hsum]
  have := hself f
  calc cA + f + (cB + f) = cA + cB + (f + f) := by abel
    _ = cA + cB := by rw [this, add_zero]

end Generic

section Matching

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]

/-- Distinct cells lie in distinct rows and distinct columns. -/
def IsMatching (T : Finset (ι × κ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, (p.1 = q.1 → p = q) ∧ (p.2 = q.2 → p = q)

/-- Matchings with rows in `R` and columns in `C`. -/
def D (R : Finset ι) (C : Finset κ) (T : Finset (ι × κ)) : Prop :=
  IsMatching T ∧ ∀ p ∈ T, p.1 ∈ R ∧ p.2 ∈ C

/-- Matchings in `R × C` that leave some column of `A` unused. -/
def G (R : Finset ι) (C : Finset κ) (A : Finset κ) (T : Finset (ι × κ)) : Prop :=
  D R C T ∧ ∃ j ∈ A, ∀ p ∈ T, p.2 ≠ j

/-- Sets `T` such that adding the cell `(i, j)` for some `j ∈ B` gives a matching in `R × C`. -/
def S (R : Finset ι) (C : Finset κ) (i : ι) (B : Finset κ) (T : Finset (ι × κ)) : Prop :=
  ∃ j ∈ B, D R C (insert (i, j) T)

variable {R : Finset ι} {C A B : Finset κ} {i : ι} {j : κ} {T : Finset (ι × κ)}

theorem D_down : DownClosed (D R C) := fun _ _ h hT =>
  ⟨fun p hp q hq => hT.1 p (h hp) q (h hq), fun p hp => hT.2 p (h hp)⟩

theorem G_down : DownClosed (G R C A) := fun _ _ h hT => by
  obtain ⟨hD, j, hj, hfree⟩ := hT
  exact ⟨D_down _ _ h hD, j, hj, fun p hp => hfree p (h hp)⟩

theorem S_down : DownClosed (S R C i B) := fun _ _ h hT => by
  obtain ⟨j, hj, hD⟩ := hT
  exact ⟨j, hj, D_down _ _ (insert_subset_insert _ h) hD⟩

theorem D_empty : D R C (∅ : Finset (ι × κ)) :=
  ⟨fun p hp => absurd hp (notMem_empty p), fun p hp => absurd hp (notMem_empty p)⟩

theorem D_insert (hT : D R C T) (hi : i ∈ R) (hj : j ∈ C) (hrow : ∀ p ∈ T, p.1 ≠ i)
    (hcol : ∀ p ∈ T, p.2 ≠ j) : D R C (insert (i, j) T) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => absurd h.symm (hrow q hq), fun h => absurd h.symm (hcol q hq)⟩
    · exact ⟨fun h => absurd h (hrow p hp), fun h => absurd h (hcol p hp)⟩
    · exact hT.1 p hp q hq
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact ⟨hi, hj⟩
    · exact hT.2 p hp

theorem D_insert_free (h : D R C (insert (i, j) T)) (hn : (i, j) ∉ T) :
    (∀ p ∈ T, p.1 ≠ i) ∧ (∀ p ∈ T, p.2 ≠ j) := by
  refine ⟨fun p hp hpi => ?_, fun p hp hpj => ?_⟩
  · have := (h.1 p (mem_insert_of_mem hp) (i, j) (mem_insert_self _ _)).1 hpi
    exact hn (this ▸ hp)
  · have := (h.1 p (mem_insert_of_mem hp) (i, j) (mem_insert_self _ _)).2 hpj
    exact hn (this ▸ hp)

theorem D_singleton (hi : i ∈ R) (hj : j ∈ C) : D R C {(i, j)} := by
  have := D_insert (T := ∅) (D_empty (R := R) (C := C)) hi hj
    (fun p hp => absurd hp (notMem_empty p)) (fun p hp => absurd hp (notMem_empty p))
  simpa using this

theorem G_singleton : G R C {j} T ↔ D R (C.erase j) T := by
  constructor
  · rintro ⟨hD, j', hj', hfree⟩
    rw [mem_singleton] at hj'
    subst hj'
    exact ⟨hD.1, fun p hp => ⟨(hD.2 p hp).1, mem_erase.mpr ⟨hfree p hp, (hD.2 p hp).2⟩⟩⟩
  · intro hD
    exact ⟨⟨hD.1, fun p hp => ⟨(hD.2 p hp).1, (mem_erase.mp (hD.2 p hp).2).2⟩⟩, j,
      mem_singleton_self j, fun p hp => (mem_erase.mp (hD.2 p hp).2).1⟩

theorem G_insert : G R C (insert j A) T ↔ G R C A T ∨ G R C {j} T := by
  constructor
  · rintro ⟨hD, j', hj', hfree⟩
    rcases mem_insert.mp hj' with rfl | h
    · exact Or.inr ⟨hD, j', mem_singleton_self _, hfree⟩
    · exact Or.inl ⟨hD, j', h, hfree⟩
  · rintro (⟨hD, j', hj', hfree⟩ | ⟨hD, j', hj', hfree⟩)
    · exact ⟨hD, j', mem_insert_of_mem hj', hfree⟩
    · rw [mem_singleton] at hj'
      subst hj'
      exact ⟨hD, j', mem_insert_self _ _, hfree⟩

theorem G_inter : (G R C A T ∧ G R C {j} T) ↔ G R (C.erase j) A T := by
  constructor
  · rintro ⟨⟨_, j', hj', hfree⟩, h2⟩
    exact ⟨G_singleton.mp h2, j', hj', hfree⟩
  · rintro ⟨hD, j', hj', hfree⟩
    have h2 : G R C {j} T := G_singleton.mpr hD
    exact ⟨⟨h2.1, j', hj', hfree⟩, h2⟩

theorem S_insert : S R C i (insert j B) T ↔ S R C i B T ∨ S R C i {j} T := by
  constructor
  · rintro ⟨j', hj', hD⟩
    rcases mem_insert.mp hj' with rfl | h
    · exact Or.inr ⟨j', mem_singleton_self _, hD⟩
    · exact Or.inl ⟨j', h, hD⟩
  · rintro (⟨j', hj', hD⟩ | ⟨j', hj', hD⟩)
    · exact ⟨j', mem_insert_of_mem hj', hD⟩
    · rw [mem_singleton] at hj'
      subst hj'
      exact ⟨j', mem_insert_self _ _, hD⟩

theorem S_cone (h : S R C i {j} T) : S R C i {j} (insert (i, j) T) := by
  obtain ⟨j', hj', hD⟩ := h
  rw [mem_singleton] at hj'
  subst hj'
  exact ⟨j', mem_singleton_self _, by rwa [Finset.insert_idem]⟩

theorem S_inter (hi : i ∈ R) (hj : j ∈ C) (hB : B ⊆ C) (hjB : j ∉ B) :
    (S R C i B T ∧ S R C i {j} T) ↔ G (R.erase i) (C.erase j) B T := by
  constructor
  · rintro ⟨⟨j', hj', h1⟩, ⟨j'', hj'', h2⟩⟩
    rw [mem_singleton] at hj''
    subst hj''
    have hne : j' ≠ j'' := fun h => hjB (h ▸ hj')
    have hn1 : (i, j') ∉ T := by
      intro hmem
      have := (h2.1 (i, j') (mem_insert_of_mem hmem) (i, j'') (mem_insert_self _ _)).1 rfl
      exact hne (congrArg Prod.snd this)
    have hn2 : (i, j'') ∉ T := by
      intro hmem
      have := (h1.1 (i, j'') (mem_insert_of_mem hmem) (i, j') (mem_insert_self _ _)).1 rfl
      exact hne (congrArg Prod.snd this).symm
    obtain ⟨hr, hc1⟩ := D_insert_free h1 hn1
    obtain ⟨_, hc2⟩ := D_insert_free h2 hn2
    have hDT : D R C T := D_down _ _ (subset_insert _ _) h1
    exact ⟨⟨hDT.1, fun p hp => ⟨mem_erase.mpr ⟨hr p hp, (hDT.2 p hp).1⟩,
      mem_erase.mpr ⟨hc2 p hp, (hDT.2 p hp).2⟩⟩⟩, j', hj', hc1⟩
  · rintro ⟨hD, j', hj', hfree⟩
    have hDT : D R C T :=
      ⟨hD.1, fun p hp => ⟨(mem_erase.mp (hD.2 p hp).1).2, (mem_erase.mp (hD.2 p hp).2).2⟩⟩
    have hr : ∀ p ∈ T, p.1 ≠ i := fun p hp => (mem_erase.mp (hD.2 p hp).1).1
    have hc : ∀ p ∈ T, p.2 ≠ j := fun p hp => (mem_erase.mp (hD.2 p hp).2).1
    exact ⟨⟨j', hj', D_insert hDT hi (hB hj') hr hfree⟩,
      ⟨j, mem_singleton_self _, D_insert hDT hi hj hr hc⟩⟩

theorem IsMatching.card_image_fst (h : IsMatching T) : (T.image Prod.fst).card = T.card :=
  Finset.card_image_of_injOn fun p hp q hq hpq => (h p hp q hq).1 hpq

theorem IsMatching.card_image_snd (h : IsMatching T) : (T.image Prod.snd).card = T.card :=
  Finset.card_image_of_injOn fun p hp q hq hpq => (h p hp q hq).2 hpq

theorem D_iff_S (hi : i ∈ R) (hcard : R.card ≤ C.card) : D R C T ↔ S R C i C T := by
  constructor
  · intro hD
    by_cases h : ∃ p ∈ T, p.1 = i
    · obtain ⟨p, hp, hpi⟩ := h
      refine ⟨p.2, (hD.2 p hp).2, ?_⟩
      have : (i, p.2) = p := by rw [← hpi]
      rw [this, insert_eq_of_mem hp]
      exact hD
    · have h : ∀ p ∈ T, p.1 ≠ i := fun p hp hpi => h ⟨p, hp, hpi⟩
      have h1 : T.image Prod.fst ⊆ R.erase i := by
        intro r hr
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
        exact mem_erase.mpr ⟨h p hp, (hD.2 p hp).1⟩
      have h2 := Finset.card_le_card h1
      rw [hD.1.card_image_fst, Finset.card_erase_of_mem hi] at h2
      have h3 : 0 < R.card := Finset.card_pos.mpr ⟨i, hi⟩
      have h4 : (T.image Prod.snd).card < C.card := by
        rw [hD.1.card_image_snd]
        omega
      obtain ⟨j, hjC, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card h4
      exact ⟨j, hjC, D_insert hD hi hjC h fun p hp hpj => hj (mem_image.mpr ⟨p, hp, hpj⟩)⟩
  · rintro ⟨j, _, hD⟩
    exact D_down _ _ (subset_insert _ _) hD

theorem exact_D_zero (R : Finset ι) (C : Finset κ) (hR : 1 ≤ R.card) (hC : R.card ≤ C.card) :
    Exact (D R C) 0 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hR
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le hR hC)
  exact exact_zero_of_vertex (i, j) (D_singleton hi hj)

theorem exact_G_zero (R : Finset ι) (C A : Finset κ) (hA : A.Nonempty) (hR : 1 ≤ R.card)
    (hC : R.card + 1 ≤ C.card) : Exact (G R C A) 0 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hR
  obtain ⟨a, ha⟩ := hA
  have h1 : 0 < (C.erase a).card := by
    have := Finset.pred_card_le_card_erase (s := C) (a := a)
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp h1
  obtain ⟨hja, hjC⟩ := mem_erase.mp hj
  refine exact_zero_of_vertex (i, j) ⟨D_singleton hi hjC, a, ha, fun p hp => ?_⟩
  rw [mem_singleton.mp hp]
  exact hja

theorem exact_S_succ (k : ℕ)
    (hG : ∀ (R : Finset ι) (C A : Finset κ), A.Nonempty → k + 1 ≤ R.card →
      R.card + k + 1 ≤ C.card → Exact (G R C A) k)
    (R : Finset ι) (C : Finset κ) (i : ι) (hi : i ∈ R) (hR : k + 2 ≤ R.card)
    (hC : R.card + (k + 1) ≤ C.card) (B : Finset κ) (hBne : B.Nonempty) :
    B ⊆ C → Exact (S R C i B) (k + 1) := by
  induction hBne using Finset.Nonempty.cons_induction with
  | singleton j => exact fun _ => exact_of_cone (i, j) (fun T h => S_cone h) (k + 1)
  | cons j B hjB hBne ih =>
    intro hsub
    rw [Finset.cons_eq_insert] at hsub ⊢
    have hjC : j ∈ C := hsub (mem_insert_self _ _)
    have hBC : B ⊆ C := fun x hx => hsub (mem_insert_of_mem hx)
    have hRe : (R.erase i).card = R.card - 1 := Finset.card_erase_of_mem hi
    have hCe : (C.erase j).card = C.card - 1 := Finset.card_erase_of_mem hjC
    refine exact_congr (fun T => S_insert.symm) (exact_union S_down S_down ?_ (ih hBC)
      (exact_of_cone (i, j) (fun T h => S_cone h) (k + 1)))
    exact exact_congr (fun T => (S_inter hi hjC hBC hjB).symm)
      (hG (R.erase i) (C.erase j) B hBne (by omega) (by omega))

theorem exact_D_succ (k : ℕ)
    (hG : ∀ (R : Finset ι) (C A : Finset κ), A.Nonempty → k + 1 ≤ R.card →
      R.card + k + 1 ≤ C.card → Exact (G R C A) k)
    (R : Finset ι) (C : Finset κ) (hR : k + 2 ≤ R.card) (hC : R.card + (k + 1) ≤ C.card) :
    Exact (D R C) (k + 1) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  exact exact_congr (fun T => (D_iff_S hi (by omega)).symm)
    (exact_S_succ k hG R C i hi hR hC C hCne (Finset.Subset.refl C))

theorem exact_G_succ (k : ℕ)
    (hD : ∀ (R : Finset ι) (C : Finset κ), k + 2 ≤ R.card → R.card + (k + 1) ≤ C.card →
      Exact (D R C) (k + 1))
    (hG : ∀ (R : Finset ι) (C A : Finset κ), A.Nonempty → k + 1 ≤ R.card →
      R.card + k + 1 ≤ C.card → Exact (G R C A) k)
    (R : Finset ι) (C : Finset κ) (hR : k + 2 ≤ R.card) (hC : R.card + (k + 1) + 1 ≤ C.card)
    (A : Finset κ) (hA : A.Nonempty) : Exact (G R C A) (k + 1) := by
  have hCe : ∀ j, C.card - 1 ≤ (C.erase j).card := fun j => Finset.pred_card_le_card_erase
  have hone : ∀ j, Exact (G R C {j}) (k + 1) := fun j =>
    exact_congr (fun T => G_singleton.symm) (hD R (C.erase j) hR (by have := hCe j; omega))
  induction hA using Finset.Nonempty.cons_induction with
  | singleton j => exact hone j
  | cons j A hjA hAne ih =>
    rw [Finset.cons_eq_insert]
    refine exact_congr (fun T => G_insert.symm) (exact_union G_down G_down ?_ ih (hone j))
    exact exact_congr (fun T => G_inter.symm)
      (hG R (C.erase j) A hAne (by omega) (by have := hCe j; omega))

/-- Joint induction on the size `k`. -/
theorem exact_D_G (k : ℕ) :
    (∀ (R : Finset ι) (C : Finset κ), k + 1 ≤ R.card → R.card + k ≤ C.card → Exact (D R C) k) ∧
    (∀ (R : Finset ι) (C A : Finset κ), A.Nonempty → k + 1 ≤ R.card →
      R.card + k + 1 ≤ C.card → Exact (G R C A) k) := by
  induction k with
  | zero =>
    exact ⟨fun R C hR hC => exact_D_zero R C (by omega) (by omega),
      fun R C A hA hR hC => exact_G_zero R C A hA (by omega) (by omega)⟩
  | succ k ih =>
    have hD := fun R C hR hC => exact_D_succ k ih.2 R C hR hC
    exact ⟨hD, fun R C A hA hR hC => exact_G_succ k hD ih.2 R C hR hC A hA⟩

/-- The filling statement: on a board with `|R| + k ≤ |C|` and `k + 1 ≤ |R|`, every function on
`k`-cell matchings whose boundary vanishes is the boundary of a function on `(k+1)`-cell
matchings. -/
theorem exact_D (k : ℕ) (R : Finset ι) (C : Finset κ) (hR : k + 1 ≤ R.card)
    (hC : R.card + k ≤ C.card) : Exact (D R C) k :=
  (exact_D_G k).1 R C hR hC

end Matching

section Extension

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]

/-- The columns not used by `T`. -/
def freeCols (T : Finset (ι × κ)) : Finset κ := univ.filter fun j => ∀ p ∈ T, p.2 ≠ j

/-- `z` satisfies the missing-row equations at every matching with fewer than `k` cells. -/
def Consistent (k : ℕ) (z : Finset (ι × κ) → ZMod 2) : Prop :=
  ∀ T, IsMatching T → T.card < k → ∀ i, (∀ p ∈ T, p.1 ≠ i) →
    z T = ∑ j ∈ freeCols T, z (insert (i, j) T)

theorem mem_freeCols {T : Finset (ι × κ)} {j : κ} : j ∈ freeCols T ↔ ∀ p ∈ T, p.2 ≠ j := by
  simp [freeCols]

/-- The boundary at a matching `T` of a function supported on matchings with rows in `S`:
only cells in an unused row of `S` and an unused column contribute. -/
theorem bd_rows {S : Finset ι} {g : Finset (ι × κ) → ZMod 2} {T : Finset (ι × κ)}
    (hg : ∀ U, g U ≠ 0 → D S (univ : Finset κ) U) :
    bd g T = ∑ r ∈ S \ T.image Prod.fst, ∑ j ∈ freeCols T, g (insert (r, j) T) := by
  rw [← Finset.sum_product (s := S \ T.image Prod.fst) (t := freeCols T)
    (f := fun v => g (insert v T))]
  unfold bd
  symm
  refine Finset.sum_subset ?_ ?_
  · intro v hv
    rw [mem_product, mem_sdiff] at hv
    rw [mem_compl]
    exact fun hvT => hv.1.2 (mem_image_of_mem _ hvT)
  · intro v hv hnot
    by_contra hne
    have hD := hg _ hne
    obtain ⟨hr, hc⟩ := D_insert_free (i := v.1) (j := v.2) hD (mem_compl.mp hv)
    apply hnot
    rw [mem_product, mem_sdiff]
    refine ⟨⟨(hD.2 v (mem_insert_self _ _)).1, fun hmem => ?_⟩, mem_freeCols.mpr hc⟩
    obtain ⟨p, hp, hpv⟩ := mem_image.mp hmem
    exact hr p hp hpv

/-- Extension of consistent families: with at least `2 * k + 1` columns, every `k`-consistent
family of values in `ZMod 2` agrees on all sets with at most `k` cells with a
`(k + 1)`-consistent family. The number of rows is arbitrary. -/
theorem consistent_extend (k : ℕ) (hN : 2 * k + 1 ≤ Fintype.card κ)
    (z : Finset (ι × κ) → ZMod 2) (hz : Consistent k z) :
    ∃ z' : Finset (ι × κ) → ZMod 2, Consistent (k + 1) z' ∧ ∀ T, T.card ≤ k → z' T = z T := by
  classical
  set cS : Finset ι → Finset (ι × κ) → ZMod 2 := fun S T =>
    if D S (univ : Finset κ) T ∧ T.card = k then z T else 0 with hcS
  have hchain : ∀ S, IsChain (D S (univ : Finset κ)) k (cS S) := by
    intro S T hT
    by_cases h : D S (univ : Finset κ) T ∧ T.card = k
    · exact h
    · simp [hcS, h] at hT
  have hcycle : ∀ S : Finset ι, S.card = k + 1 → bd (cS S) = 0 := by
    intro S hS
    funext T
    by_cases h : D S (univ : Finset κ) T ∧ T.card + 1 = k
    · obtain ⟨hD, hcard⟩ := h
      rw [bd_rows (fun U hU => ((hchain S) U hU).1)]
      have hinner : ∀ r ∈ S \ T.image Prod.fst,
          ∑ j ∈ freeCols T, cS S (insert (r, j) T) = z T := by
        intro r hr
        rw [mem_sdiff] at hr
        have hrow : ∀ p ∈ T, p.1 ≠ r := fun p hp hpr => hr.2 (mem_image.mpr ⟨p, hp, hpr⟩)
        rw [hz T hD.1 (by omega) r hrow]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hcol := mem_freeCols.mp hj
        have hnot : (r, j) ∉ T := fun hmem => hcol _ hmem rfl
        have h1 : D S (univ : Finset κ) (insert (r, j) T) :=
          D_insert hD hr.1 (mem_univ j) hrow hcol
        have h2 : (insert (r, j) T).card = k := by
          rw [Finset.card_insert_of_notMem hnot]; exact hcard
        simp [hcS, h1, h2]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const]
      have hsub : T.image Prod.fst ⊆ S := by
        intro r hr
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
        exact (hD.2 p hp).1
      have hc2 : (S \ T.image Prod.fst).card = 2 := by
        rw [Finset.card_sdiff_of_subset hsub, hD.1.card_image_fst]
        omega
      rw [hc2, Pi.zero_apply, two_nsmul]
      exact zmod2_add_self _
    · unfold bd
      rw [Pi.zero_apply]
      refine Finset.sum_eq_zero fun v hv => ?_
      by_contra hne
      obtain ⟨h1, h2⟩ := hchain S _ hne
      rw [Finset.card_insert_of_notMem (mem_compl.mp hv)] at h2
      exact h ⟨D_down _ _ (subset_insert _ _) h1, h2⟩
  have key : ∀ S : Finset ι, ∃ g : Finset (ι × κ) → ZMod 2, S.card = k + 1 →
      IsChain (D S (univ : Finset κ)) (k + 1) g ∧ bd g = cS S := by
    intro S
    by_cases hS : S.card = k + 1
    · obtain ⟨g, hg⟩ := exact_D k S (univ : Finset κ) (by omega)
        (by rw [Finset.card_univ]; omega) (cS S) (hchain S) (hcycle S hS)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose y hy using key
  refine ⟨fun T => if T.card ≤ k then z T else y (T.image Prod.fst) T, ?_, ?_⟩
  · intro T hT hcard i hrow
    have hins : ∀ j ∈ freeCols T, (insert (i, j) T).card = T.card + 1 := by
      intro j hj
      exact Finset.card_insert_of_notMem fun hmem => mem_freeCols.mp hj _ hmem rfl
    have hTk : T.card ≤ k := by omega
    simp only [hTk, ite_true]
    rcases Nat.lt_or_ge T.card k with hlt | hge
    · rw [hz T hT hlt i hrow]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : (insert (i, j) T).card ≤ k := by rw [hins j hj]; omega
      simp [this]
    · have hTcard : T.card = k := by omega
      set S := insert i (T.image Prod.fst) with hSdef
      have hiS : i ∉ T.image Prod.fst := by
        intro hmem
        obtain ⟨p, hp, hpi⟩ := mem_image.mp hmem
        exact hrow p hp hpi
      have hScard : S.card = k + 1 := by
        rw [hSdef, Finset.card_insert_of_notMem hiS, hT.card_image_fst, hTcard]
      obtain ⟨hych, hybd⟩ := hy S hScard
      have hDT : D S (univ : Finset κ) T :=
        ⟨hT, fun p hp => ⟨mem_insert_of_mem (mem_image_of_mem _ hp), mem_univ _⟩⟩
      have h1 : bd (y S) T = z T := by
        rw [hybd]
        simp [hcS, hDT, hTcard]
      rw [bd_rows (fun U hU => (hych U hU).1)] at h1
      have h2 : S \ T.image Prod.fst = {i} := by
        ext r
        simp only [hSdef, mem_sdiff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨h | h, hn⟩
          · exact h
          · exact absurd h hn
        · rintro rfl
          exact ⟨Or.inl rfl, hiS⟩
      rw [h2, Finset.sum_singleton] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬ (insert (i, j) T).card ≤ k := by rw [hins j hj]; omega
      simp only [this, ite_false]
      rw [Finset.image_insert]
  · intro T hT
    simp [hT]

/-- The board with `m` rows and `N` columns, `2 * k + 1 ≤ N`, any `m`. -/
theorem consistent_extend_fin (m N k : ℕ) (hN : 2 * k + 1 ≤ N)
    (z : Finset (Fin m × Fin N) → ZMod 2) (hz : Consistent k z) :
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2,
      Consistent (k + 1) z' ∧ ∀ T, T.card ≤ k → z' T = z T :=
  consistent_extend k (by simpa using hN) z hz

end Extension

end PEqualNP.ProofComplexity.Helpers.MomentExt
