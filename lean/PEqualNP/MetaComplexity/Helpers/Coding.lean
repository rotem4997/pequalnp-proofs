import Mathlib

/-!
# The satisfiability coding bound and the depth 3 parity bound

Helpers for `L-meta-027` and `L-meta-028`. No project definition is used.

A set `S` of points of the cube `Fin m → Bool` has certificates of width `k` when every
non-member lies in a subcube, fixing at most `k` coordinates, that misses `S` (so `S` is the
solution set of a CNF of width `k`). If moreover no two members of `S` are neighbours, then
`S.card ≤ 2 * k * 2 ^ (m - m / (2 * k))`.

The proof orders the coordinates by a permutation `σ`. Coordinate `i` is forced at `x` under
`σ` when some certificate of the neighbour of `x` across `i` contains `i` and has all its other
coordinates before `i`. Three steps:

* `kraft`: for each order, the subcubes obtained from the members of `S` by freeing their
  forced coordinates are pairwise disjoint, so `∑ x ∈ S, 2 ^ (forced x) ≤ 2 ^ m`.
* `perm_last_count`, `forced_count`: a given coordinate of a set of at most `k` coordinates
  comes last in at least one order out of `k`, so each coordinate of a member is forced in at
  least one order out of `k`.
* `many_good_orders`, `coding_bound`: a counting step in `ℕ`. Each member has at least
  `m / (2 * k)` forced coordinates in at least one order out of `2 * k`; some order is that
  good for one member out of `2 * k`; `kraft` bounds the number of those.

The parity bound `parity_cover` follows: a set of odd points has no two neighbours, and half
of the cube is odd.
-/

namespace PEqualNP.MetaComplexity.Helpers.Coding

open Finset

section Order

variable {m : ℕ}

/-- The orders in which `i` comes after every other element of `V`. -/
def lastSet (V : Finset (Fin m)) (i : Fin m) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ : Equiv.Perm (Fin m) => ∀ j ∈ V, j ≠ i → σ j < σ i

theorem mem_lastSet {V : Finset (Fin m)} {i : Fin m} {σ : Equiv.Perm (Fin m)} :
    σ ∈ lastSet V i ↔ ∀ j ∈ V, j ≠ i → σ j < σ i := by
  simp [lastSet]

/-- An element of `V` comes last among `V` in at least one order out of `V.card`. -/
theorem perm_last_count (V : Finset (Fin m)) (i : Fin m) (hi : i ∈ V) :
    Fintype.card (Equiv.Perm (Fin m)) ≤ V.card * (lastSet V i).card := by
  have hcover : (univ : Finset (Equiv.Perm (Fin m))) ⊆ V.biUnion (lastSet V) := by
    intro σ _
    obtain ⟨i', hi', hmax⟩ := Finset.exists_max_image V (fun j => σ j) ⟨i, hi⟩
    refine Finset.mem_biUnion.mpr ⟨i', hi', mem_lastSet.mpr ?_⟩
    intro j hj hne
    exact lt_of_le_of_ne (hmax j hj) (fun h => hne (σ.injective h))
  have hle : ∀ i' ∈ V, (lastSet V i').card ≤ (lastSet V i).card := by
    intro i' hi'
    refine Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap i i') ?_ ?_
    · intro σ hσ
      have hσ' := mem_lastSet.mp (Finset.mem_coe.mp hσ)
      refine Finset.mem_coe.mpr (mem_lastSet.mpr ?_)
      intro j hj hne
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
      by_cases hji : j = i'
      · subst hji
        rw [Equiv.swap_apply_right]
        exact hσ' i hi (Ne.symm hne)
      · rw [Equiv.swap_apply_of_ne_of_ne hne hji]
        exact hσ' j hj hji
    · intro σ _ τ _ h
      exact mul_right_cancel h
  calc Fintype.card (Equiv.Perm (Fin m))
      = (univ : Finset (Equiv.Perm (Fin m))).card := Finset.card_univ.symm
    _ ≤ (V.biUnion (lastSet V)).card := Finset.card_le_card hcover
    _ ≤ ∑ i' ∈ V, (lastSet V i').card := Finset.card_biUnion_le
    _ ≤ ∑ _i' ∈ V, (lastSet V i).card := Finset.sum_le_sum hle
    _ = V.card * (lastSet V i).card := by rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- The coordinates forced at `x` under the order `σ`: those `i` for which some subcube around
the neighbour of `x` across `i`, fixing at most `k` coordinates and missing `S`, fixes `i` and
otherwise only coordinates before `i`. -/
noncomputable def forcedSet (S : Finset (Fin m → Bool)) (k : ℕ) (σ : Equiv.Perm (Fin m))
    (x : Fin m → Bool) : Finset (Fin m) :=
  univ.filter fun i => ∃ V : Finset (Fin m), i ∈ V ∧ V.card ≤ k ∧
    (∀ y : Fin m → Bool, (∀ j ∈ V, y j = Function.update x i (!x i) j) → y ∉ S) ∧
    ∀ j ∈ V, j ≠ i → σ j < σ i

theorem mem_forcedSet {S : Finset (Fin m → Bool)} {k : ℕ} {σ : Equiv.Perm (Fin m)}
    {x : Fin m → Bool} {i : Fin m} :
    i ∈ forcedSet S k σ x ↔ ∃ V : Finset (Fin m), i ∈ V ∧ V.card ≤ k ∧
      (∀ y : Fin m → Bool, (∀ j ∈ V, y j = Function.update x i (!x i) j) → y ∉ S) ∧
      ∀ j ∈ V, j ≠ i → σ j < σ i := by
  simp [forcedSet]

/-- The first coordinate at which `x` differs from a member of `S` is not forced at `x`. -/
theorem not_mem_forcedSet {S : Finset (Fin m → Bool)} {k : ℕ} {σ : Equiv.Perm (Fin m)}
    {x x' : Fin m → Bool} {i : Fin m} (hx' : x' ∈ S) (hne : x i ≠ x' i)
    (hbefore : ∀ j, σ j < σ i → x j = x' j) : i ∉ forcedSet S k σ x := by
  rw [mem_forcedSet]
  rintro ⟨V, -, -, hV, hord⟩
  refine hV x' ?_ hx'
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    cases h1 : x j <;> cases h2 : x' j <;> simp_all
  · rw [Function.update_of_ne hji]
    exact (hbefore j (hord j hj hji)).symm

/-- The point `x` with the coordinates in `T` flipped. -/
def flipOn (x : Fin m → Bool) (T : Finset (Fin m)) : Fin m → Bool :=
  fun i => if i ∈ T then !x i else x i

theorem flipOn_injective (x : Fin m → Bool) : Function.Injective (flipOn x) := by
  intro T T' h
  ext i
  have h3 := congrFun h i
  simp only [flipOn] at h3
  by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ T' <;> simp_all

/-- The Kraft inequality of the coding argument, for one order. -/
theorem kraft (S : Finset (Fin m → Bool)) (k : ℕ) (σ : Equiv.Perm (Fin m)) :
    ∑ x ∈ S, 2 ^ (forcedSet S k σ x).card ≤ 2 ^ m := by
  classical
  have hcard : ∀ x, ((forcedSet S k σ x).powerset.image (flipOn x)).card =
      2 ^ (forcedSet S k σ x).card := by
    intro x
    rw [Finset.card_image_of_injective _ (flipOn_injective x), Finset.card_powerset]
  have hdisj : (S : Set (Fin m → Bool)).PairwiseDisjoint
      (fun x => (forcedSet S k σ x).powerset.image (flipOn x)) := by
    intro x hx x' hx' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨T', hT', hTT⟩ := Finset.mem_image.mp hy'
    rw [Finset.mem_powerset] at hT hT'
    have hD : (univ.filter fun i => x i ≠ x' i).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hne
      funext i
      by_contra hi
      have hmem : i ∈ univ.filter fun i => x i ≠ x' i := by simp [hi]
      rw [hcon] at hmem
      simp at hmem
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun j => σ j) hD
    have hi' : x i ≠ x' i := (Finset.mem_filter.mp hi).2
    have hbef : ∀ j, σ j < σ i → x j = x' j := by
      intro j hj
      by_contra hcon
      exact absurd (hmin j (by simp [hcon])) (not_le.mpr hj)
    have h1 : i ∉ forcedSet S k σ x := not_mem_forcedSet hx' hi' hbef
    have h2 : i ∉ forcedSet S k σ x' :=
      not_mem_forcedSet hx (Ne.symm hi') (fun j hj => (hbef j hj).symm)
    have h3 := congrFun hTT i
    simp only [flipOn, ite_eq_right (fun h => h1 (hT h)), ite_eq_right (fun h => h2 (hT' h))] at h3
    exact hi' h3.symm
  calc ∑ x ∈ S, 2 ^ (forcedSet S k σ x).card
      = ∑ x ∈ S, ((forcedSet S k σ x).powerset.image (flipOn x)).card :=
        Finset.sum_congr rfl (fun x _ => (hcard x).symm)
    _ = (S.biUnion fun x => (forcedSet S k σ x).powerset.image (flipOn x)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (univ : Finset (Fin m → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ m := by simp

/-- Each coordinate of an isolated member is forced in at least one order out of `k`. -/
theorem forced_count (S : Finset (Fin m → Bool)) (k : ℕ)
    (hcert : ∀ x : Fin m → Bool, x ∉ S → ∃ V : Finset (Fin m), V.card ≤ k ∧
      ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ S)
    (x : Fin m → Bool) (hx : x ∈ S) (i : Fin m) (hiso : Function.update x i (!x i) ∉ S) :
    Fintype.card (Equiv.Perm (Fin m)) ≤
      k * (univ.filter fun σ : Equiv.Perm (Fin m) => i ∈ forcedSet S k σ x).card := by
  obtain ⟨V, hVk, hV⟩ := hcert _ hiso
  have hiV : i ∈ V := by
    by_contra hcon
    refine hV x (fun j hj => ?_) hx
    have hji : j ≠ i := by
      rintro rfl
      exact hcon hj
    rw [Function.update_of_ne hji]
  calc Fintype.card (Equiv.Perm (Fin m)) ≤ V.card * (lastSet V i).card := perm_last_count V i hiV
    _ ≤ k * (univ.filter fun σ : Equiv.Perm (Fin m) => i ∈ forcedSet S k σ x).card := by
        refine Nat.mul_le_mul hVk (Finset.card_le_card ?_)
        intro σ hσ
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, mem_forcedSet.mpr ⟨V, hiV, hVk, hV, mem_lastSet.mp hσ⟩⟩

/-- A member all of whose coordinates are forced in one order out of `k` has at least
`m / (2 * k)` forced coordinates in at least one order out of `2 * k`. -/
theorem many_good_orders (S : Finset (Fin m → Bool)) (k : ℕ) (hk : 0 < k) (x : Fin m → Bool)
    (h : ∀ i : Fin m, Fintype.card (Equiv.Perm (Fin m)) ≤
      k * (univ.filter fun σ : Equiv.Perm (Fin m) => i ∈ forcedSet S k σ x).card) :
    Fintype.card (Equiv.Perm (Fin m)) ≤
      2 * k * (univ.filter fun σ : Equiv.Perm (Fin m) =>
        m / (2 * k) ≤ (forcedSet S k σ x).card).card := by
  classical
  set P := Fintype.card (Equiv.Perm (Fin m)) with hP
  set t := m / (2 * k) with ht
  set G := (univ.filter fun σ : Equiv.Perm (Fin m) => t ≤ (forcedSet S k σ x).card).card with hG
  -- double counting
  have hswap : ∑ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card =
      ∑ i : Fin m, (univ.filter fun σ : Equiv.Perm (Fin m) => i ∈ forcedSet S k σ x).card := by
    have e1 : ∀ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card =
        ∑ i : Fin m, if i ∈ forcedSet S k σ x then 1 else 0 := by
      intro σ
      rw [← Finset.card_filter]
      congr 1
      ext i
      simp
    rw [Finset.sum_congr rfl (fun σ _ => e1 σ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_filter]
  have hlow : m * P ≤ k * ∑ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card := by
    rw [hswap, Finset.mul_sum]
    calc m * P = ∑ _i : Fin m, P := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => h i)
  have hF : ∀ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card ≤
      (if t ≤ (forcedSet S k σ x).card then m else 0) + t := by
    intro σ
    have hle : (forcedSet S k σ x).card ≤ m := by
      simpa using Finset.card_le_univ (forcedSet S k σ x)
    by_cases hc : t ≤ (forcedSet S k σ x).card
    · rw [ite_eq_left hc]
      exact Nat.le_add_right_of_le hle
    · rw [ite_eq_right hc]
      exact le_trans (le_of_lt (not_le.mp hc)) (Nat.le_add_left _ _)
  have hup : ∑ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card ≤ G * m + P * t := by
    calc ∑ σ : Equiv.Perm (Fin m), (forcedSet S k σ x).card
        ≤ ∑ σ : Equiv.Perm (Fin m),
            ((if t ≤ (forcedSet S k σ x).card then m else 0) + t) :=
          Finset.sum_le_sum (fun σ _ => hF σ)
      _ = G * m + P * t := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
            smul_eq_mul, smul_eq_mul, Finset.card_univ]
  have htm : t * (2 * k) ≤ m := Nat.div_mul_le_self m (2 * k)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have ht0 : t = 0 := by rw [ht, hm]; simp
    have hGP : G = P := by
      rw [hG, hP, ← Finset.card_univ]
      congr 1
      ext σ
      simp [ht0]
    rw [hGP]
    nlinarith
  · have h1 : m * P ≤ k * (G * m + P * t) := le_trans hlow (Nat.mul_le_mul_left k hup)
    have h2 : P * (t * (2 * k)) ≤ P * m := Nat.mul_le_mul_left P htm
    have h3 : m * P ≤ m * (2 * k * G) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h3 hm

/-- The satisfiability coding bound, weak integer form: a set of points of the cube with no two
neighbours, each of whose non-members is excluded by at most `k` coordinates, has at most
`2 * k * 2 ^ (m - m / (2 * k))` points. -/
theorem coding_bound (m k : ℕ) (S : Finset (Fin m → Bool)) (hk : 0 < k)
    (hcert : ∀ x : Fin m → Bool, x ∉ S → ∃ V : Finset (Fin m), V.card ≤ k ∧
      ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ S)
    (hiso : ∀ x ∈ S, ∀ i : Fin m, Function.update x i (!x i) ∉ S) :
    S.card ≤ 2 * k * 2 ^ (m - m / (2 * k)) := by
  classical
  set P := Fintype.card (Equiv.Perm (Fin m)) with hP
  set t := m / (2 * k) with ht
  have hPpos : 0 < P := Fintype.card_pos
  have hx : ∀ x ∈ S, P ≤ 2 * k * (univ.filter fun σ : Equiv.Perm (Fin m) =>
      t ≤ (forcedSet S k σ x).card).card := fun x hxS =>
    many_good_orders S k hk x (fun i => forced_count S k hcert x hxS i (hiso x hxS i))
  have hσ : ∀ σ : Equiv.Perm (Fin m),
      (S.filter fun x => t ≤ (forcedSet S k σ x).card).card ≤ 2 ^ (m - t) := by
    intro σ
    have htm : t ≤ m := Nat.div_le_self _ _
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos (by norm_num : 0 < 2) : 0 < 2 ^ t)
    calc (S.filter fun x => t ≤ (forcedSet S k σ x).card).card * 2 ^ t
        = ∑ _x ∈ S.filter fun x => t ≤ (forcedSet S k σ x).card, 2 ^ t := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ S.filter fun x => t ≤ (forcedSet S k σ x).card,
            2 ^ (forcedSet S k σ x).card :=
          Finset.sum_le_sum (fun x hxm =>
            Nat.pow_le_pow_right (by norm_num) (Finset.mem_filter.mp hxm).2)
      _ ≤ ∑ x ∈ S, 2 ^ (forcedSet S k σ x).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ 2 ^ m := kraft S k σ
      _ = 2 ^ (m - t) * 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel htm]
  have key : S.card * P ≤ 2 * k * 2 ^ (m - t) * P := by
    calc S.card * P = ∑ _x ∈ S, P := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ S, 2 * k * (univ.filter fun σ : Equiv.Perm (Fin m) =>
            t ≤ (forcedSet S k σ x).card).card := Finset.sum_le_sum hx
      _ = 2 * k * ∑ x ∈ S, ∑ σ : Equiv.Perm (Fin m),
            if t ≤ (forcedSet S k σ x).card then 1 else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.card_filter]
      _ = 2 * k * ∑ σ : Equiv.Perm (Fin m),
            (S.filter fun x => t ≤ (forcedSet S k σ x).card).card := by
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [Finset.card_filter]
      _ ≤ 2 * k * ∑ _σ : Equiv.Perm (Fin m), 2 ^ (m - t) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun σ _ => hσ σ))
      _ = 2 * k * 2 ^ (m - t) * P := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
          ring
  exact Nat.le_of_mul_le_mul_right key hPpos

end Order

section Parity

variable {m : ℕ}

/-- Flipping one coordinate changes the parity of the number of true coordinates. -/
theorem flip_parity (x : Fin m → Bool) (i : Fin m) :
    (univ.filter fun j : Fin m => Function.update x i (!x i) j = true).card % 2 ≠
      (univ.filter fun j : Fin m => x j = true).card % 2 := by
  cases h : x i
  · have he : (univ.filter fun j : Fin m => Function.update x i (!false) j = true) =
        insert i (univ.filter fun j : Fin m => x j = true) := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    have hni : i ∉ univ.filter fun j : Fin m => x j = true := by simp [h]
    rw [he, Finset.card_insert_of_notMem hni]
    omega
  · have he : (univ.filter fun j : Fin m => Function.update x i (!true) j = true) =
        (univ.filter fun j : Fin m => x j = true).erase i := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    have hi : i ∈ univ.filter fun j : Fin m => x j = true := by simp [h]
    have hpos : 0 < (univ.filter fun j : Fin m => x j = true).card := Finset.card_pos.mpr ⟨i, hi⟩
    rw [he, Finset.card_erase_of_mem hi]
    omega

theorem flip_flip (x : Fin m → Bool) (i : Fin m) :
    Function.update (Function.update x i (!x i)) i (!(Function.update x i (!x i)) i) = x := by
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [Function.update_of_ne hji]

/-- At least half of the points of a cube of positive dimension have odd weight. -/
theorem two_pow_le_odd (hm : 0 < m) :
    2 ^ m ≤ 2 * (univ.filter fun x : Fin m → Bool =>
      (univ.filter fun i : Fin m => x i = true).card % 2 = 1).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Bool)))
    (fun x : Fin m → Bool => (univ.filter fun i : Fin m => x i = true).card % 2 = 1)
  have hle : (univ.filter fun x : Fin m → Bool =>
        ¬ (univ.filter fun i : Fin m => x i = true).card % 2 = 1).card ≤
      (univ.filter fun x : Fin m → Bool =>
        (univ.filter fun i : Fin m => x i = true).card % 2 = 1).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : Fin m → Bool => Function.update x ⟨0, hm⟩ (!x ⟨0, hm⟩)) ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      have hfl := flip_parity x ⟨0, hm⟩
      have hlt := Nat.mod_lt (univ.filter fun i : Fin m => x i = true).card (by norm_num : 0 < 2)
      have hlt' := Nat.mod_lt (univ.filter fun j : Fin m =>
        Function.update x ⟨0, hm⟩ (!x ⟨0, hm⟩) j = true).card (by norm_num : 0 < 2)
      show (univ.filter fun j : Fin m =>
        Function.update x ⟨0, hm⟩ (!x ⟨0, hm⟩) j = true).card % 2 = 1
      omega
    · intro x _ y _ hxy
      have hxy' : Function.update x ⟨0, hm⟩ (!x ⟨0, hm⟩) =
          Function.update y ⟨0, hm⟩ (!y ⟨0, hm⟩) := hxy
      rw [← flip_flip x ⟨0, hm⟩, ← flip_flip y ⟨0, hm⟩, hxy']
  have hcard : (univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
  omega

/-- Parity on `m ≥ 1` bits is not a union of few sets with certificates of width `k`. -/
theorem parity_cover (m k N : ℕ) (E : Fin N → Finset (Fin m → Bool)) (hk : 0 < k) (hm : 0 < m)
    (hcert : ∀ (a : Fin N) (x : Fin m → Bool), x ∉ E a → ∃ V : Finset (Fin m), V.card ≤ k ∧
      ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ E a)
    (hpar : ∀ x : Fin m → Bool, (∃ a : Fin N, x ∈ E a) ↔
      (univ.filter fun i : Fin m => x i = true).card % 2 = 1) :
    2 ^ m ≤ N * (4 * k * 2 ^ (m - m / (2 * k))) := by
  have hE : ∀ a : Fin N, (E a).card ≤ 2 * k * 2 ^ (m - m / (2 * k)) := by
    intro a
    refine coding_bound m k (E a) hk (hcert a) ?_
    intro x hx i hcon
    have h1 := (hpar x).1 ⟨a, hx⟩
    have h2 := (hpar (Function.update x i (!x i))).1 ⟨a, hcon⟩
    exact flip_parity x i (by rw [h1, h2])
  have hsub : (univ.filter fun x : Fin m → Bool =>
      (univ.filter fun i : Fin m => x i = true).card % 2 = 1) ⊆ univ.biUnion E := by
    intro x hx
    obtain ⟨a, ha⟩ := (hpar x).2 (Finset.mem_filter.mp hx).2
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ha⟩
  have hodd : (univ.filter fun x : Fin m → Bool =>
      (univ.filter fun i : Fin m => x i = true).card % 2 = 1).card ≤
      N * (2 * k * 2 ^ (m - m / (2 * k))) := by
    calc _ ≤ (univ.biUnion E).card := Finset.card_le_card hsub
      _ ≤ ∑ a : Fin N, (E a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : Fin N, 2 * k * 2 ^ (m - m / (2 * k)) := Finset.sum_le_sum (fun a _ => hE a)
      _ = N * (2 * k * 2 ^ (m - m / (2 * k))) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have h2 := two_pow_le_odd hm
  calc 2 ^ m ≤ 2 * (N * (2 * k * 2 ^ (m - m / (2 * k)))) := le_trans h2 (Nat.mul_le_mul_left 2 hodd)
    _ = N * (4 * k * 2 ^ (m - m / (2 * k))) := by ring

end Parity

end PEqualNP.MetaComplexity.Helpers.Coding
