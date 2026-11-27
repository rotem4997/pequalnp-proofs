import PEqualNP.Search.Helpers.Tree.LOF

/-!
# Helpers for L-lib-103: counting over the cube of free pigeons

Pigeons `ι`, `l` bits per hole. For a set `T` of touched pigeons and a point `x`, the cube
`Om x T` is the set of points that agree with `x` on the bits of the pigeons of `T` (every
other bit is free). An equation touches the free pigeon `i` if it has a nonzero coefficient on
some bit of `i`; `kT T e` counts those pigeons (pigeon density).

* `half_bound` (C1): an equation that touches a free pigeon holds on at most half the cube.
* `dense_bound` (C2): an equation touching at least `128 K^2` free pigeons holds on at most a
  `1/(4K)` part of the cube (from `lof`).
* `cube_small` (C3): fixing the hole of a free pigeon as a function of the other bits leaves a
  `2^(-l)` part of the cube.
* `collision_bound` (C4): the points of the cube where two pigeons of `T2 ⊇ T` share a hole are
  at most a `|T2|^2 / 2^l` part, when `x` is injective on `T`.
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.Search

open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {l : ℕ}

/-- The free pigeons (outside `T`) on which `e` has a nonzero coefficient. -/
noncomputable def touchP (T : Finset ι) (e : QEq (ι × Fin l)) : Finset ι :=
  (Finset.univ \ T).filter fun i => ∃ b, e.1 (i, b) ≠ 0

/-- The number of free pigeons `e` touches. -/
noncomputable def kT (T : Finset ι) (e : QEq (ι × Fin l)) : ℕ := (touchP T e).card

/-- The pigeons of `T` sit in different holes at `y`. -/
def Inj (T : Finset ι) (y : ι × Fin l → Bool) : Prop :=
  ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → hole y i ≠ hole y i'

/-- The cube of points agreeing with `x` on the bits of the pigeons of `T`. -/
noncomputable def Om (x : ι × Fin l → Bool) (T : Finset ι) : Finset (ι × Fin l → Bool) :=
  Dom x (Finset.univ \ T) (fun _ => Finset.univ)

theorem mem_Om {x y : ι × Fin l → Bool} {T : Finset ι} :
    y ∈ Om x T ↔ ∀ i ∈ T, ∀ b, y (i, b) = x (i, b) := by
  simp [Om, mem_Dom]

theorem self_mem_Om (x : ι × Fin l → Bool) (T : Finset ι) : x ∈ Om x T :=
  mem_Om.mpr fun _ _ _ => rfl

theorem mem_touchP {T : Finset ι} {e : QEq (ι × Fin l)} {i : ι} :
    i ∈ touchP T e ↔ i ∉ T ∧ ∃ b, e.1 (i, b) ≠ 0 := by
  simp [touchP]

theorem touchP_mono {T T' : Finset ι} (h : T ⊆ T') (e : QEq (ι × Fin l)) :
    touchP T' e ⊆ touchP T e := by
  intro i hi
  rw [mem_touchP] at hi ⊢
  exact ⟨fun h' => hi.1 (h h'), hi.2⟩

theorem kT_mono {T T' : Finset ι} (h : T ⊆ T') (e : QEq (ι × Fin l)) : kT T' e ≤ kT T e :=
  Finset.card_le_card (touchP_mono h e)

theorem coeff_zero_of_kT {T : Finset ι} {e : QEq (ι × Fin l)} (he : kT T e = 0) {i : ι}
    (hi : i ∉ T) (b : Fin l) : e.1 (i, b) = 0 := by
  by_contra hne
  have : i ∈ touchP T e := mem_touchP.mpr ⟨hi, b, hne⟩
  rw [kT, Finset.card_eq_zero] at he
  simp [he] at this

/-- Fact 0.1: an equation touching no free pigeon reads only the bits of `T`. -/
theorem closed_holds_iff {T : Finset ι} {e : QEq (ι × Fin l)} (he : kT T e = 0)
    {x y : ι × Fin l → Bool} (hy : y ∈ Om x T) : QEq.Holds y e ↔ QEq.Holds x e := by
  rw [mem_Om] at hy
  unfold QEq.Holds
  have : (∑ v, e.1 v * (if y v then 1 else 0)) = ∑ v, e.1 v * (if x v then 1 else 0) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨i, b⟩ := v
    by_cases hi : i ∈ T
    · rw [hy i hi b]
    · rw [coeff_zero_of_kT he hi b]; simp
  rw [this]

/-- Fact 0.2: injectivity on `T` reads only the bits of `T`. -/
theorem inj_of_mem_Om {T : Finset ι} {x y : ι × Fin l → Bool} (hx : Inj T x)
    (hy : y ∈ Om x T) : Inj T y := by
  rw [mem_Om] at hy
  have hh : ∀ i ∈ T, hole y i = hole x i := fun i hi => funext fun b => hy i hi b
  intro i hi i' hi' hne
  rw [hh i hi, hh i' hi']
  exact hx i hi i' hi' hne

theorem inj_mono {T T' : Finset ι} (h : T ⊆ T') {y : ι × Fin l → Bool} (hy : Inj T' y) :
    Inj T y := fun i hi i' hi' hne => hy i (h hi) i' (h hi') hne

/-- C3: fixing the hole of a free pigeon `u` as a function `g` of the bits of the other pigeons
leaves at most a `2^(-l)` part of the cube. -/
theorem cube_small (x : ι × Fin l → Bool) (T : Finset ι) (u : ι) (hu : u ∉ T)
    (g : (ι × Fin l → Bool) → (Fin l → Bool))
    (hg : ∀ y y' : ι × Fin l → Bool, (∀ v : ι × Fin l, v.1 ≠ u → y v = y' v) → g y = g y') :
    ((Om x T).filter fun y => hole y u = g y).card * 2 ^ l ≤ (Om x T).card := by
  set s := (Om x T).filter fun y => hole y u = g y
  let φ : (ι × Fin l → Bool) × (Fin l → Bool) → (ι × Fin l → Bool) :=
    fun p v => if v.1 = u then p.2 v.2 else p.1 v
  have hcard : (s ×ˢ (Finset.univ : Finset (Fin l → Bool))).card = s.card * 2 ^ l := by
    rw [Finset.card_product]; simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn φ
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    have hp1 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
    rw [mem_Om] at hp1 ⊢
    intro i hi b
    have : i ≠ u := fun h => hu (h ▸ hi)
    simp [φ, this, hp1 i hi b]
  · intro p hp p' hp' heq
    simp only [Finset.mem_coe] at hp hp'
    have hp1 := Finset.mem_filter.mp (Finset.mem_product.mp hp).1
    have hp1' := Finset.mem_filter.mp (Finset.mem_product.mp hp').1
    have h2 : p.2 = p'.2 := by
      funext b
      have := congrFun heq (u, b)
      simpa [φ] using this
    have hoff : ∀ v : ι × Fin l, v.1 ≠ u → p.1 v = p'.1 v := by
      intro v hv
      have := congrFun heq v
      simpa [φ, hv] using this
    have hgg := hg p.1 p'.1 hoff
    have h1 : p.1 = p'.1 := by
      funext v
      obtain ⟨i, b⟩ := v
      by_cases hi : i = u
      · subst hi
        have a := congrFun hp1.2 b
        have a' := congrFun hp1'.2 b
        simp only [hole] at a a'
        rw [a, a', hgg]
      · exact hoff (i, b) hi
    exact Prod.ext h1 h2

/-- C1: an equation touching a free pigeon holds on at most half the cube. -/
theorem half_bound (x : ι × Fin l → Bool) (T : Finset ι) (e : QEq (ι × Fin l))
    (he : 1 ≤ kT T e) :
    2 * ((Om x T).filter fun y => QEq.Holds y e).card ≤ (Om x T).card := by
  obtain ⟨i0, hi0⟩ : (touchP T e).Nonempty := Finset.card_pos.mp he
  obtain ⟨hi0T, b0, hb0⟩ := mem_touchP.mp hi0
  set v0 : ι × Fin l := (i0, b0)
  let fl : (ι × Fin l → Bool) → (ι × Fin l → Bool) := fun y => Function.update y v0 (!y v0)
  have hsplit : ∀ z : ι × Fin l → Bool, (∑ v, e.1 v * (if z v then 1 else 0)) =
      e.1 v0 * (if z v0 then 1 else 0) +
        ∑ v ∈ Finset.univ.erase v0, e.1 v * (if z v then 1 else 0) := by
    intro z
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ v0)).symm
  have hrest : ∀ z : ι × Fin l → Bool,
      (∑ v ∈ Finset.univ.erase v0, e.1 v * (if fl z v then 1 else 0)) =
        ∑ v ∈ Finset.univ.erase v0, e.1 v * (if z v then 1 else 0) := by
    intro z
    refine Finset.sum_congr rfl fun v hv => ?_
    have : v ≠ v0 := Finset.ne_of_mem_erase hv
    simp [fl, Function.update_of_ne this]
  have hle : ((Om x T).filter fun y => QEq.Holds y e).card ≤
      ((Om x T).filter fun y => ¬ QEq.Holds y e).card := by
    apply Finset.card_le_card_of_injOn fl
    · intro y hy
      simp only [Finset.mem_coe] at hy ⊢
      obtain ⟨hyO, hyH⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [mem_Om] at hyO ⊢
        intro i hi b
        have : (i, b) ≠ v0 := fun h => by
          have h1 : i = i0 := congrArg Prod.fst h
          exact hi0T (h1 ▸ hi)
        simp [fl, Function.update_of_ne this, hyO i hi b]
      · intro hfl
        unfold QEq.Holds at hyH hfl
        rw [hsplit, hrest] at hfl
        rw [hsplit] at hyH
        have : e.1 v0 * (if fl y v0 then 1 else 0) = e.1 v0 * (if y v0 then 1 else 0) := by
          linarith
        simp only [fl, Function.update_self] at this
        cases hy0 : y v0 <;> simp [hy0] at this <;> omega
    · intro y _ y' _ h
      have h0 := congrFun h v0
      simp only [fl, Function.update_self, Bool.not_inj_iff] at h0
      funext v
      by_cases hv : v = v0
      · rw [hv, h0]
      · have := congrFun h v
        simpa [fl, Function.update_of_ne hv] using this
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Om x T) (fun y => QEq.Holds y e)
  omega

/-- C2: an equation touching at least `r ≥ 128 K^2` free pigeons holds on at most a `1/(4K)`
part of the cube. -/
theorem dense_bound (x : ι × Fin l → Bool) (T : Finset ι) (e : QEq (ι × Fin l)) (K r : ℕ)
    (hr : 128 * K ^ 2 ≤ r) (hl : 2 ≤ l) (he : r ≤ kT T e) :
    4 * K * ((Om x T).filter fun y => QEq.Holds y e).card ≤ (Om x T).card := by
  have h := lof x (Finset.univ \ T) (touchP T e) (Finset.filter_subset _ _)
    (fun _ => Finset.univ) (2 ^ l) hl (by omega) (fun i _ => by simp) e
    (fun i hi => (mem_touchP.mp hi).2)
  change ((Om x T).filter fun y => QEq.Holds y e).card ^ 2 * ((touchP T e).card + 1) ≤
    8 * (Om x T).card ^ 2 at h
  set N := ((Om x T).filter fun y => QEq.Holds y e).card
  set W := (Om x T).card
  have hk : 128 * K ^ 2 ≤ (touchP T e).card + 1 := by unfold kT at he; omega
  have h2 : 8 * (4 * K * N) ^ 2 ≤ 8 * W ^ 2 := by
    calc 8 * (4 * K * N) ^ 2 = N ^ 2 * (128 * K ^ 2) := by ring
      _ ≤ N ^ 2 * ((touchP T e).card + 1) := Nat.mul_le_mul_left _ hk
      _ ≤ _ := h
  have h3 : (4 * K * N) ^ 2 ≤ W ^ 2 := by omega
  by_contra hc
  push Not at hc
  have := Nat.pow_lt_pow_left hc (two_ne_zero)
  omega

/-- C4: the points of the cube where two pigeons of `T2 ⊇ T` share a hole, when `x` is
injective on `T`. -/
theorem collision_bound (x : ι × Fin l → Bool) (T T2 : Finset ι) (hx : Inj T x) :
    ((Om x T).filter fun y => ¬ Inj T2 y).card * 2 ^ l ≤ T2.card ^ 2 * (Om x T).card := by
  set pairs := ((T2 \ T) ×ˢ T2).filter fun p => p.1 ≠ p.2
  have hsub : ((Om x T).filter fun y => ¬ Inj T2 y) ⊆
      pairs.biUnion fun p => (Om x T).filter fun y => hole y p.1 = hole y p.2 := by
    intro y hy
    obtain ⟨hyO, hyI⟩ := Finset.mem_filter.mp hy
    have hyT := inj_of_mem_Om hx hyO
    simp only [Inj, not_forall, not_not, exists_prop] at hyI
    obtain ⟨i, hi, i', hi', hne, heq⟩ := hyI
    rw [Finset.mem_biUnion]
    by_cases hiT : i ∈ T
    · by_cases hi'T : i' ∈ T
      · exact absurd heq (hyT i hiT i' hi'T hne)
      · refine ⟨(i', i), ?_, Finset.mem_filter.mpr ⟨hyO, heq.symm⟩⟩
        simp [pairs, hi', hi'T, hi, Ne.symm hne]
    · refine ⟨(i, i'), ?_, Finset.mem_filter.mpr ⟨hyO, heq⟩⟩
      simp [pairs, hi', hiT, hi, hne]
  have hpairs : pairs.card ≤ T2.card ^ 2 := by
    calc pairs.card ≤ ((T2 \ T) ×ˢ T2).card := Finset.card_filter_le _ _
      _ = (T2 \ T).card * T2.card := Finset.card_product _ _
      _ ≤ T2.card * T2.card := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      _ = T2.card ^ 2 := by ring
  have hone : ∀ p ∈ pairs,
      ((Om x T).filter fun y => hole y p.1 = hole y p.2).card * 2 ^ l ≤ (Om x T).card := by
    intro p hp
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff] at hp
    refine cube_small x T p.1 hp.1.1.2 (fun y => hole y p.2) ?_
    intro y y' hyy
    funext b
    exact hyy (p.2, b) (Ne.symm hp.2)
  calc ((Om x T).filter fun y => ¬ Inj T2 y).card * 2 ^ l
      ≤ (pairs.biUnion fun p => (Om x T).filter fun y => hole y p.1 = hole y p.2).card * 2 ^ l :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ p ∈ pairs, ((Om x T).filter fun y => hole y p.1 = hole y p.2).card) * 2 ^ l :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ p ∈ pairs, ((Om x T).filter fun y => hole y p.1 = hole y p.2).card * 2 ^ l := by
        rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ pairs, (Om x T).card := Finset.sum_le_sum hone
    _ = pairs.card * (Om x T).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ T2.card ^ 2 * (Om x T).card := Nat.mul_le_mul_right _ hpairs

/-! ## Union bounds over lists -/

theorem card_filter_list_exists {α β : Type} (s : Finset β) (p : α → β → Prop) :
    ∀ L : List α, (s.filter fun y => ∃ d ∈ L, p d y).card ≤
      (L.map fun d => (s.filter fun y => p d y).card).sum
  | [] => by simp
  | d :: L => by
    have ih := card_filter_list_exists s p L
    have he : (s.filter fun y => ∃ d' ∈ d :: L, p d' y) =
        (s.filter fun y => p d y) ∪ (s.filter fun y => ∃ d' ∈ L, p d' y) := by
      rw [← Finset.filter_or]
      exact Finset.filter_congr fun y _ => by simp
    rw [he, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem list_sum_mul_le {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ L : List α, (∀ d ∈ L, a * f d ≤ b) → a * (L.map f).sum ≤ L.length * b
  | [] => by simp
  | d :: L => by
    intro h
    have ih := list_sum_mul_le f a b L fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    have h0 := h d List.mem_cons_self
    rw [List.map_cons, List.sum_cons, List.length_cons, mul_add, Nat.succ_mul]
    omega

/-- C2 summed over a list whose entries are closed or dense: the points of the cube where some
non-closed entry holds. -/
theorem dense_list_bound (x : ι × Fin l → Bool) (T : Finset ι) (K r : ℕ)
    (hr : 128 * K ^ 2 ≤ r) (hl : 2 ≤ l) (Φ : List (QEq (ι × Fin l)))
    (hΦ : ∀ d ∈ Φ, kT T d = 0 ∨ r ≤ kT T d) :
    4 * K * ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card ≤
      Φ.length * (Om x T).card := by
  have hU : ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card ≤
      (Φ.map fun d => ((Om x T).filter fun y => kT T d ≠ 0 ∧ QEq.Holds y d).card).sum := by
    convert card_filter_list_exists (Om x T) (fun d y => kT T d ≠ 0 ∧ QEq.Holds y d) Φ
  refine (Nat.mul_le_mul_left (4 * K) hU).trans ?_
  refine list_sum_mul_le _ _ _ Φ fun d hd => ?_
  rcases hΦ d hd with h0 | hd'
  · have : ((Om x T).filter fun y => kT T d ≠ 0 ∧ QEq.Holds y d) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun _ _ h => h.1 h0
    rw [this]; simp
  · have hsub : ((Om x T).filter fun y => kT T d ≠ 0 ∧ QEq.Holds y d) ⊆
        (Om x T).filter fun y => QEq.Holds y d :=
      fun y hy => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.2⟩
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans
      (dense_bound x T d K r hr hl hd')

/-- A filter smaller than the set misses a point. -/
theorem exists_not_of_card_lt {β : Type} (s : Finset β) (p : β → Prop) [DecidablePred p]
    (h : (s.filter p).card < s.card) : ∃ y ∈ s, ¬ p y := by
  by_contra hc
  push Not at hc
  rw [Finset.filter_true_of_mem hc] at h
  exact lt_irrefl _ h

end PEqualNP.Search.Helpers.Tree
