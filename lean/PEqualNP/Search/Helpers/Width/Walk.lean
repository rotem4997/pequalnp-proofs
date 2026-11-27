import PEqualNP.Defs
import PEqualNP.Search.Helpers.Width.LO
import PEqualNP.Search.Helpers.ResLinQ
import Mathlib.Tactic

/-!
# Helpers: a width lower bound for Res(lin) over the integers on the bit pigeonhole formula

A walk from the empty line toward the axioms keeps a point that falsifies the current line and
is injective on a closure set of pigeons. Counting over the free bits (with the
Erdos-Littlewood-Offord bound `lo_bound`) shows the walk can always continue, and an axiom
line can never be reached.
-/

namespace PEqualNP.Search.Helpers.Width

open PEqualNP.Search

/-! ## Counting over fibers of a set of resampled coordinates -/

section Fiber

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Overwrite the coordinates `t j` of `z` by `y j`. -/
noncomputable def glue {k : ℕ} (t : Fin k → V) (y : Fin k → Bool) (z : V → Bool) : V → Bool :=
  Function.extend t y z

theorem glue_apply_t {k : ℕ} {t : Fin k → V} (ht : Function.Injective t) (y : Fin k → Bool)
    (z : V → Bool) (j : Fin k) : glue t y z (t j) = y j :=
  ht.extend_apply y z j

theorem glue_apply_not {k : ℕ} (t : Fin k → V) (y : Fin k → Bool) (z : V → Bool) (v : V)
    (hv : ¬ ∃ j, t j = v) : glue t y z v = z v :=
  Function.extend_apply' y z v hv

/-- Fiber counting: if `S` is closed under resampling the coordinates of `t`, and inside
every fiber at most a `1 / M` fraction of the `2 ^ k` resamplings satisfy `H`, then at most a
`1 / M` fraction of `S` satisfies `H`. -/
theorem fiber_count {k : ℕ} (t : Fin k → V) (ht : Function.Injective t)
    (S : Finset (V → Bool)) (hS : ∀ a ∈ S, ∀ y, glue t y a ∈ S)
    (H : (V → Bool) → Prop) [DecidablePred H] (M : ℕ)
    (hM : ∀ z, M * (Finset.univ.filter fun y => H (glue t y z)).card ≤ 2 ^ k) :
    M * (S.filter H).card ≤ S.card := by
  classical
  set φ : (V → Bool) → (V → Bool) := fun a => glue t (fun _ => false) a with hφ
  have h1 := Finset.card_eq_sum_card_fiberwise (f := φ) (s := S.filter H) (t := S.image φ)
    (fun x hx => Finset.mem_image_of_mem φ (Finset.mem_filter.mp hx).1)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := φ) (s := S) (t := S.image φ)
    (fun x hx => Finset.mem_image_of_mem φ hx)
  rw [h1, h2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hz
  -- the fiber of `φ a0` inside `S ∩ H` sits in the image of the good resamplings
  have hsub : (S.filter H).filter (fun a => φ a = φ a0) ⊆
      (Finset.univ.filter fun y => H (glue t y (φ a0))).image (fun y => glue t y (φ a0)) := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨⟨_, hHa⟩, hφa⟩ := ha
    have hrec : glue t (fun j => a (t j)) (φ a0) = a := by
      funext v
      by_cases hv : ∃ j, t j = v
      · obtain ⟨j, rfl⟩ := hv
        rw [glue_apply_t ht]
      · rw [glue_apply_not t _ _ v hv, ← hφa, hφ]
        simp only
        rw [glue_apply_not t _ _ v hv]
    refine Finset.mem_image.mpr ⟨fun j => a (t j), ?_, hrec⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hrec]; exact hHa
  -- the whole fiber of `φ a0` inside `S` has `2 ^ k` points
  have hsup : (Finset.univ : Finset (Fin k → Bool)).image (fun y => glue t y (φ a0)) ⊆
      S.filter (fun a => φ a = φ a0) := by
    intro a ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ha
    have heq : glue t y (φ a0) = glue t y a0 := by
      funext v
      by_cases hv : ∃ j, t j = v
      · obtain ⟨j, rfl⟩ := hv
        rw [glue_apply_t ht, glue_apply_t ht]
      · rw [glue_apply_not t _ _ v hv, glue_apply_not t _ _ v hv, hφ]
        simp only
        rw [glue_apply_not t _ _ v hv]
    refine Finset.mem_filter.mpr ⟨heq ▸ hS a0 ha0 y, ?_⟩
    funext v
    rw [hφ]
    simp only
    by_cases hv : ∃ j, t j = v
    · obtain ⟨j, rfl⟩ := hv
      rw [glue_apply_t ht, glue_apply_t ht]
    · rw [glue_apply_not t _ _ v hv, glue_apply_not t _ _ v hv]
  have hinj : Function.Injective (fun y => glue t y (φ a0)) := by
    intro y y' h
    funext j
    have := congrFun h (t j)
    simpa only [glue_apply_t ht] using this
  have hcard : (Finset.univ : Finset (Fin k → Bool)).image (fun y => glue t y (φ a0)) =
      (Finset.univ : Finset (Fin k → Bool)).map ⟨_, hinj⟩ := by
    rw [Finset.map_eq_image]; rfl
  calc M * ((S.filter H).filter (fun a => φ a = φ a0)).card
      ≤ M * ((Finset.univ.filter fun y => H (glue t y (φ a0))).image
          (fun y => glue t y (φ a0))).card := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
    _ ≤ M * (Finset.univ.filter fun y => H (glue t y (φ a0))).card :=
          Nat.mul_le_mul_left _ Finset.card_image_le
    _ ≤ 2 ^ k := hM _
    _ = ((Finset.univ : Finset (Fin k → Bool)).image (fun y => glue t y (φ a0))).card := by
          rw [hcard, Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin]
    _ ≤ (S.filter (fun a => φ a = φ a0)).card := Finset.card_le_card hsup

/-- The value of an equation at a glued point: the base value plus the change on the
coordinates of `t`. -/
theorem sum_glue {k : ℕ} {t : Fin k → V} (ht : Function.Injective t) (c : V → ℤ)
    (y : Fin k → Bool) (z : V → Bool) :
    (∑ v, c v * (if glue t y z v then 1 else 0)) =
      (∑ v, c v * (if z v then 1 else 0)) +
      ∑ j, c (t j) * ((if y j then 1 else 0) - (if z (t j) then 1 else 0)) := by
  have hd : (∑ v, c v * (if glue t y z v then 1 else 0)) - (∑ v, c v * (if z v then 1 else 0))
      = ∑ v, c v * ((if glue t y z v then 1 else 0) - (if z v then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
  have hs : (∑ v, c v * ((if glue t y z v then (1 : ℤ) else 0) - (if z v then 1 else 0))) =
      ∑ v ∈ Finset.univ.map ⟨t, ht⟩,
        c v * ((if glue t y z v then (1 : ℤ) else 0) - (if z v then 1 else 0)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hv' : ¬ ∃ j, t j = v := by
      rintro ⟨j, rfl⟩
      exact hv (Finset.mem_map_of_mem _ (Finset.mem_univ j))
    rw [glue_apply_not t _ _ v hv']; ring
  rw [Finset.sum_map] at hs
  simp only [Function.Embedding.coeFn_mk, glue_apply_t ht] at hs
  linarith

end Fiber

/-! ## Pigeons, extensions and the counting estimates -/

section Pigeon

open scoped Classical

variable {N l : ℕ}

/-- The pigeons an equation involves: those with a nonzero coefficient on some bit. -/
noncomputable def inv (e : QEq (Fin N × Fin l)) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∃ b, e.1 (i, b) ≠ 0

/-- The extensions of `q` on the pigeons `A`: the points agreeing with `q` on their bits. -/
noncomputable def Ext (q : Fin N × Fin l → Bool) (A : Finset (Fin N)) :
    Finset (Fin N × Fin l → Bool) :=
  Finset.univ.filter fun a => ∀ i ∈ A, ∀ b, a (i, b) = q (i, b)

/-- The point `a` sends distinct pigeons of `A` to distinct holes. -/
def InjP (a : Fin N × Fin l → Bool) (A : Finset (Fin N)) : Prop :=
  ∀ i ∈ A, ∀ i' ∈ A, (∀ b, a (i, b) = a (i', b)) → i = i'

/-- The point `a` falsifies every equation of the line `L`. -/
def Fals (a : Fin N × Fin l → Bool) (L : QLine (Fin N × Fin l)) : Prop :=
  ∀ e ∈ L, ¬ QEq.Holds a e

theorem mem_Ext {q a : Fin N × Fin l → Bool} {A : Finset (Fin N)} :
    a ∈ Ext q A ↔ ∀ i ∈ A, ∀ b, a (i, b) = q (i, b) := by
  simp [Ext]

theorem self_mem_Ext (q : Fin N × Fin l → Bool) (A : Finset (Fin N)) : q ∈ Ext q A :=
  mem_Ext.mpr fun _ _ _ => rfl

theorem Ext_closed {k : ℕ} (t : Fin k → Fin N × Fin l) (q : Fin N × Fin l → Bool)
    (A : Finset (Fin N)) (hfree : ∀ j, (t j).1 ∉ A) :
    ∀ a ∈ Ext q A, ∀ y, glue t y a ∈ Ext q A := by
  intro a ha y
  rw [mem_Ext] at ha ⊢
  intro i hi b
  have hv : ¬ ∃ j, t j = (i, b) := by
    rintro ⟨j, hj⟩
    exact hfree j (by rw [hj]; exact hi)
  rw [glue_apply_not t _ _ _ hv]
  exact ha i hi b

/-- An equation involving only pigeons of `A` is constant on the extensions. -/
theorem holds_const (e : QEq (Fin N × Fin l)) (A : Finset (Fin N)) (he : inv e ⊆ A)
    (q a : Fin N × Fin l → Bool) (ha : a ∈ Ext q A) :
    QEq.Holds a e ↔ QEq.Holds q e := by
  rw [mem_Ext] at ha
  have : (∑ v, e.1 v * (if a v then 1 else 0)) = ∑ v, e.1 v * (if q v then 1 else 0) := by
    apply Finset.sum_congr rfl
    rintro ⟨i, b⟩ _
    by_cases h0 : e.1 (i, b) = 0
    · simp [h0]
    · have hi : i ∈ inv e := by simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨b, h0⟩
      rw [ha i (he hi) b]
  simp only [QEq.Holds, this]

theorem four_pow (k : ℕ) : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]

/-- The key estimate: an equation with at least `16 W ^ 2` free pigeons holds on at most a
`1 / (4 W)` fraction of the extensions. -/
theorem key_estimate (W : ℕ) (e : QEq (Fin N × Fin l)) (A : Finset (Fin N))
    (q : Fin N × Fin l → Bool) (hk : 16 * W ^ 2 ≤ (inv e \ A).card) :
    4 * W * ((Ext q A).filter (fun a => QEq.Holds a e)).card ≤ (Ext q A).card := by
  set P := inv e \ A with hP
  set k := P.card with hkdef
  have hb : ∀ p : P, ∃ b, e.1 ((p : Fin N), b) ≠ 0 := by
    intro p
    have := p.2
    simp only [hP, Finset.mem_sdiff, inv, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1
  let t : Fin k → Fin N × Fin l := fun j =>
    (((P.equivFin.symm j : P) : Fin N), (hb (P.equivFin.symm j)).choose)
  have ht : Function.Injective t := by
    intro j j' h
    have h1 := congrArg Prod.fst h
    exact P.equivFin.symm.injective (Subtype.ext h1)
  have hfree : ∀ j, (t j).1 ∉ A := by
    intro j
    have hmem : ((P.equivFin.symm j : P) : Fin N) ∈ inv e \ A := (P.equivFin.symm j).2
    exact (Finset.mem_sdiff.mp hmem).2
  have hcoef : ∀ j, e.1 (t j) ≠ 0 := fun j => (hb _).choose_spec
  apply fiber_count t ht _ (Ext_closed t q A hfree) _ (4 * W)
  intro z
  set c' : ℤ := e.2 - (∑ v, e.1 v * (if z v then 1 else 0)) +
    ∑ j, e.1 (t j) * (if z (t j) then 1 else 0) with hc'
  have hfil : (Finset.univ.filter fun y => QEq.Holds (glue t y z) e) =
      Finset.univ.filter fun y : Fin k → Bool =>
        (∑ j, e.1 (t j) * (if y j then 1 else 0)) = c' := by
    apply Finset.filter_congr
    intro y _
    simp only [QEq.Holds]
    rw [sum_glue ht]
    simp only [mul_sub, Finset.sum_sub_distrib, hc']
    constructor <;> intro h <;> linarith
  rw [hfil]
  set c := (Finset.univ.filter fun y : Fin k → Bool =>
    (∑ j, e.1 (t j) * (if y j then 1 else 0)) = c').card with hc
  have hlo : c ^ 2 * k ≤ 4 ^ k := lo_bound k (fun j => e.1 (t j)) hcoef c'
  have h2 : (4 * W * c) ^ 2 ≤ (2 ^ k) ^ 2 := by
    rw [← four_pow]
    calc (4 * W * c) ^ 2 = c ^ 2 * (16 * W ^ 2) := by ring
      _ ≤ c ^ 2 * k := Nat.mul_le_mul_left _ hk
      _ ≤ 4 ^ k := hlo
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

/-- Union bound over the equations of a line: if the line is closed for `A` and `q` falsifies
it, at most a quarter of the extensions satisfy some equation of the line. -/
theorem union_bound (W : ℕ) (hW : 0 < W) (L : QLine (Fin N × Fin l)) (hL : L.length ≤ W)
    (A : Finset (Fin N)) (hgood : ∀ e ∈ L, inv e ⊆ A ∨ 16 * W ^ 2 ≤ (inv e \ A).card)
    (q : Fin N × Fin l → Bool) (hq : Fals q L) :
    4 * ((Ext q A).filter (fun a => ¬ Fals a L)).card ≤ (Ext q A).card := by
  have hsub : (Ext q A).filter (fun a => ¬ Fals a L) ⊆
      L.toFinset.biUnion (fun e => (Ext q A).filter (fun a => QEq.Holds a e)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haE, haF⟩ := ha
    simp only [Fals, not_forall, not_not] at haF
    obtain ⟨e, he, hae⟩ := haF
    exact Finset.mem_biUnion.mpr ⟨e, List.mem_toFinset.mpr he, Finset.mem_filter.mpr ⟨haE, hae⟩⟩
  have hterm : ∀ e ∈ L.toFinset,
      4 * W * ((Ext q A).filter (fun a => QEq.Holds a e)).card ≤ (Ext q A).card := by
    intro e he
    rw [List.mem_toFinset] at he
    rcases hgood e he with hs | hb
    · have : (Ext q A).filter (fun a => QEq.Holds a e) = ∅ := by
        apply Finset.filter_false_of_mem
        intro a ha hae
        exact hq e he ((holds_const e A hs q a ha).mp hae)
      rw [this]; simp
    · exact key_estimate W e A q hb
  have h1 : 4 * W * ((Ext q A).filter (fun a => ¬ Fals a L)).card ≤ W * (Ext q A).card :=
    calc 4 * W * ((Ext q A).filter (fun a => ¬ Fals a L)).card
        ≤ 4 * W * ∑ e ∈ L.toFinset, ((Ext q A).filter (fun a => QEq.Holds a e)).card :=
          Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ e ∈ L.toFinset, 4 * W * ((Ext q A).filter (fun a => QEq.Holds a e)).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ e ∈ L.toFinset, (Ext q A).card := Finset.sum_le_sum hterm
      _ = L.toFinset.card * (Ext q A).card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ W * (Ext q A).card := Nat.mul_le_mul_right _ ((List.toFinset_card_le L).trans hL)
  have h2 : W * (4 * ((Ext q A).filter (fun a => ¬ Fals a L)).card) ≤ W * (Ext q A).card := by
    calc _ = 4 * W * ((Ext q A).filter (fun a => ¬ Fals a L)).card := by ring
      _ ≤ _ := h1
  exact Nat.le_of_mul_le_mul_left h2 hW

/-- Two distinct pigeons, the first free: they share a hole on at most a `2 ^ (-l)` fraction
of the extensions. -/
theorem pair_free (q : Fin N × Fin l → Bool) (A : Finset (Fin N)) (i i' : Fin N) (hi : i ∉ A)
    (hne : i ≠ i') :
    2 ^ l * ((Ext q A).filter (fun a => ∀ b, a (i, b) = a (i', b))).card ≤ (Ext q A).card := by
  let t : Fin l → Fin N × Fin l := fun b => (i, b)
  have ht : Function.Injective t := fun b b' h => (Prod.mk.inj h).2
  apply fiber_count t ht _ (Ext_closed t q A (fun _ => hi)) _ (2 ^ l)
  intro z
  have hone : (Finset.univ.filter fun y =>
      ∀ b, glue t y z (i, b) = glue t y z (i', b)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy y' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    funext b
    have hn : ¬ ∃ j, t j = (i', b) := by
      rintro ⟨j, hj⟩
      exact hne (congrArg Prod.fst hj)
    have e1 : y b = z (i', b) := by
      have := hy b
      rwa [show ((i, b) : Fin N × Fin l) = t b from rfl, glue_apply_t ht,
        glue_apply_not t _ _ _ hn] at this
    have e2 : y' b = z (i', b) := by
      have := hy' b
      rwa [show ((i, b) : Fin N × Fin l) = t b from rfl, glue_apply_t ht,
        glue_apply_not t _ _ _ hn] at this
    rw [e1, e2]
  calc 2 ^ l * (Finset.univ.filter fun y =>
        ∀ b, glue t y z (i, b) = glue t y z (i', b)).card ≤ 2 ^ l * 1 :=
        Nat.mul_le_mul_left _ hone
    _ = 2 ^ l := by ring

theorem pair_bound (q : Fin N × Fin l → Bool) (A : Finset (Fin N)) (i i' : Fin N)
    (h : i ∉ A ∨ i' ∉ A) (hne : i ≠ i') :
    2 ^ l * ((Ext q A).filter (fun a => ∀ b, a (i, b) = a (i', b))).card ≤ (Ext q A).card := by
  rcases h with h | h
  · exact pair_free q A i i' h hne
  · have := pair_free q A i' i h (Ne.symm hne)
    have heq : (Ext q A).filter (fun a => ∀ b, a (i, b) = a (i', b)) =
        (Ext q A).filter (fun a => ∀ b, a (i', b) = a (i, b)) :=
      Finset.filter_congr (fun a _ => ⟨fun h b => (h b).symm, fun h b => (h b).symm⟩)
    rw [heq]; exact this

/-- The extensions of an injective `q` on `A` that are not injective on `A'`: at most a
`|A'| ^ 2 / 2 ^ l` fraction. -/
theorem bad_inj (q : Fin N × Fin l → Bool) (A A' : Finset (Fin N)) (hq : InjP q A) :
    2 ^ l * ((Ext q A).filter (fun a => ¬ InjP a A')).card ≤ A'.card ^ 2 * (Ext q A).card := by
  set pairs := (A' ×ˢ A').filter (fun p : Fin N × Fin N => p.1 ≠ p.2 ∧ (p.1 ∉ A ∨ p.2 ∉ A))
    with hpairs
  have hsub : (Ext q A).filter (fun a => ¬ InjP a A') ⊆
      pairs.biUnion (fun p => (Ext q A).filter (fun a => ∀ b, a (p.1, b) = a (p.2, b))) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haE, haI⟩ := ha
    simp only [InjP, not_forall] at haI
    obtain ⟨i, hi, i', hi', hsame, hne⟩ := haI
    have hfree : i ∉ A ∨ i' ∉ A := by
      by_contra hc
      push Not at hc
      apply hne
      apply hq i hc.1 i' hc.2
      intro b
      rw [← mem_Ext.mp haE i hc.1 b, ← mem_Ext.mp haE i' hc.2 b]
      exact hsame b
    refine Finset.mem_biUnion.mpr ⟨(i, i'), ?_, Finset.mem_filter.mpr ⟨haE, hsame⟩⟩
    simp only [hpairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hi, hi'⟩, hne, hfree⟩
  calc 2 ^ l * ((Ext q A).filter (fun a => ¬ InjP a A')).card
      ≤ 2 ^ l * ∑ p ∈ pairs, ((Ext q A).filter (fun a => ∀ b, a (p.1, b) = a (p.2, b))).card :=
        Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = ∑ p ∈ pairs, 2 ^ l * ((Ext q A).filter (fun a => ∀ b, a (p.1, b) = a (p.2, b))).card :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ pairs, (Ext q A).card := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [hpairs, Finset.mem_filter] at hp
        exact pair_bound q A p.1 p.2 hp.2.2 hp.2.1
    _ = pairs.card * (Ext q A).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ A'.card ^ 2 * (Ext q A).card := by
        apply Nat.mul_le_mul_right
        calc pairs.card ≤ (A' ×ˢ A').card := Finset.card_filter_le _ _
          _ = A'.card ^ 2 := by rw [Finset.card_product, sq]

/-! ## The closure of a line -/

/-- Every equation of `L` involves no pigeon outside `A`, or at least `k0` of them. -/
def Good (k0 : ℕ) (A : Finset (Fin N)) (L : QLine (Fin N × Fin l)) : Prop :=
  ∀ e ∈ L, inv e ⊆ A ∨ k0 ≤ (inv e \ A).card

theorem closure_grow (k0 : ℕ) (L : QLine (Fin N × Fin l)) : ∀ n (S : Finset (Fin N)),
    (L.toFinset.filter (fun e => ¬ inv e ⊆ S)).card ≤ n →
    ∃ A : Finset (Fin N), A.card ≤ S.card + n * k0 ∧ Good k0 A L := by
  intro n
  induction n with
  | zero =>
    intro S hS
    refine ⟨S, by simp, fun e he => Or.inl ?_⟩
    by_contra hc
    have hmem : e ∈ L.toFinset.filter (fun e => ¬ inv e ⊆ S) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he, hc⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hS
    rw [hS] at hmem; simp at hmem
  | succ n ih =>
    intro S hS
    by_cases hg : Good k0 S L
    · exact ⟨S, by omega, hg⟩
    · simp only [Good, not_forall, not_or, not_le] at hg
      obtain ⟨e, he, hns, hlt⟩ := hg
      have hcard : (S ∪ inv e).card ≤ S.card + k0 := by
        have := Finset.card_sdiff_add_card (inv e) S
        rw [Finset.union_comm] at this
        omega
      have hlt' : (L.toFinset.filter (fun f => ¬ inv f ⊆ S ∪ inv e)).card <
          (L.toFinset.filter (fun f => ¬ inv f ⊆ S)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨e, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he, hns⟩, ?_⟩
          simp only [Finset.mem_filter, not_and, not_not]
          intro _; exact Finset.subset_union_right
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun h => hx.2 (h.trans Finset.subset_union_left)⟩
      obtain ⟨A, hA, hgA⟩ := ih (S ∪ inv e)
        (by omega)
      exact ⟨A, by rw [Nat.succ_mul]; omega, hgA⟩

theorem closure_exists (k0 : ℕ) (L : QLine (Fin N × Fin l)) :
    ∃ A : Finset (Fin N), A.card ≤ L.length * k0 ∧ Good k0 A L := by
  obtain ⟨A, hA, hg⟩ := closure_grow k0 L L.length ∅
    ((Finset.card_filter_le _ _).trans (List.toFinset_card_le L))
  exact ⟨A, by simpa using hA, hg⟩

/-- The closure of a line: a set of at most `|L| k0` pigeons for which `L` is good. -/
noncomputable def clo (k0 : ℕ) (L : QLine (Fin N × Fin l)) : Finset (Fin N) :=
  (closure_exists k0 L).choose

theorem clo_card (k0 : ℕ) (L : QLine (Fin N × Fin l)) : (clo k0 L).card ≤ L.length * k0 :=
  (closure_exists k0 L).choose_spec.1

theorem clo_good (k0 : ℕ) (L : QLine (Fin N × Fin l)) : Good k0 (clo k0 L) L :=
  (closure_exists k0 L).choose_spec.2

/-! ## The walk -/

/-- One step of the walk: from a point injective on the closure of `L` and falsifying `L`,
to a point injective on the closure of one of the premises and falsifying it. -/
theorem step (W : ℕ) (hW : 0 < W) (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l)
    (L L1 L2 : QLine (Fin N × Fin l)) (hL : L.length ≤ W) (hL1 : L1.length ≤ W)
    (hL2 : L2.length ≤ W) (himp : ∀ a, Fals a L → Fals a L1 ∨ Fals a L2)
    (q : Fin N × Fin l → Bool) (hq : InjP q (clo (16 * W ^ 2) L)) (hF : Fals q L) :
    ∃ a, (Fals a L1 ∧ InjP a (clo (16 * W ^ 2) L1)) ∨
      (Fals a L2 ∧ InjP a (clo (16 * W ^ 2) L2)) := by
  set k0 := 16 * W ^ 2 with hk0
  set E := Ext q (clo k0 L) with hE
  have hbad : ∀ L' : QLine (Fin N × Fin l), L'.length ≤ W →
      8 * (E.filter (fun a => ¬ InjP a (clo k0 L'))).card ≤ E.card := by
    intro L' hL'
    have h1 := bad_inj q (clo k0 L) (clo k0 L') hq
    have hc : (clo k0 L').card ≤ W * k0 := (clo_card k0 L').trans (Nat.mul_le_mul_right _ hL')
    have hc2 : (clo k0 L').card ^ 2 ≤ (W * k0) ^ 2 := Nat.pow_le_pow_left hc 2
    have h3 : 2 ^ l * (8 * (E.filter (fun a => ¬ InjP a (clo k0 L'))).card) ≤
        2 ^ l * E.card := by
      calc 2 ^ l * (8 * (E.filter (fun a => ¬ InjP a (clo k0 L'))).card)
          = 8 * (2 ^ l * (E.filter (fun a => ¬ InjP a (clo k0 L'))).card) := by ring
        _ ≤ 8 * ((clo k0 L').card ^ 2 * E.card) := Nat.mul_le_mul_left _ h1
        _ ≤ 8 * ((W * k0) ^ 2 * E.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
        _ = (8 * (W * k0) ^ 2) * E.card := by ring
        _ ≤ 2 ^ l * E.card := Nat.mul_le_mul_right _ hnum
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)
  have hU : 4 * (E.filter (fun a => ¬ Fals a L)).card ≤ E.card :=
    union_bound W hW L hL (clo k0 L) (clo_good k0 L) q hF
  have hsplit := Finset.card_filter_add_card_filter_not (s := E) (fun a => Fals a L)
  have hpos : 0 < E.card := Finset.card_pos.mpr ⟨q, self_mem_Ext q _⟩
  by_contra hno
  push Not at hno
  have hsub : E.filter (fun a => Fals a L) ⊆ E.filter (fun a => ¬ InjP a (clo k0 L1)) ∪
      E.filter (fun a => ¬ InjP a (clo k0 L2)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases himp a ha.2 with h | h
    · exact Or.inl ⟨ha.1, (hno a).1 h⟩
    · exact Or.inr ⟨ha.1, (hno a).2 h⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have b1 := hbad L1 hL1
  have b2 := hbad L2 hL2
  omega

theorem inv_lit (i : Fin N) (b : Fin l) (β : Bool) : inv (litQEq ((i, b), β)) = {i} := by
  ext j
  unfold inv
  rw [Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, litQEq]
  constructor
  · rintro ⟨b', h⟩
    by_contra hj
    apply h
    simp [hj]
  · rintro rfl
    exact ⟨b, by simp⟩

/-- An axiom line cannot be reached: a point injective on its closure satisfies it. -/
theorem axiom_case (k0 : ℕ) (hk0 : 2 ≤ k0) (hl : 0 < l)
    (C : PEqualNP.ProofComplexity.Clause (Fin N × Fin l))
    (hC : C ∈ PEqualNP.ProofComplexity.BPHP N l) (L : QLine (Fin N × Fin l))
    (hL : ∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit)
    (q : Fin N × Fin l → Bool) (hq : InjP q (clo k0 L)) (hF : Fals q L) : False := by
  obtain ⟨i, i', α, hne, rfl⟩ := hC
  have hin : ∀ j b, (j = i ∨ j = i') → litQEq ((j, b), !α b) ∈ L := by
    intro j b hj
    rw [hL]
    refine ⟨((j, b), !α b), ?_, rfl⟩
    rcases hj with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  have hA : ∀ j, (j = i ∨ j = i') → j ∈ clo k0 L := by
    intro j hj
    rcases clo_good k0 L _ (hin j ⟨0, hl⟩ hj) with h | h
    · rw [inv_lit] at h; exact Finset.singleton_subset_iff.mp h
    · rw [inv_lit] at h
      have := Finset.card_le_card (Finset.sdiff_subset : ({j} : Finset (Fin N)) \ clo k0 L ⊆ {j})
      rw [Finset.card_singleton] at this
      omega
  have hval : ∀ j b, (j = i ∨ j = i') → q (j, b) = α b := by
    intro j b hj
    have hnot := hF _ (hin j b hj)
    by_contra hc
    apply hnot
    apply PEqualNP.Search.Helpers.litQEq_holds
    simp only
    revert hc
    cases q (j, b) <;> cases α b <;> simp
  exact hne (hq i (hA i (Or.inl rfl)) i' (hA i' (Or.inr rfl))
    (fun b => by rw [hval i b (Or.inl rfl), hval i' b (Or.inr rfl)]))

/-- The walk: no line of a derivation of width at most `W` is falsified by a point injective
on its closure. -/
theorem walk (W : ℕ) (hW : 0 < W) (hl : 0 < l) (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l) :
    ∀ π : List (QLine (Fin N × Fin l)),
      IsResLinQDerivation (PEqualNP.ProofComplexity.BPHP N l) π →
      (∀ L ∈ π, L.length ≤ W) →
      ∀ L ∈ π, ∀ q, InjP q (clo (16 * W ^ 2) L) → Fals q L → False := by
  intro π h
  induction h with
  | nil => intro _ L hL; simp at hL
  | ax C _ hC hL ih =>
    intro hw L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · intro q hq hF
      have : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ hW
      exact axiom_case (16 * W ^ 2) (by omega) hl C hC _ hL q hq hF
    · exact ih (fun L hL => hw L (List.mem_cons_of_mem _ hL)) L' hL'
  | @res π e e' C D α β _ h1 h2 ih =>
    intro hw L' hL'
    have hw' : ∀ L ∈ π, L.length ≤ W := fun L hL => hw L (List.mem_cons_of_mem _ hL)
    rcases List.mem_cons.mp hL' with rfl | hL'
    · intro q hq hF
      have himp : ∀ a, Fals a ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) →
          Fals a (e :: C) ∨ Fals a (e' :: D) := by
        intro a ha
        by_contra hc
        rw [not_or] at hc
        simp only [Fals, not_forall, not_not] at hc
        obtain ⟨⟨f, hf, haf⟩, ⟨g, hg, hag⟩⟩ := hc
        rcases List.mem_cons.mp hf with rfl | hf
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact ha _ List.mem_cons_self (PEqualNP.Search.Helpers.combo_holds a _ _ α β haf hag)
          · exact ha g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)) hag
        · exact ha f (List.mem_cons_of_mem _ (List.mem_append_left _ hf)) haf
      obtain ⟨a, h | h⟩ := step W hW hnum _ (e :: C) (e' :: D) (hw _ List.mem_cons_self)
        (hw' _ h1) (hw' _ h2) himp q hq hF
      · exact ih hw' _ h1 a h.2 h.1
      · exact ih hw' _ h2 a h.2 h.1
    · exact ih hw' L' hL'
  | @weaken π C D _ hC himp ih =>
    intro hw L' hL'
    have hw' : ∀ L ∈ π, L.length ≤ W := fun L hL => hw L (List.mem_cons_of_mem _ hL)
    rcases List.mem_cons.mp hL' with rfl | hL'
    · intro q hq hF
      have himp' : ∀ a, Fals a L' → Fals a C ∨ Fals a C := fun a ha => Or.inl fun f hf haf => by
        obtain ⟨g, hg, hag⟩ := himp a ⟨f, hf, haf⟩
        exact ha g hg hag
      obtain ⟨a, h | h⟩ := step W hW hnum _ C C (hw _ List.mem_cons_self)
        (hw' _ hC) (hw' _ hC) himp' q hq hF
      · exact ih hw' _ hC a h.2 h.1
      · exact ih hw' _ hC a h.2 h.1
    · exact ih hw' L' hL'

end Pigeon

/-- Width lower bound: every Res(lin) refutation over the integers of the bit pigeonhole
formula with `2 ^ (8 m) + 1` pigeons has a line with more than `2 ^ m` equations. -/
theorem width_lower (m : ℕ) (hm : 8 ≤ m)
    (π : List (PEqualNP.Search.QLine (Fin (2 ^ (8 * m) + 1) × Fin (8 * m))))
    (hπ : PEqualNP.Search.IsResLinQRefutation
      (PEqualNP.ProofComplexity.BPHP (2 ^ (8 * m) + 1) (8 * m)) π) :
    ∃ L ∈ π, 2 ^ m < L.length := by
  by_contra hc
  push Not at hc
  have hnum : 8 * (2 ^ m * (16 * (2 ^ m) ^ 2)) ^ 2 ≤ 2 ^ (8 * m) := by
    have : 8 * (2 ^ m * (16 * (2 ^ m) ^ 2)) ^ 2 = 2 ^ (11 + 6 * m) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, show (16 : ℕ) = 2 ^ 4 by norm_num]; ring
    rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine walk (2 ^ m) (by positivity) (by omega) hnum π hπ.1 hc [] hπ.2 (fun _ => false) ?_ ?_
  · have h0 := clo_card (16 * (2 ^ m) ^ 2)
      ([] : QLine (Fin (2 ^ (8 * m) + 1) × Fin (8 * m)))
    simp only [List.length_nil, zero_mul, Nat.le_zero, Finset.card_eq_zero] at h0
    rw [h0]; intro i hi; simp at hi
  · intro e he; simp at he

end PEqualNP.Search.Helpers.Width
