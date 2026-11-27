import PEqualNP.Defs
import PEqualNP.Search.Helpers.Width.Walk
import Mathlib.Tactic

/-!
# Helpers: anti-concentration of a linear form over pigeons placed in hole sets

Points are `y : ι × Fin l → Bool`, the hole of pigeon `i` is `fun b => y (i, b)`. The domain
`Dom q P T` places every pigeon `i` of `P` in a hole of `T i` and fixes the others as in `q`.
An integer form with a nonzero coefficient on some bit of every pigeon of `P' ⊆ P` takes a
fixed value on few points of the domain: with each `T i` of size `M ≥ 3 2^l / 4`, the count
`N` satisfies `N ^ 2 (|P'| + 1) ≤ 8 |Dom| ^ 2`, that is `N ≤ sqrt 8 |Dom| / sqrt (|P'| + 1)`.

Proof: for every pigeon of `P'` choose inside its hole set a set `Q i` of `2^(l-1)` holes
closed under flipping one bit `β i` with nonzero coefficient. Split the domain by the set `Z`
of pigeons of `P'` whose hole lies in `Q i`. On a piece, resampling the bits `β i` of the
pigeons of `Z` stays in the piece, so the Erdos-Littlewood-Offord count `lo_bound` with fiber
counting `fiber_count` bounds the count on the piece by `|piece| / sqrt |Z|`. The pieces have
binomial sizes, and Cauchy-Schwarz with `sum_Z |piece| / (|Z|+1) ≤ M^(k+1) / (A (k+1))`
finishes. No probability: everything is a count.
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.Search PEqualNP.Search.Helpers.Width

open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {l : ℕ}

/-- The hole of pigeon `i` at the point `y`. -/
def hole (y : ι × Fin l → Bool) (i : ι) : Fin l → Bool := fun b => y (i, b)

/-- The points that put every pigeon `i` of `P` in a hole of `T i` and agree with `q` on the
bits of the other pigeons. -/
noncomputable def Dom (q : ι × Fin l → Bool) (P : Finset ι) (T : ι → Finset (Fin l → Bool)) :
    Finset (ι × Fin l → Bool) :=
  Finset.univ.filter fun y => (∀ i, i ∉ P → ∀ b, y (i, b) = q (i, b)) ∧ ∀ i ∈ P, hole y i ∈ T i

theorem mem_Dom {q y : ι × Fin l → Bool} {P : Finset ι} {T : ι → Finset (Fin l → Bool)} :
    y ∈ Dom q P T ↔ (∀ i, i ∉ P → ∀ b, y (i, b) = q (i, b)) ∧ ∀ i ∈ P, hole y i ∈ T i := by
  simp [Dom]

theorem card_Dom (q : ι × Fin l → Bool) (P : Finset ι) (T : ι → Finset (Fin l → Bool)) :
    (Dom q P T).card = ∏ i ∈ P, (T i).card := by
  rw [← Finset.card_pi]
  refine Finset.card_bij' (fun y _ => fun i _ => hole y i)
    (fun f _ => fun v => if h : v.1 ∈ P then f v.1 h v.2 else q v) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_pi]
    intro i hi
    exact (mem_Dom.mp hy).2 i hi
  · intro f hf
    rw [Finset.mem_pi] at hf
    rw [mem_Dom]
    refine ⟨fun i hi b => by simp [hi], fun i hi => ?_⟩
    have : hole (fun v : ι × Fin l => if h : v.1 ∈ P then f v.1 h v.2 else q v) i = f i hi := by
      funext b; simp [hole, hi]
    rw [this]; exact hf i hi
  · intro y hy
    funext ⟨i, b⟩
    by_cases hi : i ∈ P
    · simp [hi, hole]
    · simp only [hi, dite_false]
      exact ((mem_Dom.mp hy).1 i hi b).symm
  · intro f hf
    funext i hi
    funext b
    simp [hole, hi]

/-! ## A set of holes closed under flipping one bit -/

/-- Inside a hole set `F` with `r + 2^(l-1) ≤ |F|`, there are `r` disjoint pairs of holes
differing only in bit `b`: a subset of `F` of size `2 r` closed under setting bit `b`. -/
theorem exists_pairs (F : Finset (Fin l → Bool)) (b : Fin l) (r : ℕ)
    (hr : r + 2 ^ (l - 1) ≤ F.card) :
    ∃ Q ⊆ F, Q.card = 2 * r ∧ ∀ h ∈ Q, ∀ v, Function.update h b v ∈ Q := by
  set up : (Fin l → Bool) → (Fin l → Bool) := fun h => Function.update h b true with hup
  set dn : (Fin l → Bool) → (Fin l → Bool) := fun h => Function.update h b false with hdn
  set C0 := (Finset.univ : Finset (Fin l → Bool)).filter (fun h => h b = false) with hC0
  set C1 := (Finset.univ : Finset (Fin l → Bool)).filter (fun h => ¬ h b = false) with hC1
  have hupb : ∀ h, up h b = true := fun h => by simp [hup]
  have hdnb : ∀ h, dn h b = false := fun h => by simp [hdn]
  have hdnup : ∀ h, h b = false → dn (up h) = h := by
    intro h hh; simp only [hdn, hup, Function.update_idem]
    rw [← hh, Function.update_eq_self]
  have hupdn : ∀ h, ¬ h b = false → up (dn h) = h := by
    intro h hh; simp only [hdn, hup, Function.update_idem]
    have : h b = true := by simpa using hh
    rw [← this, Function.update_eq_self]
  have hl : 1 ≤ l := by have := b.2; omega
  have hcube : C0.card + C1.card = 2 ^ l := by
    rw [hC0, hC1, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h01 : C0.card = C1.card := by
    refine Finset.card_bij' (fun h _ => up h) (fun h _ => dn h) ?_ ?_ ?_ ?_
    · intro h _; simp [hC1, hupb]
    · intro h _; simp [hC0, hdnb]
    · intro h hh; exact hdnup h (Finset.mem_filter.mp hh).2
    · intro h hh; exact hupdn h (Finset.mem_filter.mp hh).2
  have hC0c : C0.card = 2 ^ (l - 1) := by
    have : 2 ^ l = 2 * 2 ^ (l - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  set F0 := F.filter (fun h => h b = false) with hF0
  set F1 := F.filter (fun h => ¬ h b = false) with hF1
  set G := C0.filter (fun h => up h ∈ F) with hG
  have hFF : F0.card + F1.card = F.card := Finset.card_filter_add_card_filter_not _
  have hG1 : G.card = F1.card := by
    refine Finset.card_bij' (fun h _ => up h) (fun h _ => dn h) ?_ ?_ ?_ ?_
    · intro h hh; simp only [hG, Finset.mem_filter] at hh; simp [hF1, hupb, hh.2]
    · intro h hh
      simp only [hF1, Finset.mem_filter] at hh
      simp [hG, hC0, hdnb, hupdn h hh.2, hh.1]
    · intro h hh; exact hdnup h (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2
    · intro h hh; exact hupdn h (Finset.mem_filter.mp hh).2
  have hunion : (F0 ∪ G).card ≤ C0.card := by
    apply Finset.card_le_card
    intro h hh
    rcases Finset.mem_union.mp hh with hh | hh
    · simp only [hF0, Finset.mem_filter] at hh; simp [hC0, hh.2]
    · exact (Finset.mem_filter.mp hh).1
  have hui := Finset.card_union_add_card_inter F0 G
  have hR : r ≤ (F0 ∩ G).card := by omega
  obtain ⟨R, hRs, hRc⟩ := Finset.exists_subset_card_eq hR
  have hRb : ∀ h ∈ R, h b = false ∧ h ∈ F ∧ up h ∈ F := by
    intro h hh
    have := hRs hh
    rw [Finset.mem_inter] at this
    simp only [hF0, hG, Finset.mem_filter] at this
    exact ⟨this.1.2, this.1.1, this.2.2⟩
  refine ⟨R ∪ R.image up, ?_, ?_, ?_⟩
  · intro h hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact (hRb h hh).2.1
    · obtain ⟨h0, h0R, rfl⟩ := Finset.mem_image.mp hh
      exact (hRb h0 h0R).2.2
  · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn, hRc]
    · ring
    · intro h hh h' hh' he
      rw [← hdnup h (hRb h hh).1, ← hdnup h' (hRb h' hh').1]
      exact congrArg dn he
    · rw [Finset.disjoint_left]
      intro h hh hh'
      obtain ⟨h0, _, rfl⟩ := Finset.mem_image.mp hh'
      have := (hRb _ hh).1
      rw [hupb] at this; exact absurd this (by simp)
  · have key : ∀ h ∈ R, ∀ v, Function.update h b v ∈ R ∪ R.image up := by
      intro h hh v
      cases v
      · have : Function.update h b false = h := by
          rw [← (hRb h hh).1, Function.update_eq_self]
        rw [this]; exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)
    intro h hh v
    rcases Finset.mem_union.mp hh with hh | hh
    · exact key h hh v
    · obtain ⟨h0, h0R, rfl⟩ := Finset.mem_image.mp hh
      simp only [hup, Function.update_idem]
      exact key h0 h0R v

/-! ## Resampling the chosen bits of a set of pigeons -/

/-- The chosen bit `β i` of every pigeon `i` of `Z`, enumerated. -/
noncomputable def bits (Z : Finset ι) (β : ι → Fin l) : Fin Z.card → ι × Fin l :=
  fun j => ((Z.equivFin.symm j : ι), β (Z.equivFin.symm j))

theorem bits_inj (Z : Finset ι) (β : ι → Fin l) : Function.Injective (bits Z β) := by
  intro j j' h
  exact Z.equivFin.symm.injective (Subtype.ext (congrArg Prod.fst h))

theorem glue_bits_off (Z : Finset ι) (β : ι → Fin l) (y : Fin Z.card → Bool)
    (z : ι × Fin l → Bool) (i : ι) (hi : i ∉ Z) (b : Fin l) :
    glue (bits Z β) y z (i, b) = z (i, b) := by
  apply glue_apply_not
  rintro ⟨j, hj⟩
  apply hi
  have : ((Z.equivFin.symm j : ι)) = i := congrArg Prod.fst hj
  rw [← this]; exact (Z.equivFin.symm j).2

theorem hole_glue_bits (Z : Finset ι) (β : ι → Fin l) (y : Fin Z.card → Bool)
    (z : ι × Fin l → Bool) (i : ι) (hi : i ∈ Z) :
    hole (glue (bits Z β) y z) i =
      Function.update (hole z i) (β i) (y (Z.equivFin ⟨i, hi⟩)) := by
  funext b
  have hj : bits Z β (Z.equivFin ⟨i, hi⟩) = (i, β i) := by
    simp [bits]
  by_cases hb : b = β i
  · subst hb
    simp only [hole, Function.update_self]
    rw [← hj, glue_apply_t (bits_inj Z β)]
  · rw [Function.update_of_ne hb]
    simp only [hole]
    apply glue_apply_not
    rintro ⟨j, hj'⟩
    have h1 : ((Z.equivFin.symm j : ι)) = i := congrArg Prod.fst hj'
    have h2 : β (Z.equivFin.symm j) = b := congrArg Prod.snd hj'
    rw [h1] at h2
    exact hb h2.symm

/-- Erdos-Littlewood-Offord on a piece: if `S` is closed under resampling the chosen bits of
the pigeons of `Z`, and the form has a nonzero coefficient on each of them, then the form
takes a fixed value on at most a `1 / sqrt |Z|` fraction of `S`. -/
theorem piece_bound (Z : Finset ι) (β : ι → Fin l) (e : QEq (ι × Fin l))
    (hβ : ∀ i ∈ Z, e.1 (i, β i) ≠ 0) (S : Finset (ι × Fin l → Bool))
    (hS : ∀ y ∈ S, ∀ v, glue (bits Z β) v y ∈ S) :
    Nat.sqrt Z.card * (S.filter fun y => QEq.Holds y e).card ≤ S.card := by
  set k := Z.card with hk
  set t := bits Z β with ht_def
  have ht : Function.Injective t := bits_inj Z β
  have hcoef : ∀ j, e.1 (t j) ≠ 0 := fun j => hβ _ (Z.equivFin.symm j).2
  apply fiber_count t ht S hS _ (Nat.sqrt k)
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
  have h2 : (Nat.sqrt k * c) ^ 2 ≤ (2 ^ k) ^ 2 := by
    rw [← four_pow]
    calc (Nat.sqrt k * c) ^ 2 = c ^ 2 * Nat.sqrt k ^ 2 := by ring
      _ ≤ c ^ 2 * k := Nat.mul_le_mul_left _ (Nat.sqrt_le' k)
      _ ≤ 4 ^ k := hlo
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

/-- The squared form on a piece: `count ^ 2 (|Z| + 1) ≤ 4 |S| ^ 2`. -/
theorem piece_sq (Z : Finset ι) (β : ι → Fin l) (e : QEq (ι × Fin l))
    (hβ : ∀ i ∈ Z, e.1 (i, β i) ≠ 0) (S : Finset (ι × Fin l → Bool))
    (hS : ∀ y ∈ S, ∀ v, glue (bits Z β) v y ∈ S) :
    (S.filter fun y => QEq.Holds y e).card ^ 2 * (Z.card + 1) ≤ 4 * S.card ^ 2 := by
  have hb := piece_bound Z β e hβ S hS
  set c := (S.filter fun y => QEq.Holds y e).card
  have hcS : c ≤ S.card := Finset.card_filter_le _ _
  set m := Z.card
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; nlinarith
  · set s := Nat.sqrt m
    have hs : 1 ≤ s := Nat.sqrt_pos.mpr hpos
    have hlt : m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' m
    have h4 : m + 1 ≤ 4 * s ^ 2 := by nlinarith
    calc c ^ 2 * (m + 1) ≤ c ^ 2 * (4 * s ^ 2) := Nat.mul_le_mul_left _ h4
      _ = 4 * (s * c) ^ 2 := by ring
      _ ≤ 4 * S.card ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)

/-! ## The count over the whole domain -/

/-- The core count. For each pigeon `i` of `P' ⊆ P`: its hole set `T i` has `M` holes and
contains a set `Q i` of `A` holes closed under setting bit `β i`, and the form has a nonzero
coefficient on `(i, β i)`. Then the number `N` of points of the domain where the form takes
its value satisfies `N ^ 2 (|P'| + 1) A ≤ 4 M |Dom| ^ 2`. -/
theorem lof_core (q : ι × Fin l → Bool) (P P' : Finset ι) (hPP : P' ⊆ P)
    (T Q : ι → Finset (Fin l → Bool)) (β : ι → Fin l) (A M : ℕ) (hAM : A ≤ M)
    (hQT : ∀ i ∈ P', Q i ⊆ T i) (hQA : ∀ i ∈ P', (Q i).card = A)
    (hTM : ∀ i ∈ P', (T i).card = M)
    (hQc : ∀ i ∈ P', ∀ h ∈ Q i, ∀ v, Function.update h (β i) v ∈ Q i)
    (e : QEq (ι × Fin l)) (hβ : ∀ i ∈ P', e.1 (i, β i) ≠ 0) :
    ((Dom q P T).filter fun y => QEq.Holds y e).card ^ 2 * ((P'.card + 1) * A) ≤
      4 * M * (Dom q P T).card ^ 2 := by
  set X := Dom q P T with hXdef
  let TZ : Finset ι → ι → Finset (Fin l → Bool) := fun Z i =>
    if i ∈ P' then (if i ∈ Z then Q i else T i \ Q i) else T i
  let f : (ι × Fin l → Bool) → Finset ι := fun y => P'.filter (fun i => hole y i ∈ Q i)
  have hf : ∀ y ∈ X, f y ∈ P'.powerset :=
    fun y _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hfib : ∀ Z ∈ P'.powerset, X.filter (fun y => f y = Z) = Dom q P (TZ Z) := by
    intro Z hZ
    rw [Finset.mem_powerset] at hZ
    ext y
    rw [Finset.mem_filter, hXdef, mem_Dom, mem_Dom]
    constructor
    · rintro ⟨⟨hoff, hin⟩, hfy⟩
      refine ⟨hoff, fun i hi => ?_⟩
      have hmem : i ∈ f y ↔ i ∈ Z := by rw [hfy]
      simp only [f, Finset.mem_filter] at hmem
      by_cases hi' : i ∈ P'
      · by_cases hz : i ∈ Z
        · simp only [TZ, hi', hz, ite_true]; exact (hmem.mpr hz).2
        · simp only [TZ, hi', hz, ite_true, ite_false]
          exact Finset.mem_sdiff.mpr ⟨hin i hi, fun h => hz (hmem.mp ⟨hi', h⟩)⟩
      · simp only [TZ, hi', ite_false]; exact hin i hi
    · rintro ⟨hoff, hin⟩
      refine ⟨⟨hoff, fun i hi => ?_⟩, ?_⟩
      · have := hin i hi
        by_cases hi' : i ∈ P'
        · by_cases hz : i ∈ Z
          · simp only [TZ, hi', hz, ite_true] at this; exact hQT i hi' this
          · simp only [TZ, hi', hz, ite_true, ite_false] at this
            exact (Finset.mem_sdiff.mp this).1
        · simp only [TZ, hi', ite_false] at this; exact this
      · ext i
        simp only [f, Finset.mem_filter]
        constructor
        · rintro ⟨hi', hq⟩
          by_contra hz
          have := hin i (hPP hi')
          simp only [TZ, hi', hz, ite_true, ite_false] at this
          exact (Finset.mem_sdiff.mp this).2 hq
        · intro hz
          have hi' := hZ hz
          have := hin i (hPP hi')
          simp only [TZ, hi', hz, ite_true] at this
          exact ⟨hi', this⟩
  have hclosed : ∀ Z ∈ P'.powerset, ∀ y ∈ Dom q P (TZ Z), ∀ v,
      glue (bits Z β) v y ∈ Dom q P (TZ Z) := by
    intro Z hZ y hy v
    rw [Finset.mem_powerset] at hZ
    rw [mem_Dom] at hy ⊢
    refine ⟨fun i hi b => ?_, fun i hi => ?_⟩
    · rw [glue_bits_off Z β v y i (fun h => hi (hPP (hZ h)))]; exact hy.1 i hi b
    · by_cases hz : i ∈ Z
      · rw [hole_glue_bits Z β v y i hz]
        have hi' := hZ hz
        have := hy.2 i hi
        simp only [TZ, hi', hz, ite_true] at this ⊢
        exact hQc i hi' _ this _
      · have : hole (glue (bits Z β) v y) i = hole y i := by
          funext b; exact glue_bits_off Z β v y i hz b
        rw [this]; exact hy.2 i hi
  set K0 := ∏ i ∈ P \ P', (T i).card with hK0
  have hcardZ : ∀ Z ∈ P'.powerset, (Dom q P (TZ Z)).card =
      K0 * (A ^ Z.card * (M - A) ^ (P'.card - Z.card)) := by
    intro Z hZ
    rw [Finset.mem_powerset] at hZ
    rw [card_Dom, ← Finset.prod_sdiff hPP]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp [TZ, (Finset.mem_sdiff.mp hi).2]
    · rw [Finset.prod_congr rfl (g := fun i => if i ∈ Z then A else M - A)]
      · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have h1 : P'.filter (· ∈ Z) = Z := by
          ext i; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hZ h, h⟩⟩
        have h2 := Finset.card_filter_add_card_filter_not (s := P') (fun i => i ∈ Z)
        rw [h1] at h2 ⊢
        congr 2; omega
      · intro i hi
        by_cases hz : i ∈ Z
        · simp [TZ, hi, hz, hQA i hi]
        · simp [TZ, hi, hz, Finset.card_sdiff_of_subset (hQT i hi), hQA i hi, hTM i hi]
  have hX : X.card = K0 * M ^ P'.card := by
    rw [hXdef, card_Dom, ← Finset.prod_sdiff hPP, Finset.prod_congr rfl (fun i hi => hTM i hi),
      Finset.prod_const]
  let N : Finset ι → ℕ := fun Z => (Dom q P (TZ Z)).card
  let c : Finset ι → ℕ := fun Z => ((Dom q P (TZ Z)).filter fun y => QEq.Holds y e).card
  have hXsum : X.card = ∑ Z ∈ P'.powerset, N Z := by
    rw [Finset.card_eq_sum_card_fiberwise hf]
    exact Finset.sum_congr rfl fun Z hZ => by rw [hfib Z hZ]
  have hHsum : (X.filter fun y => QEq.Holds y e).card = ∑ Z ∈ P'.powerset, c Z := by
    rw [Finset.card_eq_sum_card_fiberwise (fun y hy => hf y (Finset.mem_filter.mp hy).1)]
    refine Finset.sum_congr rfl fun Z hZ => ?_
    simp only [c]
    rw [← hfib Z hZ, Finset.filter_filter, Finset.filter_filter]
    congr 1
    exact Finset.filter_congr fun y _ => and_comm
  have hpiece : ∀ Z ∈ P'.powerset, c Z ^ 2 * (Z.card + 1) ≤ 4 * N Z ^ 2 := fun Z hZ =>
    piece_sq Z β e (fun i hi => hβ i (Finset.mem_powerset.mp hZ hi)) _ (hclosed Z hZ)
  -- Cauchy-Schwarz over the pieces
  have hCS : (∑ Z ∈ P'.powerset, (c Z : ℝ)) ^ 2 ≤
      (∑ Z ∈ P'.powerset, (N Z : ℝ) / (Z.card + 1)) * ∑ Z ∈ P'.powerset, 4 * (N Z : ℝ) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intros; positivity
    · intros; positivity
    · intro Z hZ
      have h' : ((c Z : ℝ)) ^ 2 * (Z.card + 1) ≤ 4 * (N Z : ℝ) ^ 2 := by
        exact_mod_cast hpiece Z hZ
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : (N Z : ℝ) * (4 * N Z) = 4 * (N Z : ℝ) ^ 2 := by ring
      linarith
  -- the binomial sum
  set k := P'.card with hk
  have hS1 : (∑ Z ∈ P'.powerset, (N Z : ℝ) / (Z.card + 1)) * (A * (k + 1)) ≤
      K0 * (M : ℝ) ^ (k + 1) := by
    set B : ℝ := (M : ℝ) - A with hB
    have hrw : ∀ Z ∈ P'.powerset, (N Z : ℝ) / (Z.card + 1) =
        (fun m : ℕ => (K0 : ℝ) * ((A : ℝ) ^ m * B ^ (k - m)) / (m + 1)) Z.card := by
      intro Z hZ
      simp only [N]
      rw [hcardZ Z hZ]
      push_cast [Nat.cast_sub hAM]
      ring
    rw [Finset.sum_congr rfl hrw,
      Finset.sum_powerset_apply_card (fun m : ℕ => (K0 : ℝ) * ((A : ℝ) ^ m * B ^ (k - m)) / (m + 1)),
      Finset.sum_mul]
    have hB0 : 0 ≤ B := by rw [hB, sub_nonneg]; exact_mod_cast hAM
    have hterm : ∀ m ∈ Finset.range (k + 1),
        (k.choose m • ((K0 : ℝ) * ((A : ℝ) ^ m * B ^ (k - m)) / (m + 1))) * (A * (k + 1)) =
        K0 * ((A : ℝ) ^ (m + 1) * B ^ (k + 1 - (m + 1)) * ((k + 1).choose (m + 1) : ℕ)) := by
      intro m _
      have hc' : ((k : ℝ) + 1) * (k.choose m : ℕ) = ((k + 1).choose (m + 1) : ℕ) * (m + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq k m
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      rw [nsmul_eq_mul, Nat.add_sub_add_right]
      calc ((k.choose m : ℕ) : ℝ) * ((K0 : ℝ) * ((A : ℝ) ^ m * B ^ (k - m)) / (m + 1)) *
            (A * (k + 1))
          = K0 * ((A : ℝ) ^ (m + 1) * B ^ (k - m)) * (((k : ℝ) + 1) * (k.choose m : ℕ)) /
              (m + 1) := by ring
        _ = K0 * ((A : ℝ) ^ (m + 1) * B ^ (k - m)) *
              (((k + 1).choose (m + 1) : ℕ) * (m + 1)) / (m + 1) := by rw [hc']
        _ = _ := by field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hMAB : (A : ℝ) + B = M := by rw [hB]; ring
    have hpow := add_pow (A : ℝ) B (k + 1)
    rw [Finset.sum_range_succ', hMAB] at hpow
    rw [hpow]
    have hK0 : (0 : ℝ) ≤ K0 := Nat.cast_nonneg _
    apply mul_le_mul_of_nonneg_left _ hK0
    have : 0 ≤ (A : ℝ) ^ 0 * B ^ (k + 1 - 0) * ((k + 1).choose 0 : ℕ) := by positivity
    linarith
  -- assemble
  have hfin : ((X.filter fun y => QEq.Holds y e).card : ℝ) ^ 2 * ((k + 1) * A) ≤
      4 * M * (X.card : ℝ) ^ 2 := by
    rw [hHsum]
    push_cast
    have h4 : ∑ Z ∈ P'.powerset, 4 * (N Z : ℝ) = 4 * X.card := by
      rw [← Finset.mul_sum, hXsum]; push_cast; ring
    rw [h4] at hCS
    have hXr : (X.card : ℝ) = K0 * (M : ℝ) ^ k := by rw [hX]; push_cast; ring
    set S1 := ∑ Z ∈ P'.powerset, (N Z : ℝ) / (Z.card + 1)
    have hX0 : (0 : ℝ) ≤ X.card := by positivity
    have hkA : (0 : ℝ) ≤ (k + 1) * A := by positivity
    calc (∑ Z ∈ P'.powerset, (c Z : ℝ)) ^ 2 * ((k + 1) * A)
        ≤ S1 * (4 * X.card) * ((k + 1) * A) := mul_le_mul_of_nonneg_right hCS hkA
      _ = 4 * X.card * (S1 * (A * (k + 1))) := by ring
      _ ≤ 4 * X.card * (K0 * (M : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = 4 * M * (X.card : ℝ) ^ 2 := by rw [hXr]; ring
  exact_mod_cast hfin

/-- Anti-concentration over hole sets of at least three quarters of the holes. Every pigeon `i`
of `P` is placed in its hole set `T i` (those of `P' ⊆ P` with `M` holes, `3 2^l ≤ 4 M`), the other pigeons are fixed as in `q`, and the form has a nonzero coefficient
on some bit of every pigeon of `P'`. Then the number `N` of points where the form takes its
value satisfies `N ^ 2 (|P'| + 1) ≤ 8 |Dom| ^ 2`, that is `N ≤ sqrt 8 |Dom| / sqrt (|P'|+1)`.
With `T i = F` for all `i`, `|Dom| = |F| ^ |P|` (`card_Dom`). -/
theorem lof (q : ι × Fin l → Bool) (P P' : Finset ι) (hPP : P' ⊆ P)
    (T : ι → Finset (Fin l → Bool)) (M : ℕ) (hl : 2 ≤ l) (hM : 3 * 2 ^ l ≤ 4 * M)
    (hTM : ∀ i ∈ P', (T i).card = M)
    (e : QEq (ι × Fin l)) (he : ∀ i ∈ P', ∃ b, e.1 (i, b) ≠ 0) :
    ((Dom q P T).filter fun y => QEq.Holds y e).card ^ 2 * (P'.card + 1) ≤
      8 * (Dom q P T).card ^ 2 := by
  set X := Dom q P T
  set N := (X.filter fun y => QEq.Holds y e).card
  rcases P'.eq_empty_or_nonempty with h0 | ⟨i0, hi0⟩
  · rw [h0, Finset.card_empty]
    have : N ≤ X.card := Finset.card_filter_le _ _
    nlinarith
  have hMl : M ≤ 2 ^ l := by
    rw [← hTM i0 hi0]
    calc (T i0).card ≤ (Finset.univ : Finset (Fin l → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ l := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
  have hp1 : 2 ^ l = 2 * 2 ^ (l - 1) := by rw [← pow_succ']; congr 1; omega
  have hp2 : 2 ^ (l - 1) = 2 * 2 ^ (l - 2) := by rw [← pow_succ']; congr 1; omega
  set r := 2 ^ (l - 2)
  have hr : ∀ i ∈ P', r + 2 ^ (l - 1) ≤ (T i).card := by
    intro i hi; rw [hTM i hi]; omega
  let β : ι → Fin l := fun i =>
    if h : ∃ b, e.1 (i, b) ≠ 0 then h.choose else ⟨0, by omega⟩
  have hβ : ∀ i ∈ P', e.1 (i, β i) ≠ 0 := by
    intro i hi
    have h := he i hi
    simp only [β, dif_pos h]
    exact h.choose_spec
  have hQex : ∀ i, ∃ Q : Finset (Fin l → Bool), i ∈ P' →
      Q ⊆ T i ∧ Q.card = 2 * r ∧ ∀ h ∈ Q, ∀ v, Function.update h (β i) v ∈ Q := by
    intro i
    by_cases hi : i ∈ P'
    · obtain ⟨Q, h1, h2, h3⟩ := exists_pairs (T i) (β i) r (hr i hi)
      exact ⟨Q, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Q hQ using hQex
  have hcore := lof_core q P P' hPP T Q β (2 * r) M (by omega)
    (fun i hi => (hQ i hi).1) (fun i hi => (hQ i hi).2.1) hTM (fun i hi => (hQ i hi).2.2) e hβ
  have hpos : 0 < 2 * r := by positivity
  have h8 : 4 * M * X.card ^ 2 ≤ (8 * X.card ^ 2) * (2 * r) := by
    have : 4 * M ≤ 8 * (2 * r) := by omega
    calc 4 * M * X.card ^ 2 ≤ 8 * (2 * r) * X.card ^ 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have := hcore.trans h8
  rw [← mul_assoc] at this
  exact Nat.le_of_mul_le_mul_right this hpos

end PEqualNP.Search.Helpers.Tree
