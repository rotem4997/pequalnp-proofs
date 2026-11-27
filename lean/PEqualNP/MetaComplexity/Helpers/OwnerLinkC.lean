import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkC2

/-!
# The owner link, clause (c): `PlacedEdges` gives `GOwnC`

Conjecture until a seat's checker accepts a row. Under `PlacedEdges`, the edges of `S` are the
thread edges of the calls, so (c1) is `ownC_c1_vals` (part 1). For (c2) a squeeze: every edge
is owned, so the edge count is at most the tail sum; the tail sum is at most `(2k + 1)` per call
(`ownC_tl_le`, part 2); and the calls times the `2k + 1` thread positions inject into the edges
(`ownC_edge_inj`), the call pairs being distinct by `PlacedEdges`.
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

theorem ownC_Xf_inj {E k u v u' v' t t' : ℕ} (hv : v < 3 * (E + 1)) (hv' : v' < 3 * (E + 1))
    (ht : 1 ≤ t) (ht2 : t ≤ 2 * k) (ht' : 1 ≤ t') (ht2' : t' ≤ 2 * k)
    (h : Xf E k u v t = Xf E k u' v' t') : u = u' ∧ v = v' ∧ t = t' := by
  unfold Xf at h
  generalize hN : 3 * (E + 1) = N at *
  have hb : 2 * k * (u * N + v) + (t - 1) = 2 * k * (u' * N + v') + (t' - 1) := by omega
  have hq : u * N + v = u' * N + v' := by
    have h1 : (2 * k * (u * N + v) + (t - 1)) / (2 * k) = u * N + v := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    have h2 : (2 * k * (u' * N + v') + (t' - 1)) / (2 * k) = u' * N + v' := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    rw [← h1, ← h2, hb]
  have hu : u = u' := by
    have h1 : (u * N + v) / N = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have h2 : (u' * N + v') / N = u' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv', Nat.zero_add]
    rw [← h1, ← h2, hq]
  subst hu
  have hvv : v = v' := by omega
  subst hvv
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- Node `p` of the thread of `(u, v)`: `u`, then the `2k` inner vertices, then `v`. -/
def ownC_nd (E k u v p : ℕ) : ℕ := if p = 0 then u else if p ≤ 2 * k then Xf E k u v p else v

theorem ownC_nd_tr {E k u v p : ℕ} (hk : 1 ≤ k) (hp : p ≤ 2 * k) :
    ownC_TR E k u v (ownC_nd E k u v p) (ownC_nd E k u v (p + 1)) ∨
      ownC_TR E k u v (ownC_nd E k u v (p + 1)) (ownC_nd E k u v p) := by
  unfold ownC_nd
  by_cases h0 : p = 0
  · subst h0
    rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    right; exact ⟨0, by omega, by unfold Xf; omega, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases h2 : p < 2 * k
    · rw [if_neg h0, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      left
      exact ⟨p - 1, by omega, by unfold Xf; omega, Or.inr (Or.inl ⟨by omega, by unfold Xf; omega⟩)⟩
    · rw [if_neg h0, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      left
      exact ⟨2 * k - 1, by omega, by unfold Xf; omega, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩

theorem ownC_nd_max {E k u v p : ℕ} (hk : 1 ≤ k) (hu : u < 3 * (E + 1)) (hv : v < 3 * (E + 1))
    (hp : p ≤ 2 * k) :
    max (ownC_nd E k u v p) (ownC_nd E k u v (p + 1)) = Xf E k u v (min (p + 1) (2 * k)) := by
  unfold ownC_nd
  by_cases h0 : p = 0
  · subst h0
    rw [if_pos rfl, if_neg (by omega), if_pos (by omega), show min (0 + 1) (2 * k) = 1 by omega]
    exact max_eq_right (by unfold Xf; omega)
  · by_cases h2 : p < 2 * k
    · rw [if_neg h0, if_pos (by omega), if_neg (by omega), if_pos (by omega),
        show min (p + 1) (2 * k) = p + 1 by omega]
      exact max_eq_right (by unfold Xf; omega)
    · rw [if_neg h0, if_pos (by omega), if_neg (by omega), if_neg (by omega),
        show min (p + 1) (2 * k) = p by omega]
      exact max_eq_left (by unfold Xf; omega)

theorem ownC_edge_inj {E k u v u' v' p p' : ℕ} (hk : 1 ≤ k) (hu : u < 3 * (E + 1))
    (hv : v < 3 * (E + 1)) (hu' : u' < 3 * (E + 1)) (hv' : v' < 3 * (E + 1)) (hp : p ≤ 2 * k)
    (hp' : p' ≤ 2 * k)
    (h : s(ownC_nd E k u v p, ownC_nd E k u v (p + 1)) =
      s(ownC_nd E k u' v' p', ownC_nd E k u' v' (p' + 1))) : u = u' ∧ v = v' ∧ p = p' := by
  have hm : max (ownC_nd E k u v p) (ownC_nd E k u v (p + 1)) =
      max (ownC_nd E k u' v' p') (ownC_nd E k u' v' (p' + 1)) := by
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, max_comm]
  rw [ownC_nd_max hk hu hv hp, ownC_nd_max hk hu' hv' hp'] at hm
  obtain ⟨rfl, rfl, ht⟩ := ownC_Xf_inj hv hv' (by omega) (by omega) (by omega) (by omega) hm
  refine ⟨rfl, rfl, ?_⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · unfold ownC_nd Xf at h1 h2
    split_ifs at h1 h2 <;> omega

theorem ownC_TR_lt {E k u v x y : ℕ} (hu : u < 3 * (E + 1)) (hv : v < 3 * (E + 1))
    (h : ownC_TR E k u v x y) :
    x < 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) ∧
      y < 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by
  obtain ⟨i, hi, rfl, hy⟩ := h
  have hx := Xf_lt (k := k) hu hv (t := i + 1) (by omega) (by omega)
  unfold Xf at hx
  refine ⟨by omega, ?_⟩
  rcases hy with ⟨-, rfl⟩ | ⟨hi1, rfl⟩ | ⟨-, rfl⟩
  · omega
  · have := Xf_lt (k := k) hu hv (t := i + 2) (by omega) (by omega)
    unfold Xf at this; omega
  · omega

theorem ownC_TR_ne {E k u v x y : ℕ} (hu : u < 3 * (E + 1)) (hv : v < 3 * (E + 1))
    (h : ownC_TR E k u v x y) : x ≠ y := by
  obtain ⟨i, hi, rfl, hy⟩ := h
  rcases hy with ⟨-, rfl⟩ | ⟨hi1, rfl⟩ | ⟨-, rfl⟩ <;> omega

/-- Clause (c) of the owner link, from `PlacedEdges`. -/
theorem gOwnC_of_placed (h : PlacedEdges) : GOwnC := by
  intro φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT S hS F hF ol hol
  obtain ⟨hnd, hbd, hadj, -⟩ := h φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT
  have hFirst := ownC_first_ren φ
  have hSadj : ∀ x y : Fin (3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1))), S.Adj x y ↔
      ∃ c ∈ callsF E (REN φ), ownC_TR E k c.1 c.2.1 x.val y.val ∨
        ownC_TR E k c.1 c.2.1 y.val x.val := by
    subst hS
    intro x y
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, ⟨u, v, huv, hadjuv, i, hx, hy⟩ | ⟨u, v, huv, hadjuv, i, hx, hy⟩⟩
      · obtain ⟨t, ht⟩ := (hadj u v huv).mp hadjuv
        exact ⟨_, ht, Or.inl ⟨i.val, i.isLt, hx, hy⟩⟩
      · obtain ⟨t, ht⟩ := (hadj u v huv).mp hadjuv
        exact ⟨_, ht, Or.inr ⟨i.val, i.isLt, hx, hy⟩⟩
    · rintro ⟨c, hc, hxy | hxy⟩
      · obtain ⟨hlt, hlt2⟩ := hbd c hc
        have hne := ownC_TR_ne (by omega) hlt2 hxy
        obtain ⟨i, hi, hx, hy⟩ := hxy
        exact ⟨fun heq => hne (congrArg Fin.val heq),
          Or.inl ⟨⟨c.1, by omega⟩, ⟨c.2.1, hlt2⟩, Fin.mk_lt_mk.mpr hlt,
            (hadj _ _ (Fin.mk_lt_mk.mpr hlt)).mpr ⟨c.2.2, hc⟩, ⟨i, hi⟩, hx, hy⟩⟩
      · obtain ⟨hlt, hlt2⟩ := hbd c hc
        have hne := ownC_TR_ne (by omega) hlt2 hxy
        obtain ⟨i, hi, hx, hy⟩ := hxy
        exact ⟨fun heq => hne (congrArg Fin.val heq.symm),
          Or.inr ⟨⟨c.1, by omega⟩, ⟨c.2.1, hlt2⟩, Fin.mk_lt_mk.mpr hlt,
            (hadj _ _ (Fin.mk_lt_mk.mpr hlt)).mpr ⟨c.2.2, hc⟩, ⟨i, hi⟩, hx, hy⟩⟩
  subst hol
  refine ⟨fun x y => ?_, ?_⟩
  · rw [hSadj, ownC_c1_vals hk hFirst x.val y.val, ← OWN_eq]
    unfold ownC_Own
    constructor
    · rintro (⟨l, hl, h1, h2⟩ | ⟨l, hl, h1, h2⟩)
      · exact ⟨l, hl, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨l, hl, Or.inr ⟨h1, h2⟩⟩
    · rintro ⟨l, hl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact Or.inl ⟨l, hl, h1, h2⟩
      · exact Or.inr ⟨l, hl, h1, h2⟩
  · have htl : ((OWN E k (REN φ)).map (fun l : List ℕ => l.tail.length)).sum =
        ownC_tl (OWN' E k (REN φ)) := by rw [OWN_eq]; rfl
    rw [htl]
    set E' : Set (Sym2 ℕ) := (Sym2.map Fin.val) '' S.edgeSet with hE'
    have hEc : E'.ncard = S.edgeSet.ncard :=
      Set.ncard_image_of_injective _ (Sym2.map.injective Fin.val_injective)
    have hEfin : E'.Finite := (Set.toFinite _).image _
    have hedge : ∀ c ∈ callsF E (REN φ), ∀ a b, ownC_TR E k c.1 c.2.1 a b → s(a, b) ∈ E' := by
      intro c hc a b hab
      obtain ⟨hlt, hlt2⟩ := hbd c hc
      obtain ⟨ha, hb⟩ := ownC_TR_lt (by omega) hlt2 hab
      have hadj' := (hSadj ⟨a, ha⟩ ⟨b, hb⟩).mpr ⟨c, hc, Or.inl hab⟩
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), (SimpleGraph.mem_edgeSet S).mpr hadj', by simp⟩
    rw [← hEc]
    apply le_antisymm
    · -- the tails are at most (2k + 1) per call, and calls times positions inject into edges
      refine (ownC_tl_le E k (REN φ)).trans ?_
      set P := (callsF E (REN φ)).map (fun c : ℕ × ℕ × Bool => (c.1, c.2.1)) with hP
      set D := P.toFinset ×ˢ Finset.range (2 * k + 1) with hD
      have hDc : D.card = (2 * k + 1) * (callsF E (REN φ)).length := by
        rw [hD, Finset.card_product, List.toFinset_card_of_nodup hnd, hP, List.length_map,
          Finset.card_range, Nat.mul_comm]
      have hmemD : ∀ q ∈ D, ∃ c ∈ callsF E (REN φ), c.1 = q.1.1 ∧ c.2.1 = q.1.2 ∧
          q.2 ≤ 2 * k := by
        intro q hq
        rw [hD, Finset.mem_product, List.mem_toFinset, hP, List.mem_map, Finset.mem_range] at hq
        obtain ⟨⟨c, hc, hcq⟩, hq2⟩ := hq
        exact ⟨c, hc, by rw [← hcq], by rw [← hcq], by omega⟩
      rw [← hDc, ← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard_of_injOn
        (fun q : (ℕ × ℕ) × ℕ => s(ownC_nd E k q.1.1 q.1.2 q.2, ownC_nd E k q.1.1 q.1.2 (q.2 + 1)))
        ?_ ?_ hEfin
      · intro q hq
        obtain ⟨c, hc, hc1, hc2, hq2⟩ := hmemD q hq
        rcases ownC_nd_tr (u := q.1.1) (v := q.1.2) hk hq2 with hab | hab
        · rw [← hc1, ← hc2] at hab ⊢; exact hedge c hc _ _ hab
        · rw [← hc1, ← hc2] at hab ⊢; rw [Sym2.eq_swap]; exact hedge c hc _ _ hab
      · intro q hq q' hq' hqq
        obtain ⟨c, hc, hc1, hc2, hq2⟩ := hmemD q hq
        obtain ⟨c', hc', hc1', hc2', hq2'⟩ := hmemD q' hq'
        obtain ⟨hl, hl2⟩ := hbd c hc
        obtain ⟨hl', hl2'⟩ := hbd c' hc'
        obtain ⟨e1, e2, e3⟩ := ownC_edge_inj hk (by omega) (by omega) (by omega) (by omega)
          hq2 hq2' hqq
        obtain ⟨⟨a, b⟩, p⟩ := q
        obtain ⟨⟨a', b'⟩, p'⟩ := q'
        simp only at e1 e2 e3
        subst e1; subst e2; subst e3; rfl
    · -- every edge is owned
      set Q : List (Sym2 ℕ) := (OWN' E k (REN φ)).flatMap
        (fun l => l.tail.map (fun y => s(l.headD 0, y))) with hQ
      have hQl : Q.length = ownC_tl (OWN' E k (REN φ)) := by
        rw [hQ, List.length_flatMap]
        simp [ownC_tl]
      have hsub : E' ⊆ ↑Q.toFinset := by
        rintro z ⟨e, he, rfl⟩
        induction e using Sym2.ind with
        | h x y =>
          have hxy := (hSadj x y).mp ((SimpleGraph.mem_edgeSet S).mp he)
          rw [ownC_c1_vals hk hFirst x.val y.val] at hxy
          simp only [Sym2.map_mk, Finset.mem_coe, List.mem_toFinset, hQ, List.mem_flatMap,
            List.mem_map]
          rcases hxy with ⟨l, hl, h1, h2⟩ | ⟨l, hl, h1, h2⟩
          · exact ⟨l, hl, y.val, h2, by rw [h1]⟩
          · exact ⟨l, hl, x.val, h2, by rw [h1, Sym2.eq_swap]⟩
      calc E'.ncard ≤ (↑Q.toFinset : Set (Sym2 ℕ)).ncard := Set.ncard_le_ncard hsub
        _ = Q.toFinset.card := Set.ncard_coe_finset _
        _ ≤ Q.length := List.toFinset_card_le _
        _ = ownC_tl (OWN' E k (REN φ)) := hQl

end PEqualNP.MetaComplexity.Helpers.OwnerLink
