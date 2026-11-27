import Mathlib
import PEqualNP.MetaComplexity.Helpers.SubdivPlan

/-!
# The forward cover map and its private edges (pieces S5 and S8; rows L-meta-288, L-meta-291)

For a vertex cover `T` of `H`, `fwd k H T` (the hubs of `T`, and on each live slot `(u, v)` the
positions `t = i + 1` with `t` even iff `u ∈ T`) is a vertex cover of `subdiv k H` with
`|T| + k |E(H)|` vertices (`stmtS5_proof`), and if every member of `T` has a private edge, so does
every member of `fwd k H T` (`stmtS8_proof`). The filed rows follow through the bridge
(`rowL288_proof`, `rowL291_proof`).
-/

namespace PEqualNP.MetaComplexity.Subdiv.Fwd

open PEqualNP.MetaComplexity.Subdiv

/-- The live slots: pairs `(u, v)` with `u < v` and `H.Adj u v`. -/
def liveSlots {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)

/-- The number of live slots is the number of edges of `H`. -/
theorem liveSlots_card {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    (liveSlots H).card = H.edgeSet.ncard := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [liveSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa using hp.2
  · intro p hp q hq h
    simp only [liveSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd hq.1 (by rw [← h1, ← h2]; exact not_lt.2 hp.1.le)
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases lt_trichotomy a b with hab | hab | hab
      · exact ⟨(a, b), by simp [liveSlots, hab, he], rfl⟩
      · exact absurd hab he.ne
      · exact ⟨(b, a), by simp [liveSlots, hab, he.symm], Sym2.eq_swap⟩

/-- An inner index of a live slot with the wrong parity is not in the forward cover. -/
theorem not_mem_fwd {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m))
    (u v : Fin m) (i : ℕ) (hi : i < 2 * k) (j : Fin (nS m k))
    (hj : j.val = m + 2 * k * (u.val * m + v.val) + i) (hpar : ¬ (i % 2 = 1 ↔ u ∈ T)) :
    j ∉ fwd k H T := by
  rw [fwd_char]
  rintro (⟨w, -, hw⟩ | ⟨u', v', i', -, -, hj', hpar'⟩)
  · have := w.2; omega
  · obtain ⟨rfl, -, rfl⟩ := thr_inj hi i'.2 (hj.symm.trans hj')
    exact hpar hpar'

theorem mem_fwd_inner {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m))
    (u v : Fin m) (huv : u < v) (hadj : H.Adj u v) (i : ℕ) (hi : i < 2 * k) (j : Fin (nS m k))
    (hj : j.val = m + 2 * k * (u.val * m + v.val) + i) (hpar : i % 2 = 1 ↔ u ∈ T) :
    j ∈ fwd k H T := by
  rw [fwd_char]
  exact Or.inr ⟨u, v, ⟨i, hi⟩, huv, hadj, hj, hpar⟩

theorem mem_fwd_hub {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m))
    (u : Fin m) (hu : u ∈ T) (j : Fin (nS m k)) (hj : j.val = u.val) : j ∈ fwd k H T := by
  rw [fwd_char]
  exact Or.inl ⟨u, hu, hj⟩

/-- One thread step has an end in the forward cover. -/
theorem subRel_cover {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m))
    (hT : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) (x y : Fin (nS m k)) (h : SubRel k H x y) :
    x ∈ fwd k H T ∨ y ∈ fwd k H T := by
  obtain ⟨u, v, huv, hadj, p, hx, hy⟩ := h
  have hp := p.2
  by_cases huT : u ∈ T
  · by_cases hp0 : p.val = 0
    · rw [if_pos hp0] at hx
      exact Or.inl (mem_fwd_hub H T u huT x hx)
    rw [if_neg hp0] at hx
    rcases Nat.even_or_odd p.val with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine Or.inl (mem_fwd_inner H T u v huv hadj (p.val - 1) (by omega) x (by omega) ?_)
      simp only [huT, iff_true]; omega
    · rw [if_neg (by omega)] at hy
      refine Or.inr (mem_fwd_inner H T u v huv hadj p.val (by omega) y hy ?_)
      simp only [huT, iff_true]; omega
  · have hvT : v ∈ T := (hT u v hadj).resolve_left huT
    rcases Nat.even_or_odd p.val with ⟨r, hr⟩ | ⟨r, hr⟩
    · by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at hy
        exact Or.inr (mem_fwd_hub H T v hvT y hy)
      rw [if_neg hp2] at hy
      refine Or.inr (mem_fwd_inner H T u v huv hadj p.val (by omega) y hy ?_)
      simp only [huT, iff_false]; omega
    · rw [if_neg (by omega)] at hx
      refine Or.inl (mem_fwd_inner H T u v huv hadj (p.val - 1) (by omega) x (by omega) ?_)
      simp only [huT, iff_false]; omega

/-- The parity bit of the forward cover on slots with lower end `u`. -/
def bit {m : ℕ} (T : Finset (Fin m)) (u : Fin m) : ℕ := if u ∈ T then 1 else 0

/-- The inner part of the forward cover, as an image. -/
def innerMap {m : ℕ} (k : ℕ) (T : Finset (Fin m)) (q : (Fin m × Fin m) × ℕ) : ℕ :=
  m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2 + bit T q.1.1)

theorem fwd_card {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m)) :
    (fwd k H T).card = T.card + k * H.edgeSet.ncard := by
  classical
  -- work with the values
  have hval : (fwd k H T).card = ((fwd k H T).image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  have hset : (fwd k H T).image Fin.val =
      T.image Fin.val ∪ ((liveSlots H ×ˢ Finset.range k).image (innerMap k T)) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_product, Finset.mem_range,
      liveSlots, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [fwd_char] at hj
      rcases hj with ⟨u, hu, hju⟩ | ⟨u, v, i, huv, hadj, hji, hpar⟩
      · exact Or.inl ⟨u, hu, hju.symm⟩
      · refine Or.inr ⟨((u, v), i.val / 2), ⟨⟨huv, hadj⟩, ?_⟩, ?_⟩
        · have := i.2; omega
        · simp only [innerMap, bit, hji]
          have := Nat.div_add_mod i.val 2
          split_ifs at hpar ⊢ with h
          · have := hpar.2 h; omega
          · have : ¬ i.val % 2 = 1 := fun h' => h (hpar.1 h')
            omega
    · rintro (⟨u, hu, rfl⟩ | ⟨⟨⟨u, v⟩, s⟩, ⟨⟨huv, hadj⟩, hs⟩, rfl⟩)
      · refine ⟨⟨u.val, ?_⟩, mem_fwd_hub H T u hu _ rfl, rfl⟩
        have := u.2; unfold nS; omega
      · have hb : bit T u ≤ 1 := by unfold bit; split_ifs <;> omega
        have hi : 2 * s + bit T u < 2 * k := by omega
        refine ⟨⟨innerMap k T ((u, v), s), thr_lt u v hi⟩, ?_, rfl⟩
        refine mem_fwd_inner H T u v huv hadj _ hi _ rfl ?_
        simp only [bit]
        split_ifs with h
        · simp only [h, iff_true]; omega
        · simp only [h, iff_false]; omega
  have hdisj : Disjoint (T.image Fin.val)
      ((liveSlots H ×ˢ Finset.range k).image (innerMap k T)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_image] at hn hn'
    obtain ⟨u, -, rfl⟩ := hn
    obtain ⟨q, -, hq⟩ := hn'
    have := u.2
    simp only [innerMap] at hq
    omega
  have hinj : Set.InjOn (innerMap k T) ↑(liveSlots H ×ˢ Finset.range k) := by
    rintro ⟨⟨u, v⟩, s⟩ hq ⟨⟨u', v'⟩, s'⟩ hq' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hq hq'
    simp only [innerMap] at h
    have hb : bit T u ≤ 1 := by unfold bit; split_ifs <;> omega
    have hb' : bit T u' ≤ 1 := by unfold bit; split_ifs <;> omega
    obtain ⟨rfl, rfl, h3⟩ := thr_inj (k := k) (by omega) (by omega) h
    have : s = s' := by omega
    subst this; rfl
  rw [hval, hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Fin.val_injective, Finset.card_image_of_injOn hinj,
    Finset.card_product, Finset.card_range, liveSlots_card, Nat.mul_comm]

/-- S5: the forward cover is a cover with `|T| + k |E(H)|` vertices. -/
theorem stmtS5_proof : StmtS5 := by
  intro k m H _ T _hk hT
  refine ⟨fun x y hxy => ?_, fwd_card H T⟩
  rcases hxy.2 with h | h
  · exact subRel_cover H T hT x y h
  · exact (subRel_cover H T hT y x h).symm

/-- S8: the forward cover of a cover with a private edge at every member has a private edge at
every member. -/
theorem stmtS8_proof : StmtS8 := by
  intro k m H _ T hk hT hmin x hx
  have hk2 : 2 ≤ 2 * k := by omega
  rw [fwd_char] at hx
  rcases hx with ⟨u, hu, hxu⟩ | ⟨u, v, i, huv, hadj, hxi, hpar⟩
  · -- a hub of `T`, with private edge `u w`
    obtain ⟨w, huw, hw⟩ := hmin u hu
    rcases lt_or_gt_of_ne huw.ne with hlt | hgt
    · -- slot `(u, w)`, first inner vertex (offset 0, position 1, odd)
      refine ⟨⟨m + 2 * k * (u.val * m + w.val) + 0, thr_lt u w (by omega)⟩, ?_, ?_⟩
      · rw [hub_adj_iff H hk x _ (by have := u.2; omega)]
        exact ⟨u, w, hlt, huw, Or.inl ⟨hxu.symm, rfl⟩⟩
      · refine not_mem_fwd H T u w 0 (by omega) _ rfl ?_
        simp [hu]
    · -- slot `(w, u)`, last inner vertex (offset 2k - 1, odd), `w ∉ T`
      refine ⟨⟨m + 2 * k * (w.val * m + u.val) + (2 * k - 1), thr_lt w u (by omega)⟩, ?_, ?_⟩
      · rw [hub_adj_iff H hk x _ (by have := u.2; omega)]
        exact ⟨w, u, hgt, huw.symm, Or.inr ⟨hxu.symm, rfl⟩⟩
      · refine not_mem_fwd H T w u (2 * k - 1) (by omega) _ rfl ?_
        simp only [hw, iff_false]; omega
  · have hi := i.2
    by_cases hup : i.val + 1 < 2 * k
    · refine ⟨⟨x.val + 1, by have := thr_lt (k := k) u v (i := i.val + 1) hup; omega⟩, ?_, ?_⟩
      · rw [inner_adj_iff H u v i x _ hxi]
        refine ⟨⟨huv, hadj⟩, Or.inr ?_⟩
        rw [if_neg (by omega)]
      · refine not_mem_fwd H T u v (i.val + 1) hup _ (by simp only; omega) ?_
        intro h; apply (show ¬ (i.val % 2 = 1 ↔ (i.val + 1) % 2 = 1) by omega)
        exact hpar.trans h.symm
    · refine ⟨⟨x.val - 1, by omega⟩, ?_, ?_⟩
      · rw [inner_adj_iff H u v i x _ hxi]
        refine ⟨⟨huv, hadj⟩, Or.inl ?_⟩
        rw [if_neg (by omega)]
      · refine not_mem_fwd H T u v (i.val - 1) (by omega) _ (by simp only; omega) ?_
        intro h; apply (show ¬ (i.val % 2 = 1 ↔ (i.val - 1) % 2 = 1) by omega)
        exact hpar.trans h.symm

/-- L-meta-288 (forward cover map), as filed. -/
theorem rowL288_proof : RowL288 := by
  intro k m H T hk hT S hS F hF
  classical
  have hS' : S = subdiv k H := hS.trans (Bridge.graph_eq H hk)
  have hF' : F = fwd k H T := Finset.ext fun j => (hF j).trans (fwd_char H T j).symm
  subst hS' hF'
  exact stmtS5_proof k m H T hk hT

/-- L-meta-291 (private edges of the forward cover of a minimal cover), as filed. -/
theorem rowL291_proof : RowL291 := by
  intro k m H T hk hT hmin S hS F hF
  classical
  have hS' : S = subdiv k H := hS.trans (Bridge.graph_eq H hk)
  have hF' : F = fwd k H T := Finset.ext fun j => (hF j).trans (fwd_char H T j).symm
  subst hS' hF'
  exact stmtS8_proof k m H T hk hT hmin

end PEqualNP.MetaComplexity.Subdiv.Fwd
