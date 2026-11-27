import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_539_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Library.Subdivision

/-! ### Section 1: Graph and Subdivision Lemmas -/

private lemma subRel_cases {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 3 ≤ k)
    {x y : Fin (nS m k)} (h : SubRel k H x y) :
    (x.val < m ∧ m ≤ y.val ∧ (y.val - m) % (2 * k) = 0) ∨
    (m ≤ x.val ∧ y.val < m ∧ (x.val - m) % (2 * k) = 2 * k - 1) ∨
    (m ≤ x.val ∧ m ≤ y.val ∧ y.val = x.val + 1 ∧ (x.val - m) % (2 * k) + 1 < 2 * k) := by
  obtain ⟨u, v, _, _, p, hx, hy⟩ := h
  by_cases hp0 : p.val = 0
  · left
    rw [if_pos hp0] at hx
    have hp2k : p.val ≠ 2 * k := by omega
    rw [if_neg hp2k] at hy
    refine ⟨hx ▸ u.isLt, by omega, ?_⟩
    have hsub : y.val - m = 2 * k * (u.val * m + v.val) := by omega
    rw [hsub]
    exact Nat.mul_mod_right (2 * k) (u.val * m + v.val)
  · by_cases hp2k : p.val = 2 * k
    · right; left
      rw [if_neg hp0] at hx
      rw [if_pos hp2k] at hy
      refine ⟨by omega, hy ▸ v.isLt, ?_⟩
      have hsub : x.val - m = 2 * k * (u.val * m + v.val) + (2 * k - 1) := by omega
      rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    · right; right
      rw [if_neg hp0] at hx
      rw [if_neg hp2k] at hy
      have hplt : p.val < 2 * k := by have := p.isLt; omega
      have hsub : x.val - m = 2 * k * (u.val * m + v.val) + (p.val - 1) := by omega
      have hmod : (x.val - m) % (2 * k) = p.val - 1 := by
        rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      refine ⟨by omega, by omega, by omega, by omega⟩

private lemma subdiv_adj_hub_inner {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 3 ≤ k)
    {c x : Fin (nS m k)} (hadj : (subdiv k H).Adj c x) (hc : c.val < m) :
    m ≤ x.val ∧ ((x.val - m) % (2 * k) = 0 ∨ (x.val - m) % (2 * k) = 2 * k - 1) := by
  rcases hadj.2 with h | h
  · rcases subRel_cases hk h with ⟨_, hxm, hm0⟩ | ⟨hcm, _, _⟩ | ⟨hcm, _, _, _⟩
    · exact ⟨hxm, Or.inl hm0⟩
    · omega
    · omega
  · rcases subRel_cases hk h with ⟨_, hcm, _⟩ | ⟨hxm, _, hm1⟩ | ⟨_, hcm, _, _⟩
    · omega
    · exact ⟨hxm, Or.inr hm1⟩
    · omega

private lemma subdiv_adj_inner_inner {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 3 ≤ k)
    {a b : Fin (nS m k)} (hadj : (subdiv k H).Adj a b) (ha : m ≤ a.val) (hb : m ≤ b.val) :
    (b.val = a.val + 1 ∧ (a.val - m) % (2 * k) + 1 < 2 * k) ∨
    (a.val = b.val + 1 ∧ (b.val - m) % (2 * k) + 1 < 2 * k) := by
  rcases hadj.2 with h | h
  · rcases subRel_cases hk h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3, h4⟩
    · omega
    · omega
    · exact Or.inl ⟨h3, h4⟩
  · rcases subRel_cases hk h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3, h4⟩
    · omega
    · omega
    · exact Or.inr ⟨h3, h4⟩

private lemma subdiv_triangle_free_core {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 3 ≤ k)
    (a b c : Fin (nS m k))
    (hab : (subdiv k H).Adj a b) (hbc : (subdiv k H).Adj b c) (hca : (subdiv k H).Adj c a) :
    False := by
  have hub_inner_pair : ∀ (x y z : Fin (nS m k)),
      x.val < m → (subdiv k H).Adj x y → (subdiv k H).Adj x z → (subdiv k H).Adj y z → False := by
    intro x y z hx hxy hxz hyz
    obtain ⟨hy, hmy⟩ := subdiv_adj_hub_inner hk hxy hx
    obtain ⟨hz, hmz⟩ := subdiv_adj_hub_inner hk hxz hx
    have step : ∀ (u v : Fin (nS m k)), m ≤ u.val → m ≤ v.val →
        v.val = u.val + 1 → (u.val - m) % (2 * k) + 1 < 2 * k →
        ((u.val - m) % (2 * k) = 0 ∨ (u.val - m) % (2 * k) = 2 * k - 1) →
        ((v.val - m) % (2 * k) = 0 ∨ (v.val - m) % (2 * k) = 2 * k - 1) → False := by
      intro u v hu hv hvu hlt hmu hmv
      have hu0 : (u.val - m) % (2 * k) = 0 := by omega
      have hvm : (v.val - m) % (2 * k) = 1 := by
        have hv1 : v.val - m = (u.val - m) + 1 := by omega
        rw [hv1, Nat.add_mod, hu0]
        simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * k)]
      omega
    rcases subdiv_adj_inner_inner hk hyz hy hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact step y z hy hz h1 h2 hmy hmz
    · exact step z y hz hy h1 h2 hmz hmy
  by_cases ha : a.val < m
  · exact hub_inner_pair a b c ha hab hca.symm hbc
  · by_cases hb : b.val < m
    · exact hub_inner_pair b a c hb hab.symm hbc hca.symm
    · by_cases hc : c.val < m
      · exact hub_inner_pair c a b hc hca hbc.symm hab
      · have h1 := subdiv_adj_inner_inner hk hab (by omega) (by omega)
        have h2 := subdiv_adj_inner_inner hk hbc (by omega) (by omega)
        have h3 := subdiv_adj_inner_inner hk hca (by omega) (by omega)
        omega

private lemma triangle_free_of_subdiv {n k m : ℕ} {K : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hk : 3 ≤ k) (hemb : Nonempty (K.Adj ↪r (subdiv k H).Adj))
    (a b c : Fin n) (hab : K.Adj a b) (hbc : K.Adj b c) (hca : K.Adj c a) : False := by
  obtain ⟨f⟩ := hemb
  exact subdiv_triangle_free_core hk (f a) (f b) (f c)
    (f.map_rel_iff.mpr hab) (f.map_rel_iff.mpr hbc) (f.map_rel_iff.mpr hca)

private lemma exists_minCover {n : ℕ} (K : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), IsMinCover K T := by
  classical
  let S : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T => K.IsVertexCover (T : Set (Fin n)))
  have hne : S.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image S Finset.card hne
  exact ⟨T, (Finset.mem_filter.mp hT).2, fun T' hT' =>
    hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩

private lemma exists_neighbor_of_free_leaf {n : ℕ} {K : SimpleGraph (Fin n)} {l p : Fin n}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T) :
    ∃ q : Fin n, q ≠ l ∧ K.Adj p q := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨T, hT⟩ := exists_minCover K
  have hlT : l ∉ T := hfree T hT
  have hpT : p ∈ T := by
    rcases hT.1 ((hlp p).mpr rfl) with hl | hp
    · exact absurd hl hlT
    · exact hp
  let T' : Finset (Fin n) := insert l (T.erase p)
  have hcov : K.IsVertexCover (T' : Set (Fin n)) := by
    intro u v huv
    by_cases hup : u = p
    · subst hup
      have hvl : v = l := by
        by_contra hne
        exact hno v hne huv
      subst hvl
      exact Or.inr (Finset.mem_insert_self _ _)
    · by_cases hvp : v = p
      · subst hvp
        have hul : u = l := by
          by_contra hne
          exact hno u hne huv.symm
        subst hul
        exact Or.inl (Finset.mem_insert_self _ _)
      · rcases hT.1 huv with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hup, hu⟩))
        · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvp, hv⟩))
  have hcard : T'.card = T.card := by
    have hl_not : l ∉ T.erase p := fun h => hlT (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hl_not, Finset.card_erase_add_one hpT]
  have hmin' : IsMinCover K T' := ⟨hcov, fun S hS => by rw [hcard]; exact hT.2 S hS⟩
  exact hfree T' hmin' (Finset.mem_insert_self _ _)

private lemma minCover_K_to_K' {n : ℕ} {K K' : SimpleGraph (Fin n)} {l p : Fin n}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    {T : Finset (Fin n)} (hT : IsMinCover K T) : IsMinCover K' T := by
  classical
  refine ⟨fun u v huv => hT.1 ((hK' u v).mp huv).1, ?_⟩
  intro T' hT'
  by_contra hlt
  push Not at hlt
  let S' : Finset (Fin n) := insert l T'
  have hcovK : K.IsVertexCover (S' : Set (Fin n)) := by
    intro u v huv
    by_cases hul : u = l
    · subst hul; exact Or.inl (Finset.mem_insert_self _ _)
    · by_cases hvl : v = l
      · subst hvl; exact Or.inr (Finset.mem_insert_self _ _)
      · rcases hT' ((hK' u v).mpr ⟨huv, hul, hvl⟩) with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
  have hle := hT.2 S' hcovK
  have hins : S'.card ≤ T'.card + 1 := Finset.card_insert_le _ _
  have heq : S'.card = T.card := by omega
  have hmin : IsMinCover K S' := ⟨hcovK, fun S hS => by rw [heq]; exact hT.2 S hS⟩
  exact hfree S' hmin (Finset.mem_insert_self _ _)

private lemma minCover_card_eq {n : ℕ} {K K' : SimpleGraph (Fin n)} {l p : Fin n}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    {T T' : Finset (Fin n)} (hT : IsMinCover K T) (hT' : IsMinCover K' T') :
    T.card = T'.card := by
  have hTK' := minCover_K_to_K' hlp hfree hK' hT
  exact le_antisymm (hTK'.2 T' hT'.1) (hT'.2 T hTK'.1)

private lemma edgeFinset_card_K_eq {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {l p : Fin n}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l) :
    K.edgeFinset.card = K'.edgeFinset.card + 1 := by
  have hnot : s(l, p) ∉ K'.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hK']
    intro h; exact h.2.1 rfl
  have heq : K.edgeFinset = insert s(l, p) K'.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
        Sym2.eq_iff, hK']
      constructor
      · intro huv
        by_cases hul : u = l
        · subst hul
          left; left
          exact ⟨rfl, (hlp v).mp huv⟩
        · by_cases hvl : v = l
          · subst hvl
            left; right
            exact ⟨(hlp u).mp huv.symm, rfl⟩
          · exact Or.inr ⟨huv, hul, hvl⟩
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨huv, _, _⟩)
        · rw [h1, h2]; exact (hlp p).mpr rfl
        · rw [h1, h2]; exact ((hlp p).mpr rfl).symm
        · exact huv
  rw [heq, Finset.card_insert_of_notMem hnot]

private lemma exists_owned_not_in_cover {n : ℕ} {K : SimpleGraph (Fin n)} {d : NCCData n}
    (hmin : IsMinCover K d.cover) (hown : OwnerOK K d) {t : Fin n} (ht : t ∈ d.cover) :
    ∃ r : Fin n, r ∉ d.cover ∧ d.owns t r = true := by
  classical
  by_contra hno
  push Not at hno
  have hcov : K.IsVertexCover ((d.cover.erase t) : Set (Fin n)) := by
    intro u v huv
    have hne := hown.2 u v huv
    cases h1 : d.owns u v with
    | true =>
      have huT := (hown.1 u v h1).2
      by_cases hut : u = t
      · subst hut
        have hvT : v ∈ d.cover := by
          by_contra hvnot
          exact hno v hvnot h1
        exact Or.inr (Finset.mem_erase.mpr ⟨huv.ne.symm, hvT⟩)
      · exact Or.inl (Finset.mem_erase.mpr ⟨hut, huT⟩)
    | false =>
      have h2 : d.owns v u = true := by
        rw [h1] at hne
        cases h : d.owns v u with
        | true => rfl
        | false => exact absurd h.symm hne
      have hvT := (hown.1 v u h2).2
      by_cases hvt : v = t
      · subst hvt
        have huT : u ∈ d.cover := by
          by_contra hunot
          exact hno u hunot h2
        exact Or.inl (Finset.mem_erase.mpr ⟨huv.ne, huT⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hvt, hvT⟩)
  have hle := hmin.2 (d.cover.erase t) hcov
  have hcard := Finset.card_erase_add_one ht
  omega

private lemma graphFun_update_l_false {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {A : Finset (Fin n)} {l p : Fin n}
    (hA : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (x : Fin n → Bool) :
    graphFun K A (Function.update x l false) = graphFun K' A x := by
  have hlA : l ∉ A := fun h => hA l h p ((hlp p).mpr rfl)
  unfold graphFun
  congr 1
  · apply decide_eq_decide.mpr
    constructor
    · rintro ⟨a, ha, hxa⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by simpa [Function.update_of_ne hal] using hxa⟩
    · rintro ⟨a, ha, hxa⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by simpa [Function.update_of_ne hal] using hxa⟩
  · apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      have hul : u ≠ l := by rintro rfl; simp at hu
      have hvl : v ≠ l := by rintro rfl; simp at hv
      exact ⟨u, v, (hK' u v).mpr ⟨huv, hul, hvl⟩,
        by simpa [Function.update_of_ne hul] using hu,
        by simpa [Function.update_of_ne hvl] using hv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨h1, hul, hvl⟩ := (hK' u v).mp huv
      exact ⟨u, v, h1, by simpa [Function.update_of_ne hul] using hu,
        by simpa [Function.update_of_ne hvl] using hv⟩

private lemma graphFun_update_l_true {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {A : Finset (Fin n)} {l p : Fin n}
    (hA : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (x : Fin n → Bool) :
    graphFun K A (Function.update x l true) = (graphFun K' A x || x p) := by
  have hlA : l ∉ A := fun h => hA l h p ((hlp p).mpr rfl)
  have hne : l ≠ p := ((hlp p).mpr rfl).ne
  unfold graphFun
  cases h : (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, K'.Adj u v ∧ x u = true ∧ x v = true)) || x p with
  | true =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with (⟨a, ha, hxa⟩ | ⟨u, v, huv, hu, hv⟩) | hxp
    · have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hal] using hxa⟩
    · obtain ⟨h1, hul, hvl⟩ := (hK' u v).mp huv
      exact Or.inr ⟨u, v, h1, by simpa [Function.update_of_ne hul] using hu,
        by simpa [Function.update_of_ne hvl] using hv⟩
    · exact Or.inr ⟨l, p, (hlp p).mpr rfl, by simp,
        by simpa [Function.update_of_ne hne.symm] using hxp⟩
  | false =>
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h ⊢
    obtain ⟨⟨h1, h2⟩, hxp⟩ := h
    constructor
    · rintro ⟨a, ha, hxa⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact h1 ⟨a, ha, by simpa [Function.update_of_ne hal] using hxa⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases hul : u = l
      · subst hul
        have hvp : v = p := (hlp v).mp huv
        subst hvp
        rw [Function.update_of_ne hne.symm] at hv
        rw [hv] at hxp
        exact Bool.noConfusion hxp
      · by_cases hvl : v = l
        · subst hvl
          have hup : u = p := (hlp u).mp huv.symm
          subst hup
          rw [Function.update_of_ne hne.symm] at hu
          rw [hu] at hxp
          exact Bool.noConfusion hxp
        · rw [Function.update_of_ne hul] at hu
          rw [Function.update_of_ne hvl] at hv
          exact h2 ⟨u, v, (hK' u v).mpr ⟨huv, hul, hvl⟩, hu, hv⟩

/-! ### Section 2: Nested Cover Circuit Size, Evaluation, and Tie-Free Upper Bound -/

private lemma length_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    l.length = ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := h a (by simp)
    have ih' := ih (fun i hi => h i (by simp [hi]))
    simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib]
    rw [← ih']
    simp [ha]

private lemma tree_card (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ)
    (h : IsOrTree n C G L ρ) : L.card = G.card + 1 := by
  obtain ⟨hg, hl, hgg, hroot⟩ := h
  by_cases hG : G = ∅
  · rw [if_pos hG] at hroot
    rw [hroot, hG]; simp
  · rw [if_neg hG] at hroot
    obtain ⟨j0, hj0, hρ⟩ := hroot
    have hρL : ρ ∉ L := by
      intro hin
      apply (hl ρ hin).1
      rw [hρ]
      exact ⟨Nat.le_add_right _ _, by simpa using hj0⟩
    have hdisj : Disjoint L (G.image (fun k => n + k)) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw'
      apply (hl _ hw).1
      exact ⟨Nat.le_add_right _ _, by simpa using hk⟩
    have hsum : ∑ j ∈ G, (gateAt C j).inputs.length = 2 * G.card := by
      rw [Finset.sum_congr rfl (fun j hj => (hg j hj).2.1)]
      simp [Nat.mul_comm]
    have hlen : ∀ j ∈ G, (gateAt C j).inputs.length =
        ∑ w ∈ L ∪ G.image (fun k => n + k), (gateAt C j).inputs.count w := by
      intro j hj
      apply length_eq_sum_count
      intro i hi
      rcases (hg j hj).2.2 i hi with h1 | ⟨h1, h2⟩
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i - n, h2, by omega⟩)
    have h1 : ∑ j ∈ G, (gateAt C j).inputs.length =
        ∑ w ∈ L ∪ G.image (fun k => n + k), readsIn C G w := by
      rw [Finset.sum_congr rfl hlen, Finset.sum_comm]; rfl
    have h2 : ∑ w ∈ L, readsIn C G w = L.card := by
      rw [Finset.sum_congr rfl (fun w hw => (hl w hw).2)]
      rw [Finset.sum_congr rfl (fun w hw => if_neg (fun (e : w = ρ) => hρL (e ▸ hw)))]
      simp
    have h3 : ∑ w ∈ G.image (fun k => n + k), readsIn C G w + 1 = G.card := by
      rw [Finset.sum_image (fun a _ b _ hab => by omega)]
      rw [Finset.sum_congr rfl (fun k hk => hgg k hk)]
      have e : ∀ k ∈ G, (if n + k = ρ then 0 else 1) = (if k = j0 then 0 else 1) := by
        intro k _
        by_cases hk : k = j0
        · simp [hk, hρ]
        · have : n + k ≠ ρ := by omega
          simp [hk, this]
      rw [Finset.sum_congr rfl e, ← Finset.add_sum_erase G _ hj0]
      rw [Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
      simp only [if_true, Finset.sum_const, smul_eq_mul, Nat.mul_one, Nat.zero_add]
      have := Finset.card_erase_add_one hj0
      omega
    rw [h1, Finset.sum_union hdisj, h2] at hsum
    omega

private lemma bw_spec {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) (ht : t ∈ d.cover) :
    ∃ j < C.gates.length, d.bw t = n + j ∧ d.role j = (Kind.b, t.val) := by
  obtain ⟨j, hj, h1, h2, _⟩ := (hv.2.2.2.2.2.1 t ht).1
  exact ⟨j, hj, h1, h2⟩

private lemma bw_injOn {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (S : Finset (Fin n)) (hS : S ⊆ d.cover) :
    Set.InjOn d.bw (S : Set (Fin n)) := by
  intro s hs t ht h
  obtain ⟨j, _, h1, h2⟩ := bw_spec hv s (hS hs)
  obtain ⟨j', _, h1', h2'⟩ := bw_spec hv t (hS ht)
  have hj : j = j' := by omega
  subst hj
  rw [h2] at h2'
  exact Fin.ext (Prod.ext_iff.mp h2').2

private lemma zLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) :
    (zLeaves d t).card = (d.cover.filter (fun s => d.tie s = some t)).card + 1 := by
  unfold zLeaves
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn
    (bw_injOn hv _ (Finset.filter_subset _ _))]
  intro hin
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hin
  obtain ⟨j, _, h1, _⟩ := bw_spec hv s (Finset.mem_filter.mp hs).1
  have := t.isLt; omega

private lemma topLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) :
    (topLeaves d A).card = A.card + (d.cover.filter (fun t => d.tie t = none)).card := by
  unfold topLeaves
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injOn (bw_injOn hv _ (Finset.filter_subset _ _))]
  rw [Finset.disjoint_left]
  intro w hw hw'
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hw'
  obtain ⟨j, _, h1, _⟩ := bw_spec hv s (Finset.mem_filter.mp hs).1
  have := a.isLt; omega

private lemma oLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) (ht : t ∈ d.cover) :
    (oLeaves d t).card = (Finset.univ.filter (fun r => d.owns t r = true)).card := by
  unfold oLeaves
  apply Finset.card_image_of_injOn
  intro r hr r' hr' h
  have hr1 : d.owns t r = true := (Finset.mem_filter.mp hr).2
  have hr1' : d.owns t r' = true := (Finset.mem_filter.mp hr').2
  have key : ∀ q : Fin n, d.owns t q = true →
      d.lam t q = q.val ∨ ∃ j, d.lam t q = n + j ∧ d.role j = (Kind.z, q.val) := by
    intro q hq
    have hl := (hv.2.2.2.2.2.1 t ht).2.2.2 q hq
    unfold LamOK at hl
    split_ifs at hl
    · rcases hl.2.1 with h1 | ⟨j, _, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j, h1, h2⟩
    · exact Or.inl hl
  have hlt := r.isLt; have hlt' := r'.isLt
  rcases key r hr1 with h1 | ⟨j, h1, h2⟩ <;> rcases key r' hr1' with h1' | ⟨j', h1', h2'⟩
  · exact Fin.ext (by omega)
  · omega
  · omega
  · have hj : j = j' := by omega
    subst hj; rw [h2] at h2'
    exact Fin.ext (Prod.ext_iff.mp h2').2

private lemma bGates_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) (ht : t ∈ d.cover) :
    (gatesOf d C Kind.b t.val).card = 1 := by
  obtain ⟨j, hj, h1, h2⟩ := bw_spec hv t ht
  rw [Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext j'
  simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj', hr⟩
    rcases hv.2.2.2.2.1 j' hj' with htop | ⟨t', _, e1, e2⟩
    · rw [hr] at htop; simp at htop
    · rw [hr] at e1 e2
      have : t' = t := Fin.ext e1.symm
      subst this; have := e2 rfl; omega
  · rintro rfl; exact ⟨hj, h2⟩

private lemma gates_split {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) :
    C.gates.length = (topGates d C).card + ∑ t ∈ d.cover,
      ((gatesOf d C Kind.z t.val).card + (gatesOf d C Kind.o t.val).card +
        (gatesOf d C Kind.b t.val).card) := by
  have h0 := Finset.card_filter_add_card_filter_not
    (s := Finset.range C.gates.length) (fun j => (d.role j).1 = Kind.top)
  rw [Finset.card_range] at h0
  have hkeys : ∀ j ∈ (Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1 = Kind.top),
      d.role j ∈ ({Kind.z, Kind.o, Kind.b} : Finset Kind) ×ˢ d.cover.image Fin.val := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rcases hv.2.2.2.2.1 j hj.1 with htop | ⟨t, ht, e1, _⟩
    · exact absurd htop hj.2
    · rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_image.mpr ⟨t, ht, e1.symm⟩⟩
      have hne := hj.2
      generalize (d.role j).1 = k at hne
      cases k <;> simp at hne ⊢
  have h1 := Finset.card_eq_sum_card_fiberwise hkeys
  have hfib : ∀ k ∈ ({Kind.z, Kind.o, Kind.b} : Finset Kind) ×ˢ d.cover.image Fin.val,
      (((Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1 = Kind.top)).filter
        (fun j => d.role j = k)).card = (gatesOf d C k.1 k.2).card := by
    intro k hk
    congr 1; ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hj, _⟩, hr⟩; exact ⟨hj, hr⟩
    · rintro ⟨hj, hr⟩
      refine ⟨⟨hj, ?_⟩, hr⟩
      rw [hr]
      have hk1 := (Finset.mem_product.mp hk).1
      intro e; simp only at e; rw [e] at hk1; simp at hk1
  rw [Finset.sum_congr rfl hfib, Finset.sum_product] at h1
  dsimp only at h1
  have h2 : ∑ k ∈ ({Kind.z, Kind.o, Kind.b} : Finset Kind), ∑ v ∈ d.cover.image Fin.val,
      (gatesOf d C k v).card =
      ∑ t ∈ d.cover, ((gatesOf d C Kind.z t.val).card + (gatesOf d C Kind.o t.val).card +
        (gatesOf d C Kind.b t.val).card) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Finset.sum_image (fun a _ b _ h => Fin.val_injective h)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => by omega)
  have h3 : ((Finset.range C.gates.length).filter (fun j => (d.role j).1 = Kind.top)).card =
      (topGates d C).card := rfl
  omega

private lemma tie_split {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) :
    d.cover.card = (d.cover.filter (fun t => d.tie t = none)).card +
      ∑ t ∈ d.cover, (d.cover.filter (fun s => d.tie s = some t)).card := by
  have hkeys : ∀ s ∈ d.cover, d.tie s ∈ insert none (d.cover.image some) := by
    intro s _
    cases hs : d.tie s with
    | none => simp
    | some t =>
      have h1 := (hv.2.2.2.1 s t hs).2
      have h2 := (hv.2.2.1.1 t s h1).2
      simp [h2]
  rw [Finset.card_eq_sum_card_fiberwise hkeys, Finset.sum_insert (by simp),
    Finset.sum_image (fun a _ b _ h => Option.some_injective _ h)]

private lemma owned_card {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj] {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
    ∑ t ∈ d.cover, (Finset.univ.filter (fun r => d.owns t r = true)).card = K.edgeFinset.card := by
  have hown := hv.2.2.1
  have hP : ∀ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2 = true)),
      p.1 ∈ d.cover := fun p hp => (hown.1 p.1 p.2 (Finset.mem_filter.mp hp).2).2
  have h1 := Finset.card_eq_sum_card_fiberwise hP
  have hfib : ∀ t ∈ d.cover,
      ((Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2 = true)).filter
        (fun p => p.1 = t)).card = (Finset.univ.filter (fun r => d.owns t r = true)).card := by
    intro t _
    symm
    apply Finset.card_bij (fun r _ => (t, r))
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact ⟨hr, trivial⟩
    · intro a _ b _ h; exact (Prod.ext_iff.mp h).2
    · rintro ⟨u, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨h1, h2⟩ := hp; subst h2
      exact ⟨v, by simpa using h1, rfl⟩
  rw [Finset.sum_congr rfl hfib] at h1
  rw [← h1]
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · intro p hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hown.1 p.1 p.2 (Finset.mem_filter.mp hp).2).1
  · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hp' h
    have e1 : d.owns u v = true := (Finset.mem_filter.mp hp).2
    have e2 : d.owns u' v' = true := (Finset.mem_filter.mp hp').2
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; simp only at h1 h2; subst h1; subst h2
      exact hown.2 u v (hown.1 u v e1).1 (by rw [e1, e2])
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hne := hown.2 a b he
      cases hab : d.owns a b with
      | true => exact ⟨(a, b), by simp [hab], rfl⟩
      | false =>
        have hba : d.owns b a = true := by
          rw [hab] at hne
          cases h : d.owns b a with
          | true => rfl
          | false => exact absurd h.symm hne
        exact ⟨(b, a), by simp [hba], Sym2.eq_swap⟩

private lemma ncc_size {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj] {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
    C.size + 1 = A.card + K.edgeFinset.card + d.cover.card := by
  have hsize : C.size = C.gates.length := rfl
  have hsplit := gates_split hv
  have htop := tree_card n C _ _ _ hv.2.2.2.2.2.2
  rw [topLeaves_card hv] at htop
  have hper : ∀ u ∈ d.cover, (gatesOf d C Kind.z u.val).card + (gatesOf d C Kind.o u.val).card +
      (gatesOf d C Kind.b u.val).card =
      (d.cover.filter (fun s => d.tie s = some u)).card +
        (Finset.univ.filter (fun r => d.owns u r = true)).card := by
    intro u hu
    have hz := tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.1
    have ho := tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.2.1
    rw [zLeaves_card hv u] at hz
    rw [oLeaves_card hv u hu] at ho
    have hb := bGates_card hv u hu
    omega
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, owned_card hv] at hsplit
  have htie := tie_split hv
  omega

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  induction gs1 generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih => rw [wiresFrom_cons, ih]; simp; omega

private lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hlen]⟩
    rw [wiresFrom_cons, ht, List.append_assoc]

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi; simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval
  rw [wires_eq, wiresFrom_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD, hw]

private lemma wval_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have htake : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      exact congrArg (· :: _) (List.getD_eq_getElem _ _ hj).symm
    rw [← hdrop, htake]
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  rw [getD_snoc_eq _ _ _ _ hlen.symm]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hRB j hj i hi
  symm
  change (wiresFrom C.gates (List.ofFn x)).getD i false = _
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen]; omega), getD_snoc_lt _ _ _ _ (by omega)]

private lemma valid_fanInTwo {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) : FanInTwo C := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  have hgate : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, hj]
  rcases hv.2.2.2.2.1 j hj with htop | ⟨t, ht, heq, hb⟩
  · have hmem : j ∈ topGates d C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, htop⟩
    have h1 := hv.2.2.2.2.2.2.1 j hmem
    rw [hgate] at h1
    exact ⟨Or.inr (Or.inl h1.1), by omega⟩
  · cases hkind : (d.role j).1 with
    | top =>
      have hmem : j ∈ topGates d C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hkind⟩
      have h1 := hv.2.2.2.2.2.2.1 j hmem
      rw [hgate] at h1
      exact ⟨Or.inr (Or.inl h1.1), by omega⟩
    | z =>
      have hrole : d.role j = (Kind.z, t.val) := Prod.ext hkind heq
      have hmem : j ∈ gatesOf d C Kind.z t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrole⟩
      have h1 := (hv.2.2.2.2.2.1 t ht).2.1.1 j hmem
      rw [hgate] at h1
      exact ⟨Or.inr (Or.inl h1.1), by omega⟩
    | o =>
      have hrole : d.role j = (Kind.o, t.val) := Prod.ext hkind heq
      have hmem : j ∈ gatesOf d C Kind.o t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrole⟩
      have h1 := (hv.2.2.2.2.2.1 t ht).2.2.1.1 j hmem
      rw [hgate] at h1
      exact ⟨Or.inr (Or.inl h1.1), by omega⟩
    | b =>
      have hbw := hb hkind
      obtain ⟨j', hj', hbw', _, hop, hin⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hjj : j = j' := by omega
      subst hjj
      rw [hgate] at hop hin
      refine ⟨Or.inl hop, ?_⟩
      rcases hin with h | h <;> simp [h]

private lemma orTree_eval_up {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → wval C x u = true → wval C x ρ = true := by
  intro u hu hwu
  by_cases huρ0 : u = ρ
  · exact huρ0 ▸ hwu
  have hub : u ≤ n + C.gates.length := by
    rcases hu with huL | ⟨h1, h2⟩
    · have hr := (htree.2.1 u huL).2
      rw [if_neg huρ0] at hr
      have hex : ∃ j ∈ G, 0 < (gateAt C j).inputs.count u := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => Nat.eq_zero_of_le_zero (hno j hj))
        omega
      obtain ⟨j, hj, hcnt⟩ := hex
      have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.mp hcnt
      have := hRB j (hGlt j hj) u hmem
      have := hGlt j hj
      omega
    · have := hGlt (u - n) h2; omega
  clear huρ0
  generalize hk : n + C.gates.length - u = k
  induction k using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases huρ : u = ρ
    · exact huρ ▸ hwu
    · have hrc : readsIn C G u = 1 := by
        rcases hu with huL | ⟨h1, h2⟩
        · have := (htree.2.1 u huL).2; rw [if_neg huρ] at this; exact this
        · have hsub : n + (u - n) = u := by omega
          have := htree.2.2.1 (u - n) h2
          rw [hsub, if_neg huρ] at this; exact this
      have hex : ∃ j ∈ G, u ∈ (gateAt C j).inputs := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hno j hj))
        omega
      obtain ⟨j, hj, hmem⟩ := hex
      have hjlt := hGlt j hj
      have hult : u < n + j := hRB j hjlt u hmem
      have hop := (htree.1 j hj).1
      have hval : wval C x (n + j) = true := by
        rw [wval_gate C hRB x j hjlt, hop]
        simp [GateOp.eval]
        exact ⟨u, hmem, hwu⟩
      exact ih (n + C.gates.length - (n + j)) (by omega) (n + j)
        (Or.inr ⟨Nat.le_add_right _ _, by simpa using hj⟩) hval (by omega) rfl

private lemma orTree_eval_down {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → wval C x u = true → ∃ w ∈ L, wval C x w = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hwu
    rcases hu with huL | ⟨h1, h2⟩
    · exact ⟨u, huL, hwu⟩
    · set j := u - n with hjdef
      have hu_eq : u = n + j := by omega
      rw [hu_eq, wval_gate C hRB x j (hGlt j h2), (htree.1 j h2).1] at hwu
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at hwu
      obtain ⟨i, hi, hwi⟩ := hwu
      have hilt : i < u := by rw [hu_eq]; exact hRB j (hGlt j h2) i hi
      exact ih i hilt ((htree.1 j h2).2.2 i hi) hwi

private lemma orTree_top_mem {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (htree : IsOrTree n C G L ρ) : ρ ∈ L ∨ (n ≤ ρ ∧ ρ - n ∈ G) := by
  have hr := htree.2.2.2
  by_cases hG : G = ∅
  · rw [if_pos hG] at hr
    exact Or.inl (by rw [hr]; simp)
  · rw [if_neg hG] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact Or.inr ⟨Nat.le_add_right _ _, by simpa using hj⟩

private lemma orTree_eval_iff {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    wval C x ρ = true ↔ ∃ w ∈ L, wval C x w = true :=
  ⟨orTree_eval_down hRB hGlt htree x ρ (orTree_top_mem htree),
   fun ⟨w, hw, hww⟩ => orTree_eval_up hRB hGlt htree x w (Or.inl hw) hww⟩

private def centreStep (n : ℕ) (d : NCCData n) (w : List Bool) (g : Gate) : List Bool :=
  w ++ [decide ((d.role (w.length - n)).1 = Kind.z) && g.inputs.any (fun i => w.getD i false)]

private lemma centreFlags_eq (n : ℕ) (C : Circuit) (d : NCCData n) :
    centreFlags n C d = C.gates.foldl (centreStep n d)
      (List.ofFn fun i : Fin n => decide (i ∈ d.cover)) := rfl

private lemma foldl_centre_prefix (n : ℕ) (d : NCCData n) (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl (centreStep n d) w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (centreStep n d w g)
    refine ⟨[decide ((d.role (w.length - n)).1 = Kind.z) &&
        g.inputs.any (fun i => w.getD i false)] ++ t, ?_, by simp [hlen]⟩
    rw [List.foldl_cons, ht]; simp [centreStep, List.append_assoc]

private lemma foldl_centre_length (n : ℕ) (d : NCCData n) (gs : List Gate) (w : List Bool) :
    (gs.foldl (centreStep n d) w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := foldl_centre_prefix n d gs w
  rw [ht, List.length_append, hlen]

private lemma foldl_centre_getD_lt (n : ℕ) (d : NCCData n) (gs : List Gate) (w : List Bool)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (centreStep n d) w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := foldl_centre_prefix n d gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private lemma isCentred_input {n : ℕ} (C : Circuit) (d : NCCData n) (i : Fin n) :
    IsCentred n C d i.val ↔ i ∈ d.cover := by
  unfold IsCentred
  rw [centreFlags_eq, foldl_centre_getD_lt _ _ _ _ _ (by simp)]
  simp [List.getD, i.isLt]

private lemma isCentred_gate {n : ℕ} (C : Circuit) (d : NCCData n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    IsCentred n C d (n + j) ↔
      (d.role j).1 = Kind.z ∧ ∃ i ∈ (gateAt C j).inputs, IsCentred n C d i := by
  unfold IsCentred
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have htake : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]; simp [gateAt, List.getD, hj]
    rw [← hdrop, htake]
  set init := List.ofFn (fun i : Fin n => decide (i ∈ d.cover))
  set w0 := (C.gates.take j).foldl (centreStep n d) init
  have hlen : w0.length = n + j := by
    rw [foldl_centre_length]; simp [init, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlen1 : (centreStep n d w0 (gateAt C j)).length = n + j + 1 := by
    simp [centreStep, hlen]
  have hget : (centreFlags n C d).getD (n + j) false =
      (decide ((d.role j).1 = Kind.z) &&
        (gateAt C j).inputs.any (fun i => w0.getD i false)) := by
    rw [centreFlags_eq, hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_centre_getD_lt _ _ _ _ _ (by omega : n + j < (centreStep n d w0 (gateAt C j)).length)]
    simp only [centreStep]
    rw [getD_snoc_eq _ _ _ _ hlen.symm]
    have hsub : w0.length - n = j := by omega
    rw [hsub]
  rw [hget, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  have hlt_eq : ∀ i, i < n + j → (centreFlags n C d).getD i false = w0.getD i false := by
    intro i hi
    rw [centreFlags_eq, hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_centre_getD_lt _ _ _ _ _ (by omega : i < (centreStep n d w0 (gateAt C j)).length)]
    simp only [centreStep]
    exact getD_snoc_lt _ _ _ _ (by omega)
  constructor
  · rintro ⟨hz, i, hi, hwi⟩
    exact ⟨hz, i, hi, by rw [hlt_eq i (hRB j hj i hi)]; exact hwi⟩
  · rintro ⟨hz, i, hi, hwi⟩
    exact ⟨hz, i, hi, by rw [← hlt_eq i (hRB j hj i hi)]; exact hwi⟩

private lemma centred_eval {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) {r : Fin n} (hr : r ∈ d.cover) (x : Fin n → Bool)
    (hxr : x r = true) :
    ∀ w, (w = r.val ∨ ∃ j < C.gates.length, w = n + j ∧ d.role j = (Kind.z, r.val)) →
      IsCentred n C d w → wval C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro (rfl | ⟨j, hj, rfl, hrole⟩) hc
    · rw [wval_input C x r.val r.isLt]; exact hxr
    · obtain ⟨_, i, hi, hci⟩ := (isCentred_gate C d hv.1 j hj).mp hc
      have hilt : i < n + j := hv.1 j hj i hi
      have hmem : j ∈ gatesOf d C Kind.z r.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrole⟩
      have htree := (hv.2.2.2.2.2.1 r hr).2.1
      have hwi : wval C x i = true := by
        rcases (htree.1 j hmem).2.2 i hi with hiL | ⟨hni, hig⟩
        · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hiL
          rcases hiL with rfl | ⟨s, ⟨hs, _⟩, rfl⟩
          · exact ih r.val hilt (Or.inl rfl) hci
          · obtain ⟨jb, hjb, hbw, hrb⟩ := bw_spec hv s hs
            rw [hbw] at hci
            have hz := ((isCentred_gate C d hv.1 jb hjb).mp hci).1
            rw [hrb] at hz; cases hz
        · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
          exact ih i hilt (Or.inr ⟨i - n, hig.1, by omega, hig.2⟩) hci
      rw [wval_gate C hv.1 x j hj, (htree.1 j hmem).1]
      simp [GateOp.eval]
      exact ⟨i, hi, hwi⟩

private lemma valid_eval_sound_wire {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
    {A : Finset (Fin n)} {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → wval C x w = true →
      (w < n → True) ∧
      (∀ j, w = n + j → (d.role j).1 = Kind.top → graphFun K A x = true) ∧
      (∀ j (t : Fin n), w = n + j → t ∈ d.cover → d.role j = (Kind.b, t.val) →
        graphFun K A x = true) ∧
      (∀ j (t : Fin n), w = n + j → t ∈ d.cover → d.role j = (Kind.z, t.val) →
        x t = true ∨ graphFun K A x = true) ∧
      (∀ j (t : Fin n), w = n + j → t ∈ d.cover → d.role j = (Kind.o, t.val) →
        (∃ r, d.owns t r = true ∧ x r = true) ∨ graphFun K A x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwlt hww
    refine ⟨fun _ => trivial, ?_, ?_, ?_, ?_⟩
    · intro j rfl htop
      have hj : j < C.gates.length := by omega
      have hmem : j ∈ topGates d C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, htop⟩
      have htree := hv.2.2.2.2.2.2
      rw [wval_gate C hv.1 x j hj, (htree.1 j hmem).1] at hww
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at hww
      obtain ⟨i, hi, hwi⟩ := hww
      have hilt : i < n + j := hv.1 j hj i hi
      rcases (htree.1 j hmem).2.2 i hi with hiL | ⟨hni, hig⟩
      · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hiL
        rcases hiL with ⟨a, ha, rfl⟩ | ⟨s, ⟨hs, _⟩, rfl⟩
        · rw [wval_input C x a.val a.isLt] at hwi
          unfold graphFun; simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl ⟨a, ha, hwi⟩
        · obtain ⟨jb, hjb, hbw, hrb⟩ := bw_spec hv s hs
          exact (ih (d.bw s) hilt (by omega) hwi).2.2.1 jb s hbw hs hrb
      · simp only [topGates, Finset.mem_filter, Finset.mem_range] at hig
        exact (ih i hilt (by omega) hwi).2.1 (i - n) (by omega) hig.2
    · intro j t rfl ht hrole
      have hj : j < C.gates.length := by omega
      obtain ⟨jb, hjb, hbw, _, hop, hin⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hjj : j = jb := by
        rcases hv.2.2.2.2.1 j hj with htop | ⟨t', _, heq, hb⟩
        · rw [hrole] at htop; cases htop
        · rw [hrole] at heq hb
          have : t' = t := Fin.ext heq.symm; subst this
          have := hb rfl; omega
      subst hjj
      rw [wval_gate C hv.1 x j hj, hop] at hww
      have hboth : wval C x (d.zroot t) = true ∧ wval C x (d.oroot t) = true := by
        rcases hin with h | h <;> rw [h] at hww <;> simp [GateOp.eval] at hww
        · exact ⟨hww.1, hww.2⟩
        · exact ⟨hww.2, hww.1⟩
      have hzl : d.zroot t < n + j :=
        hv.1 j hj (d.zroot t) (by rcases hin with h | h <;> rw [h] <;> simp)
      have hol : d.oroot t < n + j :=
        hv.1 j hj (d.oroot t) (by rcases hin with h | h <;> rw [h] <;> simp)
      have hz : x t = true ∨ graphFun K A x = true := by
        rcases orTree_top_mem (hv.2.2.2.2.2.1 t ht).2.1 with hL | ⟨hni, hg⟩
        · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hL
          rcases hL with heq | ⟨s, ⟨hs, _⟩, heq⟩
          · rw [heq, wval_input C x t.val t.isLt] at hboth; exact Or.inl hboth.1
          · obtain ⟨js, hjs, hbws, hrbs⟩ := bw_spec hv s hs
            exact Or.inr ((ih (d.zroot t) hzl (by omega) hboth.1).2.2.1 js s (heq ▸ hbws) hs hrbs)
        · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hg
          exact (ih (d.zroot t) hzl (by omega) hboth.1).2.2.2.1 (d.zroot t - n) t (by omega) ht hg.2
      have ho : (∃ r, d.owns t r = true ∧ x r = true) ∨ graphFun K A x = true := by
        rcases orTree_top_mem (hv.2.2.2.2.2.1 t ht).2.2.1 with hL | ⟨hni, hg⟩
        · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hL
          obtain ⟨r, hown, heq⟩ := hL
          have hlam := (hv.2.2.2.2.2.1 t ht).2.2.2 r hown
          unfold LamOK at hlam
          split_ifs at hlam with hr
          · rcases hlam.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
            · rw [← heq, h1, wval_input C x r.val r.isLt] at hboth
              exact Or.inl ⟨r, hown, hboth.2⟩
            · rcases (ih (d.oroot t) hol (by omega) hboth.2).2.2.2.1 jz r
                (heq ▸ h1) hr h2 with hxr | hF
              · exact Or.inl ⟨r, hown, hxr⟩
              · exact Or.inr hF
          · rw [← heq, hlam, wval_input C x r.val r.isLt] at hboth
            exact Or.inl ⟨r, hown, hboth.2⟩
        · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hg
          exact (ih (d.oroot t) hol (by omega) hboth.2).2.2.2.2 (d.oroot t - n) t (by omega) ht hg.2
      rcases hz with hxt | hF
      · rcases ho with ⟨r, hown, hxr⟩ | hF
        · unfold graphFun; simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr ⟨t, r, (hv.2.2.1.1 t r hown).1, hxt, hxr⟩
        · exact hF
      · exact hF
    · intro j t rfl ht hrole
      have hj : j < C.gates.length := by omega
      have hmem : j ∈ gatesOf d C Kind.z t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrole⟩
      have htree := (hv.2.2.2.2.2.1 t ht).2.1
      rw [wval_gate C hv.1 x j hj, (htree.1 j hmem).1] at hww
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at hww
      obtain ⟨i, hi, hwi⟩ := hww
      have hilt : i < n + j := hv.1 j hj i hi
      rcases (htree.1 j hmem).2.2 i hi with hiL | ⟨hni, hig⟩
      · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hiL
        rcases hiL with rfl | ⟨s, ⟨hs, _⟩, rfl⟩
        · rw [wval_input C x t.val t.isLt] at hwi; exact Or.inl hwi
        · obtain ⟨js, hjs, hbws, hrbs⟩ := bw_spec hv s hs
          exact Or.inr ((ih (d.bw s) hilt (by omega) hwi).2.2.1 js s hbws hs hrbs)
      · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
        exact (ih i hilt (by omega) hwi).2.2.2.1 (i - n) t (by omega) ht hig.2
    · intro j t rfl ht hrole
      have hj : j < C.gates.length := by omega
      have hmem : j ∈ gatesOf d C Kind.o t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrole⟩
      have htree := (hv.2.2.2.2.2.1 t ht).2.2.1
      rw [wval_gate C hv.1 x j hj, (htree.1 j hmem).1] at hww
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at hww
      obtain ⟨i, hi, hwi⟩ := hww
      have hilt : i < n + j := hv.1 j hj i hi
      rcases (htree.1 j hmem).2.2 i hi with hiL | ⟨hni, hig⟩
      · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hiL
        obtain ⟨r, hown, rfl⟩ := hiL
        have hlam := (hv.2.2.2.2.2.1 t ht).2.2.2 r hown
        unfold LamOK at hlam
        split_ifs at hlam with hr
        · rcases hlam.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
          · rw [h1, wval_input C x r.val r.isLt] at hwi
            exact Or.inl ⟨r, hown, hwi⟩
          · rcases (ih (d.lam t r) hilt (by omega) hwi).2.2.2.1 jz r h1 hr h2 with hxr | hF
            · exact Or.inl ⟨r, hown, hxr⟩
            · exact Or.inr hF
        · rw [hlam, wval_input C x r.val r.isLt] at hwi
          exact Or.inl ⟨r, hown, hwi⟩
      · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
        exact (ih i hilt (by omega) hwi).2.2.2.2 (i - n) t (by omega) ht hig.2

private lemma orTree_le_top {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → u ≤ ρ := by
  intro u hu
  by_cases huρ0 : u = ρ
  · exact le_of_eq huρ0
  have hub : u ≤ n + C.gates.length := by
    rcases hu with huL | ⟨h1, h2⟩
    · have hr := (htree.2.1 u huL).2; rw [if_neg huρ0] at hr
      have hex : ∃ j ∈ G, u ∈ (gateAt C j).inputs := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hno j hj))
        omega
      obtain ⟨j, hj, hmem⟩ := hex
      have := hRB j (hGlt j hj) u hmem; have := hGlt j hj; omega
    · have := hGlt (u - n) h2; omega
  clear huρ0
  generalize hk : n + C.gates.length - u = k
  induction k using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases huρ : u = ρ
    · exact le_of_eq huρ
    · have hrc : readsIn C G u = 1 := by
        rcases hu with huL | ⟨h1, h2⟩
        · have := (htree.2.1 u huL).2; rw [if_neg huρ] at this; exact this
        · have hsub : n + (u - n) = u := by omega
          have := htree.2.2.1 (u - n) h2; rw [hsub, if_neg huρ] at this; exact this
      have hex : ∃ j ∈ G, u ∈ (gateAt C j).inputs := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hno j hj))
        omega
      obtain ⟨j, hj, hmem⟩ := hex
      have hult : u < n + j := hRB j (hGlt j hj) u hmem
      have hjlt := hGlt j hj
      have hjle := ih (n + C.gates.length - (n + j)) (by omega) (n + j)
        (Or.inr ⟨Nat.le_add_right _ _, by simpa using hj⟩) (by omega) rfl
      omega

private lemma valid_bw_prop {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (x : Fin n → Bool) :
    ∀ t ∈ d.cover, wval C x (d.bw t) = true → wval C x C.output = true := by
  have htop_lt : ∀ j ∈ topGates d C, j < C.gates.length :=
    fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hg_lt : ∀ k t, ∀ j ∈ gatesOf d C k t, j < C.gates.length :=
    fun _ _ j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  intro t ht hbt
  have hub : d.bw t ≤ n + C.gates.length := by
    obtain ⟨jb, hjb, hbw, _⟩ := bw_spec hv t ht; omega
  generalize hk : n + C.gates.length - d.bw t = k
  induction k using Nat.strong_induction_on generalizing t with
  | _ k ih =>
    cases htie : d.tie t with
    | none =>
      refine orTree_eval_up hv.1 htop_lt hv.2.2.2.2.2.2 x (d.bw t) (Or.inl ?_) hbt
      simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      exact Or.inr ⟨t, ⟨ht, htie⟩, rfl⟩
    | some t' =>
      have hown : d.owns t' t = true := (hv.2.2.2.1 t t' htie).2
      have ht' : t' ∈ d.cover := (hv.2.2.1.1 t' t hown).2
      obtain ⟨jb1, hjb1, hbw1, _, hop1, hin1⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hzr_t : wval C x (d.zroot t) = true := by
        rw [hbw1, wval_gate C hv.1 x jb1 hjb1, hop1] at hbt
        rcases hin1 with h | h <;> rw [h] at hbt <;> simp [GateOp.eval] at hbt
        · exact hbt.1
        · exact hbt.2
      have hlam_eq : d.lam t' t = d.zroot t := by
        have hl := (hv.2.2.2.2.2.1 t' ht').2.2.2 t hown
        unfold LamOK at hl; rw [if_pos ht] at hl
        exact hl.2.2 htie
      have hor_t' : wval C x (d.oroot t') = true := by
        refine orTree_eval_up hv.1 (hg_lt _ _) (hv.2.2.2.2.2.1 t' ht').2.2.1 x (d.lam t' t)
          (Or.inl ?_) (by rw [hlam_eq]; exact hzr_t)
        simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t, hown, rfl⟩
      have hbt_in : d.bw t ∈ zLeaves d t' := by
        simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
        exact Or.inr ⟨t, ⟨ht, htie⟩, rfl⟩
      have hzr_t' : wval C x (d.zroot t') = true :=
        orTree_eval_up hv.1 (hg_lt _ _) (hv.2.2.2.2.2.1 t' ht').2.1 x (d.bw t) (Or.inl hbt_in) hbt
      obtain ⟨jb', hjb', hbw', _, hop', hin'⟩ := (hv.2.2.2.2.2.1 t' ht').1
      have hbt' : wval C x (d.bw t') = true := by
        rw [hbw', wval_gate C hv.1 x jb' hjb', hop']
        rcases hin' with h | h <;> rw [h] <;> simp [GateOp.eval, hzr_t', hor_t']
      have hle_z : d.bw t ≤ d.zroot t' :=
        orTree_le_top hv.1 (hg_lt _ _) (hv.2.2.2.2.2.1 t' ht').2.1 (d.bw t) (Or.inl hbt_in)
      have hlt_b : d.zroot t' < d.bw t' := by
        rw [hbw']
        exact hv.1 jb' hjb' (d.zroot t') (by rcases hin' with h | h <;> rw [h] <;> simp)
      exact ih (n + C.gates.length - d.bw t') (by omega) t' ht' hbt' (by omega) rfl

private lemma valid_eval {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
    {A : Finset (Fin n)} {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
    circuitFun n C = graphFun K A := by
  funext x
  have htop_lt : ∀ j ∈ topGates d C, j < C.gates.length :=
    fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hg_lt : ∀ k t, ∀ j ∈ gatesOf d C k t, j < C.gates.length :=
    fun _ _ j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hcf : circuitFun n C x = wval C x C.output := rfl
  rw [hcf]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hout
    rcases orTree_top_mem hv.2.2.2.2.2.2 with hL | ⟨hni, hg⟩
    · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hL
      rcases hL with ⟨a, ha, heq⟩ | ⟨s, ⟨hs, _⟩, heq⟩
      · rw [← heq, wval_input C x a.val a.isLt] at hout
        unfold graphFun; simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl ⟨a, ha, hout⟩
      · obtain ⟨js, hjs, hbws, hrbs⟩ := bw_spec hv s hs
        exact (valid_eval_sound_wire hv x C.output (by omega) hout).2.2.1 js s
          (heq ▸ hbws) hs hrbs
    · simp only [topGates, Finset.mem_filter, Finset.mem_range] at hg
      exact (valid_eval_sound_wire hv x C.output (by omega) hout).2.1
        (C.output - n) (by omega) hg.2
  · intro hF
    unfold graphFun at hF
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hF
    rcases hF with ⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩
    · refine orTree_eval_up hv.1 htop_lt hv.2.2.2.2.2.2 x a.val (Or.inl ?_) ?_
      · simp only [topLeaves, Finset.mem_union, Finset.mem_image]
        exact Or.inl ⟨a, ha, rfl⟩
      · rw [wval_input C x a.val a.isLt]; exact hxa
    · have hex : ∃ t r : Fin n, d.owns t r = true ∧ x t = true ∧ x r = true := by
        have hne := hv.2.2.1.2 u v huv
        cases h1 : d.owns u v with
        | true => exact ⟨u, v, h1, hxu, hxv⟩
        | false =>
          have h2 : d.owns v u = true := by
            rw [h1] at hne
            cases h : d.owns v u with
            | true => rfl
            | false => exact absurd h.symm hne
          exact ⟨v, u, h2, hxv, hxu⟩
      obtain ⟨t, r, hown, hxt, hxr⟩ := hex
      have ht : t ∈ d.cover := (hv.2.2.1.1 t r hown).2
      have hzr : wval C x (d.zroot t) = true :=
        orTree_eval_up hv.1 (hg_lt _ _) (hv.2.2.2.2.2.1 t ht).2.1 x t.val
          (Or.inl (Finset.mem_insert_self _ _)) (by rw [wval_input C x t.val t.isLt]; exact hxt)
      have hlam_val : wval C x (d.lam t r) = true := by
        have hlam := (hv.2.2.2.2.2.1 t ht).2.2.2 r hown
        unfold LamOK at hlam
        split_ifs at hlam with hr
        · exact centred_eval hv hr x hxr (d.lam t r) hlam.2.1 hlam.1
        · rw [hlam, wval_input C x r.val r.isLt]; exact hxr
      have hor : wval C x (d.oroot t) = true := by
        refine orTree_eval_up hv.1 (hg_lt _ _) (hv.2.2.2.2.2.1 t ht).2.2.1 x (d.lam t r)
          (Or.inl ?_) hlam_val
        simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨r, hown, rfl⟩
      obtain ⟨jb, hjb, hbw, _, hop, hin⟩ := (hv.2.2.2.2.2.1 t ht).1
      have hbt : wval C x (d.bw t) = true := by
        rw [hbw, wval_gate C hv.1 x jb hjb, hop]
        rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hzr, hor]
      exact valid_bw_prop hv x t ht hbt

private def orChainAux (base : ℕ) (cur : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], cur)
  | w :: ws =>
    let r := orChainAux (base + 1) base ws
    (⟨GateOp.or, [cur, w]⟩ :: r.1, r.2)

private lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private lemma orChainAux_spec (base cur : ℕ) (ws : List ℕ) :
    (orChainAux base cur ws).1.length = ws.length ∧
    (∀ g ∈ (orChainAux base cur ws).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
    (∀ (w0 : List Bool), w0.length = base → (∀ i ∈ ws, i < base) →
      (wiresFrom (orChainAux base cur ws).1 w0).getD (orChainAux base cur ws).2 false =
        (w0.getD cur false || ws.any (fun i => w0.getD i false))) ∧
    (cur < base → (∀ i ∈ ws, i < base) → (orChainAux base cur ws).2 < base + ws.length) := by
  induction ws generalizing base cur with
  | nil =>
    refine ⟨rfl, by simp [orChainAux], fun w0 _ _ => by simp [orChainAux, wiresFrom],
      fun h _ => by simpa [orChainAux] using h⟩
  | cons a ws ih =>
    obtain ⟨hlen, hok, hev, hlt⟩ := ih (base + 1) base
    refine ⟨by simp [orChainAux, hlen], ?_, ?_, ?_⟩
    · intro g hg
      simp only [orChainAux, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · exact hok g hg
    · intro w0 hw0 hall
      simp only [orChainAux, wiresFrom_cons]
      set w1 := w0 ++ [w0.getD cur false || w0.getD a false]
      have hw1 : w1.length = base + 1 := by simp [w1, hw0]
      have hall' : ∀ i ∈ ws, i < base + 1 := fun i hi => by
        have := hall i (List.mem_cons_of_mem _ hi); omega
      have h1 := hev w1 hw1 hall'
      have hcur1 : w1.getD base false = (w0.getD cur false || w0.getD a false) :=
        getD_snoc_eq _ _ _ _ hw0.symm
      have hstep : w0 ++ [GateOp.or.eval ([cur, a].map fun i => w0.getD i false)] = w1 := by
        simp [w1, GateOp.eval]
      rw [hstep, h1, hcur1]
      have hany : ws.any (fun i => w1.getD i false) = ws.any (fun i => w0.getD i false) :=
        list_any_congr ws _ _ (fun b hb =>
          getD_snoc_lt _ _ _ _ (by have := hall b (List.mem_cons_of_mem _ hb); omega))
      simp only [List.any_cons, Bool.or_assoc, hany]
    · intro hcb hall
      simp only [orChainAux, List.length_cons]
      have := hlt (by omega) (fun i hi => by
        have := hall i (List.mem_cons_of_mem _ hi); omega)
      omega

private def orChain (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | w :: ws => orChainAux base w ws

private lemma orChain_spec (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (orChain base ws).1.length + 1 = ws.length ∧
    (∀ g ∈ (orChain base ws).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
    (∀ (w0 : List Bool), w0.length = base → (∀ i ∈ ws, i < base) →
      (wiresFrom (orChain base ws).1 w0).getD (orChain base ws).2 false =
        ws.any (fun i => w0.getD i false)) ∧
    ((∀ i ∈ ws, i < base) → (orChain base ws).2 < base + (orChain base ws).1.length) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons w ws =>
    obtain ⟨hlen, hok, hev, hlt⟩ := orChainAux_spec base w ws
    refine ⟨by simp [orChain, hlen], hok, ?_, ?_⟩
    · intro w0 hw0 hall
      simpa [orChain] using hev w0 hw0 (fun i hi => hall i (List.mem_cons_of_mem _ hi))
    · intro hall
      simp only [orChain, hlen]
      exact hlt (hall w List.mem_cons_self) (fun i hi => hall i (List.mem_cons_of_mem _ hi))

private def buildTerms (n : ℕ) (nbrs : Fin n → List (Fin n)) (base : ℕ) :
    List (Fin n) → List Gate × List ℕ
  | [] => ([], [])
  | t :: ts =>
    let r1 := orChain base ((nbrs t).map Fin.val)
    let base1 := base + r1.1.length
    let bg : Gate := ⟨GateOp.and, [t.val, r1.2]⟩
    let r2 := buildTerms n nbrs (base1 + 1) ts
    (r1.1 ++ bg :: r2.1, base1 :: r2.2)

private lemma buildTerms_spec (n : ℕ) (nbrs : Fin n → List (Fin n)) (base : ℕ)
    (ts : List (Fin n)) (hge : n ≤ base) (hne : ∀ t ∈ ts, nbrs t ≠ []) :
    (buildTerms n nbrs base ts).1.length = (ts.map (fun t => (nbrs t).length)).sum ∧
    (∀ g ∈ (buildTerms n nbrs base ts).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
    (buildTerms n nbrs base ts).2.length = ts.length ∧
    (∀ i ∈ (buildTerms n nbrs base ts).2, i < base + (buildTerms n nbrs base ts).1.length) ∧
    (∀ (x : Fin n → Bool) (w0 : List Bool), w0.length = base →
      (∀ i : Fin n, w0.getD i.val false = x i) →
      (buildTerms n nbrs base ts).2.any
          (fun b => (wiresFrom (buildTerms n nbrs base ts).1 w0).getD b false) =
        ts.any (fun t => x t && (nbrs t).any x)) := by
  induction ts generalizing base with
  | nil =>
    refine ⟨rfl, by simp [buildTerms], rfl, by simp [buildTerms], fun _ _ _ _ => rfl⟩
  | cons t ts ih =>
    have htne : (nbrs t).map Fin.val ≠ [] := by
      intro h; exact hne t List.mem_cons_self (List.map_eq_nil_iff.mp h)
    obtain ⟨hlen1, hok1, hev1, hlt1⟩ := orChain_spec base ((nbrs t).map Fin.val) htne
    set r1 := orChain base ((nbrs t).map Fin.val)
    set base1 := base + r1.1.length
    set bg : Gate := ⟨GateOp.and, [t.val, r1.2]⟩
    obtain ⟨hlen2, hok2, hblen2, hblt2, hev2⟩ :=
      ih (base1 + 1) (by omega) (fun u hu => hne u (List.mem_cons_of_mem _ hu))
    have hall1 : ∀ i ∈ (nbrs t).map Fin.val, i < base := by
      intro i hi
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
      have := r.isLt; omega
    have hr1_len : r1.1.length + 1 = (nbrs t).length := by
      simpa [List.length_map] using hlen1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (r1.1 ++ bg :: (buildTerms n nbrs (base1 + 1) ts).1).length =
        ((t :: ts).map (fun t => (nbrs t).length)).sum
      simp only [List.length_append, List.length_cons, List.map_cons, List.sum_cons, hlen2]
      omega
    · intro g hg
      change g ∈ r1.1 ++ bg :: (buildTerms n nbrs (base1 + 1) ts).1 at hg
      simp only [List.mem_append, List.mem_cons] at hg
      rcases hg with h | rfl | h
      · exact hok1 g h
      · exact ⟨Or.inl rfl, by simp [bg]⟩
      · exact hok2 g h
    · change (base1 :: (buildTerms n nbrs (base1 + 1) ts).2).length = (t :: ts).length
      simp [hblen2]
    · intro i hi
      change i ∈ base1 :: (buildTerms n nbrs (base1 + 1) ts).2 at hi
      change i < base + (r1.1 ++ bg :: (buildTerms n nbrs (base1 + 1) ts).1).length
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [List.length_append, List.length_cons, base1]; omega
      · have h1 := hblt2 i hi
        rw [List.length_append, List.length_cons]
        change i < base1 + 1 + (buildTerms n nbrs (base1 + 1) ts).1.length at h1
        have hbase : base1 = base + r1.1.length := rfl
        omega
    · intro x w0 hw0 hwx
      change (base1 :: (buildTerms n nbrs (base1 + 1) ts).2).any
          (fun b => (wiresFrom (r1.1 ++ bg :: (buildTerms n nbrs (base1 + 1) ts).1) w0).getD b false) =
        (t :: ts).any (fun t => x t && (nbrs t).any x)
      simp only [List.any_cons]
      set w1 := wiresFrom r1.1 w0
      have hw1len : w1.length = base1 := by rw [wiresFrom_length, hw0]
      set w2 := w1 ++ [bg.op.eval (bg.inputs.map fun i => w1.getD i false)]
      have hw2len : w2.length = base1 + 1 := by simp [w2, hw1len]
      have hw_eq : wiresFrom (r1.1 ++ bg :: (buildTerms n nbrs (base1 + 1) ts).1) w0 =
          wiresFrom (buildTerms n nbrs (base1 + 1) ts).1 w2 := by
        rw [wiresFrom_append, wiresFrom_cons]
      rw [hw_eq]
      have hb1_val : (wiresFrom (buildTerms n nbrs (base1 + 1) ts).1 w2).getD base1 false =
          (x t && (nbrs t).any x) := by
        rw [wiresFrom_getD_lt _ _ _ (by rw [hw2len]; omega)]
        rw [getD_snoc_eq _ _ _ _ hw1len.symm]
        simp only [bg, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq]
        have hwt : w1.getD t.val false = x t := by
          rw [wiresFrom_getD_lt _ _ _ (by rw [hw0]; have := t.isLt; omega), hwx t]
        have hwr : w1.getD r1.2 false = (nbrs t).any x := by
          rw [hev1 w0 hw0 hall1, List.any_map]
          have : (fun (i : Fin n) => w0.getD i.val false) = x := funext hwx
          rw [show (fun i => w0.getD i false) ∘ Fin.val = fun i : Fin n => w0.getD i.val false from rfl,
            this]
        rw [hwt, hwr]
      have hwx2 : ∀ i : Fin n, w2.getD i.val false = x i := by
        intro i
        have hilt : i.val < base1 := by have := i.isLt; have : base1 = base + r1.1.length := rfl; omega
        rw [getD_snoc_lt _ _ _ _ (by rw [hw1len]; exact hilt)]
        rw [wiresFrom_getD_lt _ _ _ (by rw [hw0]; have := i.isLt; omega), hwx i]
      rw [hb1_val, hev2 x w2 hw2len hwx2]

private lemma exists_circuit_bound {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (T : Finset (Fin n))
    (hT : IsMinCover K T) (hneE : ∃ u v : Fin n, K.Adj u v) :
    ∃ C : Circuit, FanInTwo C ∧ circuitFun n C = graphFun K A ∧
      C.size + 1 = A.card + K.edgeFinset.card + T.card := by
  classical
  let owns : Fin n → Fin n → Bool := fun t r =>
    decide (t ∈ T ∧ K.Adj t r ∧ (r ∉ T ∨ t.val < r.val))
  have hown_ok : ∀ t r, owns t r = true → K.Adj t r ∧ t ∈ T := by
    intro t r h
    simp only [owns, decide_eq_true_eq] at h
    exact ⟨h.2.1, h.1⟩
  have hown_uniq : ∀ u v, K.Adj u v → owns u v ≠ owns v u := by
    intro u v huv
    rcases hT.1 huv with hu | hv
    · by_cases hv' : v ∈ T
      · have hne : u.val ≠ v.val := fun h => huv.ne (Fin.ext h)
        by_cases hlt : u.val < v.val
        · have h1 : owns u v = true := decide_eq_true_eq.mpr ⟨hu, huv, Or.inr hlt⟩
          have h2 : owns v u = false := decide_eq_false_iff_not.mpr (by
            rintro ⟨_, _, h3 | h3⟩; exact h3 hu; omega)
          rw [h1, h2]; decide
        · have h1 : owns u v = false := decide_eq_false_iff_not.mpr (by
            rintro ⟨_, _, h3 | h3⟩; exact h3 hv'; omega)
          have h2 : owns v u = true := decide_eq_true_eq.mpr ⟨hv', huv.symm, Or.inr (by omega)⟩
          rw [h1, h2]; decide
      · have h1 : owns u v = true := decide_eq_true_eq.mpr ⟨hu, huv, Or.inl hv'⟩
        have h2 : owns v u = false := decide_eq_false_iff_not.mpr (fun h => hv' h.1)
        rw [h1, h2]; decide
    · by_cases hu' : u ∈ T
      · have hne : u.val ≠ v.val := fun h => huv.ne (Fin.ext h)
        by_cases hlt : u.val < v.val
        · have h1 : owns u v = true := decide_eq_true_eq.mpr ⟨hu', huv, Or.inr hlt⟩
          have h2 : owns v u = false := decide_eq_false_iff_not.mpr (by
            rintro ⟨_, _, h3 | h3⟩; exact h3 hu'; omega)
          rw [h1, h2]; decide
        · have h1 : owns u v = false := decide_eq_false_iff_not.mpr (by
            rintro ⟨_, _, h3 | h3⟩; exact h3 hv; omega)
          have h2 : owns v u = true := decide_eq_true_eq.mpr ⟨hv, huv.symm, Or.inr (by omega)⟩
          rw [h1, h2]; decide
      · have h1 : owns u v = false := decide_eq_false_iff_not.mpr (fun h => hu' h.1)
        have h2 : owns v u = true := decide_eq_true_eq.mpr ⟨hv, huv.symm, Or.inl hu'⟩
        rw [h1, h2]; decide
  let nbrs : Fin n → List (Fin n) := fun t => (Finset.univ.filter (fun r => owns t r = true)).toList
  have hnbr_ne : ∀ t ∈ T, nbrs t ≠ [] := by
    intro t ht heq
    have hemp : Finset.univ.filter (fun r => owns t r = true) = ∅ := Finset.toList_eq_nil.mp heq
    have hcov : K.IsVertexCover ((T.erase t) : Set (Fin n)) := by
      intro u v huv
      have hne := hown_uniq u v huv
      cases h1 : owns u v with
      | true =>
        have huT := (hown_ok u v h1).2
        by_cases hut : u = t
        · subst hut
          have : v ∈ Finset.univ.filter (fun r => owns u r = true) := by simp [h1]
          rw [hemp] at this; exact absurd this (Finset.notMem_empty _)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hut, huT⟩)
      | false =>
        have h2 : owns v u = true := by
          rw [h1] at hne; cases h : owns v u with
          | true => rfl
          | false => exact absurd h.symm hne
        have hvT := (hown_ok v u h2).2
        by_cases hvt : v = t
        · subst hvt
          have : u ∈ Finset.univ.filter (fun r => owns v r = true) := by simp [h2]
          rw [hemp] at this; exact absurd this (Finset.notMem_empty _)
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvt, hvT⟩)
    have hle := hT.2 (T.erase t) hcov
    have hcard := Finset.card_erase_add_one ht
    omega
  have hTne : T.Nonempty := by
    obtain ⟨u, v, huv⟩ := hneE
    rcases hT.1 huv with hu | hv
    · exact ⟨u, hu⟩
    · exact ⟨v, hv⟩
  set ts := T.toList
  obtain ⟨hlenB, hokB, hblenB, hbltB, hevB⟩ :=
    buildTerms_spec n nbrs n ts (le_refl n) (fun t ht => hnbr_ne t (Finset.mem_toList.mp ht))
  set rB := buildTerms n nbrs n ts
  set topList := A.toList.map Fin.val ++ rB.2
  have htop_ne : topList ≠ [] := by
    intro h
    have hr2 : rB.2 = [] := (List.append_eq_nil_iff.mp h).2
    have hts : ts.length = 0 := by rw [← hblenB, hr2]; rfl
    have : T.card = 0 := by simpa [ts] using hts
    exact hTne.ne_empty (Finset.card_eq_zero.mp this)
  obtain ⟨hlenO, hokO, hevO, _⟩ := orChain_spec (n + rB.1.length) topList htop_ne
  set rO := orChain (n + rB.1.length) topList
  refine ⟨⟨rB.1 ++ rO.1, rO.2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hokB g h
    · exact hokO g h
  · funext x
    change (wiresFrom (rB.1 ++ rO.1) (List.ofFn x)).getD rO.2 false = graphFun K A x
    rw [wiresFrom_append]
    set w1 := wiresFrom rB.1 (List.ofFn x)
    have hw1len : w1.length = n + rB.1.length := by rw [wiresFrom_length, List.length_ofFn]
    have htop_lt : ∀ i ∈ topList, i < n + rB.1.length := by
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; have := a.isLt; omega
      · exact hbltB i h
    rw [hevO w1 hw1len htop_lt, List.any_append]
    have hA_eq : (A.toList.map Fin.val).any (fun i => w1.getD i false) =
        decide (∃ a ∈ A, x a = true) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, Finset.mem_toList,
        decide_eq_true_eq]
      constructor
      · rintro ⟨a, ha, hwa⟩
        rw [wiresFrom_getD_lt _ _ _ (by simp)] at hwa
        simp only [List.getD, List.getElem?_ofFn, a.isLt, ↓reduceDIte, Option.getD_some] at hwa
        exact ⟨a, ha, hwa⟩
      · rintro ⟨a, ha, hxa⟩
        refine ⟨a, ha, ?_⟩
        rw [wiresFrom_getD_lt _ _ _ (by simp)]
        simp [List.getD, a.isLt, hxa]
    have hE_eq : rB.2.any (fun b => w1.getD b false) =
        decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true) := by
      rw [hevB x (List.ofFn x) (List.length_ofFn) (fun i => by simp [List.getD, i.isLt])]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq, nbrs,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t, _, hxt, r, hown, hxr⟩
        exact ⟨t, r, (hown_ok t r hown).1, hxt, hxr⟩
      · rintro ⟨u, v, huv, hxu, hxv⟩
        have hne := hown_uniq u v huv
        cases h1 : owns u v with
        | true => exact ⟨u, Finset.mem_toList.mpr (hown_ok u v h1).2, hxu, v, h1, hxv⟩
        | false =>
          have h2 : owns v u = true := by
            rw [h1] at hne; cases h : owns v u with
            | true => rfl
            | false => exact absurd h.symm hne
          exact ⟨v, Finset.mem_toList.mpr (hown_ok v u h2).2, hxv, u, h2, hxu⟩
    rw [hA_eq, hE_eq]; rfl
  · change (rB.1 ++ rO.1).length + 1 = A.card + K.edgeFinset.card + T.card
    rw [List.length_append]
    have htop_len : topList.length = A.card + T.card := by
      simp [topList, hblenB, ts]
    have hsum_edges : rB.1.length = K.edgeFinset.card := by
      rw [hlenB]
      have h1 : (ts.map (fun t => (nbrs t).length)).sum =
          ∑ t ∈ T, (Finset.univ.filter (fun r => owns t r = true)).card := by
        have heq_f : (ts.map (fun t => (nbrs t).length)).sum =
            (T.toList.map (fun t => (Finset.univ.filter (fun r => owns t r = true)).card)).sum := by
          congr 1; apply List.map_congr_left; intro t _; simp [nbrs]
        rw [heq_f, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [h1]
      -- Same bijection as owned_card
      have hP : ∀ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => owns p.1 p.2 = true)),
          p.1 ∈ T := fun p hp => (hown_ok p.1 p.2 (Finset.mem_filter.mp hp).2).2
      have h2 := Finset.card_eq_sum_card_fiberwise hP
      have hfib : ∀ t ∈ T,
          ((Finset.univ.filter (fun p : Fin n × Fin n => owns p.1 p.2 = true)).filter
            (fun p => p.1 = t)).card = (Finset.univ.filter (fun r => owns t r = true)).card := by
        intro t _
        symm
        apply Finset.card_bij (fun r _ => (t, r))
        · intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact ⟨hr, trivial⟩
        · intro a _ b _ h; exact (Prod.ext_iff.mp h).2
        · rintro ⟨u, v⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          obtain ⟨h1, h2⟩ := hp; subst h2
          exact ⟨v, by simpa using h1, rfl⟩
      rw [Finset.sum_congr rfl hfib] at h2
      rw [← h2]
      apply Finset.card_bij (fun p _ => s(p.1, p.2))
      · intro p hp
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact (hown_ok p.1 p.2 (Finset.mem_filter.mp hp).2).1
      · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hp' h
        have e1 : owns u v = true := (Finset.mem_filter.mp hp).2
        have e2 : owns u' v' = true := (Finset.mem_filter.mp hp').2
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exfalso; simp only at h1 h2; subst h1; subst h2
          exact hown_uniq u v (hown_ok u v e1).1 (by rw [e1, e2])
      · intro e he
        induction e using Sym2.ind with
        | _ a b =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          have hne := hown_uniq a b he
          cases hab : owns a b with
          | true => exact ⟨(a, b), by simp [hab], rfl⟩
          | false =>
            have hba : owns b a = true := by
              rw [hab] at hne; cases h : owns b a with
              | true => rfl
              | false => exact absurd h.symm hne
            exact ⟨(b, a), by simp [hba], Sym2.eq_swap⟩
    omega

/-! ### Section 3: Variable Restriction Elimination Engine on Any Coordinate l -/

private def OkG (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

private def NOkG (g : Gate) : Prop :=
  OkG g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_op (g : Gate) : (normGate g).op = g.op := by
  cases g with | mk op ins => cases op <;> rfl

private lemma normGate_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) : normGate g = g := by
  cases g with
  | mk op ins =>
    cases op
    · rfl
    · rfl
    · exact absurd rfl h
    · rfl
    · rfl

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [normGate]
  cases ins <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkG g) : NOkG (normGate g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨Or.inr (Or.inr rfl), by simp [normGate]⟩, fun _ => by simp [normGate]⟩

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private abbrev Stat := Bool ⊕ ℕ

private def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplifyGate op m ins).1, OkG g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_some_inv (op : GateOp) (m : ℕ) (ins : List Stat) (g' : Gate)
    (h : (simplifyGate op m ins).1 = some g') :
    g'.op = op ∧ (simplifyGate op m ins).2 = Sum.inr m ∧
    ((op = GateOp.and ∧ ∃ a b, ins = [Sum.inr a, Sum.inr b] ∧ g' = ⟨GateOp.and, [a, b]⟩) ∨
     (op = GateOp.or ∧ ∃ a b, ins = [Sum.inr a, Sum.inr b] ∧ g' = ⟨GateOp.or, [a, b]⟩) ∨
     (op = GateOp.not ∧ ∃ a rest, ins = Sum.inr a :: rest ∧ g' = ⟨GateOp.not, [a]⟩)) := by
  cases op <;> simp only [simplifyGate] at h
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h
    subst h; exact ⟨rfl, rfl, Or.inl ⟨rfl, _, _, rfl, rfl⟩⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h
    subst h; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, _, _, rfl, rfl⟩)⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at h
    subst h; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, _, _, rfl, rfl⟩)⟩
  · simp at h
  · simp at h

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let r := simplifyGate g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private lemma elimPass_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elimPass n (g :: gs) acc = elimPass n gs (elimStep n acc g) := rfl

private lemma elimPass_append (n : ℕ) (gs1 gs2 : List Gate) (acc : List Stat × List Gate) :
    elimPass n (gs1 ++ gs2) acc = elimPass n gs2 (elimPass n gs1 acc) := by
  induction gs1 generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_stat_len (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elimPass n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]; simp [elimStep]; omega

private lemma elimPass_stat_getD_lt (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (i : ℕ) (hi : i < acc.1.length) :
    (elimPass n gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma elimPass_ok (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (h : ∀ g ∈ acc.2, OkG g) : ∀ g ∈ (elimPass n gs acc).2, OkG g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elimPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      cases (simplifyGate g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    omega

private lemma elimPass_len_eq_all_some (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (heq : (elimPass n gs acc).2.length = acc.2.length + gs.length) :
    ∀ k (hk : k < gs.length),
      let b := elimPass n (gs.take k) acc
      ∃ g', (simplifyGate gs[k].op (n + b.2.length)
        (gs[k].inputs.map fun i => b.1.getD i (Sum.inl false))).1 = some g' := by
  induction gs generalizing acc with
  | nil => intro k hk; cases hk
  | cons g gs ih =>
    intro k hk
    have hstep_le : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      cases (simplifyGate g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have hrest_le := elimPass_len n gs (elimStep n acc g)
    rw [elimPass_cons, List.length_cons] at heq
    have hstep_eq : (elimStep n acc g).2.length = acc.2.length + 1 := by omega
    have hrest_eq : (elimPass n gs (elimStep n acc g)).2.length =
        (elimStep n acc g).2.length + gs.length := by omega
    cases k with
    | zero =>
      dsimp only [List.take, List.getElem_cons_zero]
      simp only [elimPass, List.foldl_nil]
      simp only [elimStep, List.length_append] at hstep_eq
      cases hr : (simplifyGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
      | none => rw [hr] at hstep_eq; simp at hstep_eq
      | some g' => exact ⟨g', rfl⟩
    | succ k' =>
      have hk' : k' < gs.length := by simp at hk; omega
      simpa [List.take_succ_cons, elimPass_cons] using ih (elimStep n acc g) hrest_eq k' hk'

private lemma elimPass_len_lt (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ gs, NOkG g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨_, h, _⟩ := hex; cases h
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      obtain ⟨c, hc'⟩ := hc
      have hnone : (simplifyGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
        simplifyGate_none_of_const _ _ _ hnok.1.1 (by simpa using hnok.1.2)
          (fun h => by simpa using hnok.2 h) ⟨c, List.mem_map.mpr ⟨k, hkg, hc'⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        dsimp only [elimStep]; rw [hnone]; simp
      have := elimPass_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.mp hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by obtain ⟨c, hc'⟩ := hc; exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc'⟩)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        cases (simplifyGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
      omega

private lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

private def ElimInv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

private lemma elimInv_pass (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, OkG g) →
      ElimInv n y w acc → ElimInv n y (wiresFrom gs w) (elimPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y
    have lw' : w'.length = n + acc.2.length := by rw [wiresFrom_length, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    have hgok := hok g List.mem_cons_self
    have hs := simplifyGate_sound g.op hgok.1 w' ins (by simpa [ins] using hgok.2)
      (by intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs; rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplifyGate g.op (n + acc.2.length) ins
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [List.map_map]
      exact List.map_congr_left (fun a _ => (hi a).2)
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := wiresFrom_append _ _ _
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    change statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq _ _ _ _ rfl, getD_snoc_eq _ _ _ _ hl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

private def initStatsAt (n : ℕ) (l : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = l then Sum.inl b else Sum.inr i.val)

private lemma elimInv_initAt (n : ℕ) (l : Fin n) (b : Bool) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (List.ofFn (Function.update x l b)) (initStatsAt n l b, []) := by
  refine ⟨by simp [initStatsAt], ?_⟩
  intro i
  by_cases hi : i < n
  · simp only [initStatsAt, List.getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some,
      wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
    by_cases hil : (⟨i, hi⟩ : Fin n) = l
    · subst hil; simp [statValid, statVal]
    · simp [hil, statValid, statVal, hi, Function.update_of_ne hil]
  · simp only [initStatsAt, List.getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_none]
    exact ⟨trivial, rfl⟩

private lemma wires_agree (gs : List Gate) (bad : ℕ → Prop) (w w' : List Bool)
    (hlen : w.length = w'.length)
    (hw : ∀ i, ¬ bad i → w.getD i false = w'.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ bad i) :
    ∀ i, ¬ bad i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact hw
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hv : v = v' := by
      dsimp only [v, v']; congr 1
      exact List.map_congr_left (fun i hi => hw i (hgs g List.mem_cons_self i hi))
    change ∀ i, ¬ bad i → (wiresFrom gs (w ++ [v])).getD i false =
      (wiresFrom gs (w' ++ [v'])).getD i false
    apply ih _ _ (by simp [hlen]) _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i hi
    by_cases heq : i = w.length
    · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega), hv]
    · rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

private lemma elim_one_at {n : ℕ} {C : Circuit} {l : Fin n}
    (hf : FanInTwo C)
    (hdep : ∃ x : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update x l true))
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update y l false)) :
    ∃ C' : Circuit, FanInTwo C' ∧
      circuitFun n C' = (fun x => circuitFun n C (Function.update x l false)) ∧
      C'.size + 1 ≤ C.size := by
  set gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOkG g := fun g hg => by
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hf g0 hg0)
  have hex_read : ∃ g ∈ gs, l.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout : C.output = l.val
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update y l false))).getD C.output false
      rw [hout, wiresFrom_getD_lt _ _ _ (by simp), wiresFrom_getD_lt _ _ _ (by simp)]
      simp [List.getD, l.isLt]
    · obtain ⟨x, hx⟩ := hdep
      apply hx
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update x l true))).getD C.output false
      rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
        ← wiresFrom_norm C.gates (List.ofFn (Function.update x l true))]
      refine wires_agree gs (fun i => i = l.val) _ _ (by simp) (fun i hi => ?_)
        (fun g hg i hi' => fun e => hno g hg (e ▸ hi')) C.output hout
      by_cases hilt : i < n
      · have hne : (⟨i, hilt⟩ : Fin n) ≠ l := fun e => hi (congrArg Fin.val e)
        simp [List.getD, hilt, Function.update_of_ne hne]
      · simp [List.getD, hilt]
  set res := elimPass n gs (initStatsAt n l false, [])
  have hlen : res.2.length + 1 ≤ C.gates.length := by
    have h1 := elimPass_len_lt n l.val gs (initStatsAt n l false, []) hnok
      (by simp [initStatsAt])
      ⟨false, by simp [initStatsAt, List.getD, l.isLt]⟩ hex_read
    simpa [gs] using h1
  have hinv : ∀ x : Fin n → Bool,
      ElimInv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x l false))) res :=
    fun x => elimInv_pass n (List.ofFn x) List.length_ofFn gs _ _
      (fun g hg => (hnok g hg).1) (elimInv_initAt n l false x)
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have hx := (hinv x).2 C.output
    have hy := (hinv y).2 C.output
    rw [hout] at hx hy
    change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
      (wiresFrom C.gates (List.ofFn (Function.update y l false))).getD C.output false
    rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
      ← wiresFrom_norm C.gates (List.ofFn (Function.update y l false)), ← hx.2, ← hy.2]
    rfl
  | inr o' =>
    refine ⟨⟨res.2, o'⟩, elimPass_ok n gs _ (by simp), ?_, hlen⟩
    funext x
    have hx := (hinv x).2 C.output
    rw [hout] at hx
    change (wiresFrom res.2 (List.ofFn x)).getD o' false =
      (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false
    rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false))]
    exact hx.2

private def remapW (n j0 w i : ℕ) : ℕ :=
  if i = n + j0 then w else if n + j0 < i then i - 1 else i

private lemma bad_reader_const (l m : ℕ) (stats : List Stat) (g : Gate)
    (hg : NOkG g) (hread : l ∈ g.inputs) (hfix : stats.getD l (Sum.inl false) = Sum.inl false)
    (hbad : ¬ (g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ l ∧ w < stats.length)) :
    ∃ b, (simplifyGate g.op m (g.inputs.map fun i => stats.getD i (Sum.inl false))).2 =
      Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  have hop := hg.1.1
  have hlen := hg.1.2
  simp only [List.getD_eq_getElem?_getD] at hfix
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : l = a := by simpa using hread
      subst a; exact ⟨false, by simp [simplifyGate, simpAnd, hfix]⟩
    · have hmem : l = a ∨ l = b := by simpa using hread
      rcases hmem with rfl | rfl
      · refine ⟨false, ?_⟩
        cases hb : stats[b]?.getD (Sum.inl false) <;> simp [simplifyGate, simpAnd, hfix, hb]
      · refine ⟨false, ?_⟩
        cases ha : stats[a]?.getD (Sum.inl false) <;> simp [simplifyGate, simpAnd, hfix, ha]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : l = a := by simpa using hread
      subst a; exact ⟨false, by simp [simplifyGate, simpOr, hfix]⟩
    · have hout (w : ℕ) (hw : w ∈ [a, b]) : stats[w]?.getD (Sum.inl false) = Sum.inl false := by
        by_cases hl : w = l
        · simpa only [hl] using hfix
        · have hnlt : ¬ w < stats.length := fun hlt => hbad ⟨rfl, rfl, w, hw, hl, hlt⟩
          exact List.getD_eq_default _ _ (Nat.le_of_not_gt hnlt)
      exact ⟨false, by simp [simplifyGate, simpOr, hout a (by simp), hout b (by simp)]⟩
    · simp at hlen
  · have hone := hg.2 rfl
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hread
    · have ha : l = a := by simpa using hread
      subst a; exact ⟨true, by simp [simplifyGate, simpNot, hfix]⟩
    · simp at hone

private lemma tight_elim_structure {n : ℕ} {C : Circuit} {l : Fin n}
    (hmin : IsMinimalCircuit n C)
    (hdep : ∃ x : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update x l true))
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update y l false))
    (htight : ∀ D : Circuit, FanInTwo D →
      circuitFun n D = (fun x => circuitFun n C (Function.update x l false)) →
      C.size ≤ D.size + 1) :
    ∃ (C' : Circuit) (j0 w : ℕ),
      IsMinimalCircuit n C' ∧
      circuitFun n C' = (fun x => circuitFun n C (Function.update x l false)) ∧
      C'.gates.length + 1 = C.gates.length ∧
      j0 < C.gates.length ∧ w < n + j0 ∧ w ≠ l.val ∧
      (gateAt C j0).op = GateOp.or ∧
      ((gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val]) ∧
      C.output < n + C.gates.length ∧ C.output ≠ l.val ∧
      remapW n j0 w C.output = C'.output ∧
      (∀ j < C.gates.length, j ≠ j0 →
        let j' := if j < j0 then j else j - 1
        (gateAt C' j').op = (gateAt C j).op ∧
        ((gateAt C' j').op ≠ GateOp.not →
          (gateAt C j).inputs.length = 2 ∧
          (gateAt C' j').inputs = (gateAt C j).inputs.map (remapW n j0 w) ∧
          ∀ i ∈ (gateAt C j).inputs, i < n + j ∧ i ≠ l.val)) := by
  set gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOkG g := fun g hg => by
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hmin.1 g0 hg0)
  have hex_read : ∃ (j : ℕ) (hj : j < gs.length), l.val ∈ gs[j].inputs := by
    by_contra hno
    push Not at hno
    have hno' : ∀ g ∈ gs, l.val ∉ g.inputs := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      exact hno j hj
    by_cases hout : C.output = l.val
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update y l false))).getD C.output false
      rw [hout, wiresFrom_getD_lt _ _ _ (by simp), wiresFrom_getD_lt _ _ _ (by simp)]
      simp [List.getD, l.isLt]
    · obtain ⟨x, hx⟩ := hdep
      apply hx
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update x l true))).getD C.output false
      rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
        ← wiresFrom_norm C.gates (List.ofFn (Function.update x l true))]
      refine wires_agree gs (fun i => i = l.val) _ _ (by simp) (fun i hi => ?_)
        (fun g hg i hi' => fun e => hno' g hg (e ▸ hi')) C.output hout
      by_cases hilt : i < n
      · have hne : (⟨i, hilt⟩ : Fin n) ≠ l := fun e => hi (congrArg Fin.val e)
        simp [List.getD, hilt, Function.update_of_ne hne]
      · simp [List.getD, hilt]
  obtain ⟨j0, hj0_gs, hj0_read⟩ := hex_read
  have hj0 : j0 < C.gates.length := by simpa [gs] using hj0_gs
  have hgs_j0 : gs[j0] = normGate (gateAt C j0) := by
    simp [gs, gateAt, List.getD, hj0]
  have hj0_read' : l.val ∈ (normGate (gateAt C j0)).inputs := hgs_j0 ▸ hj0_read
  set start : List Stat × List Gate := (initStatsAt n l false, [])
  set pre := gs.take j0
  set g0 := normGate (gateAt C j0)
  set post := gs.drop (j0 + 1)
  have hsplit : gs = pre ++ g0 :: post := by
    have htake := List.take_append_drop j0 gs
    have hdrop : gs.drop j0 = g0 :: post := by
      rw [List.drop_eq_getElem_cons hj0_gs, hgs_j0]
    rw [← hdrop, htake]
  set bef := elimPass n pre start
  set aft := elimStep n bef g0
  set res := elimPass n post aft
  have hres_eq : res = elimPass n gs start := by
    rw [hsplit, elimPass_append, elimPass_cons]
  have hbef_slen : bef.1.length = n + j0 := by
    rw [elimPass_stat_len]; simp [start, initStatsAt, pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]
  have hbef_l : bef.1.getD l.val (Sum.inl false) = Sum.inl false := by
    rw [elimPass_stat_getD_lt _ _ _ _ (by simp [start, initStatsAt])]
    simp [start, initStatsAt, List.getD, l.isLt]
  have hg0_nok : NOkG g0 := normGate_nok (gateAt C j0) (hmin.1 (gateAt C j0) (by
    simp [gateAt, List.getD, hj0]))
  have hg0_none : (simplifyGate g0.op (n + bef.2.length)
      (g0.inputs.map fun i => bef.1.getD i (Sum.inl false))).1 = none :=
    simplifyGate_none_of_const _ _ _ hg0_nok.1.1 (by simpa using hg0_nok.1.2)
      (fun h => by simpa using hg0_nok.2 h) ⟨false, List.mem_map.mpr ⟨l.val, hj0_read', hbef_l⟩⟩
  have haft_len : aft.2.length = bef.2.length := by dsimp only [aft, elimStep]; rw [hg0_none]; simp
  have hpre_le : bef.2.length ≤ j0 := by
    have := elimPass_len n pre start
    simpa [start, pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)] using this
  have hpost_le : res.2.length ≤ aft.2.length + post.length := elimPass_len n post aft
  have hpost_len : post.length = C.gates.length - (j0 + 1) := by simp [post, gs]
  have hres_le : res.2.length + 1 ≤ C.gates.length := by omega
  have hinv : ∀ x : Fin n → Bool,
      ElimInv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x l false))) res := by
    intro x; rw [hres_eq]
    exact elimInv_pass n (List.ofFn x) List.length_ofFn gs _ _
      (fun g hg => (hnok g hg).1) (elimInv_initAt n l false x)
  have hout_inr : ∃ o', res.1.getD C.output (Sum.inl false) = Sum.inr o' := by
    cases ho : res.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso; obtain ⟨x, y, hxy⟩ := hnc; apply hxy
      have hx := (hinv x).2 C.output; have hy := (hinv y).2 C.output
      rw [ho] at hx hy
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update y l false))).getD C.output false
      rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
        ← wiresFrom_norm C.gates (List.ofFn (Function.update y l false)), ← hx.2, ← hy.2]
      rfl
    | inr o' => exact ⟨o', rfl⟩
  obtain ⟨o', ho'⟩ := hout_inr
  let C' : Circuit := ⟨res.2, o'⟩
  have hC'_fan : FanInTwo C' := by
    intro g hg
    change g ∈ res.2 at hg
    rw [hres_eq] at hg
    exact elimPass_ok n gs start (by simp [start]) g hg
  have hC'_fun : circuitFun n C' = (fun x => circuitFun n C (Function.update x l false)) := by
    funext x
    have hx := (hinv x).2 C.output; rw [ho'] at hx
    change (wiresFrom res.2 (List.ofFn x)).getD o' false =
      (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false
    rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false))]; exact hx.2
  have hC_le : C.gates.length ≤ res.2.length + 1 := htight C' hC'_fan hC'_fun
  have hC'_len : C'.gates.length + 1 = C.gates.length := by change res.2.length + 1 = _; omega
  have hC'_min : IsMinimalCircuit n C' := by
    refine ⟨hC'_fan, fun D hDf hDfun => ?_⟩
    have hD := htight D hDf (hDfun.trans hC'_fun)
    change C.gates.length ≤ D.gates.length + 1 at hD
    change res.2.length ≤ D.gates.length; omega
  have hpre_eq : bef.2.length = j0 := by omega
  have hpost_eq : res.2.length = aft.2.length + post.length := by omega
  have hg0_shape : g0.op = GateOp.or ∧ g0.inputs.length = 2 ∧
      ∃ w ∈ g0.inputs, w ≠ l.val ∧ w < n + j0 := by
    by_contra hbad
    obtain ⟨c, hc⟩ := bad_reader_const l.val (n + bef.2.length) bef.1 g0 hg0_nok hj0_read' hbef_l
      (by simpa [hbef_slen] using hbad)
    have haft_j0 : aft.1.getD (n + j0) (Sum.inl false) = Sum.inl c := by
      simp only [aft, elimStep]
      rw [getD_snoc_eq _ _ _ _ hbef_slen.symm]; exact hc
    have hno_post_read : ∀ g ∈ post, n + j0 ∉ g.inputs := by
      intro g hg hmem
      have hlt := elimPass_len_lt n (n + j0) post aft
        (fun g' hg' => hnok g' (by rw [hsplit]; simp [hg']))
        (by simp [aft, elimStep, hbef_slen]) ⟨c, haft_j0⟩ ⟨g, hg, hmem⟩
      change res.2.length + 1 ≤ aft.2.length + post.length at hlt
      omega
    by_cases hout_j0 : C.output = n + j0
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hres_j0 : res.1.getD (n + j0) (Sum.inl false) = Sum.inl c := by
        rw [elimPass_stat_getD_lt _ _ _ _ (by simp [aft, elimStep, hbef_slen])]; exact haft_j0
      have hx := (hinv x).2 C.output; have hy := (hinv y).2 C.output
      rw [hout_j0, hres_j0] at hx hy
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update y l false))).getD C.output false
      rw [hout_j0, ← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
        ← wiresFrom_norm C.gates (List.ofFn (Function.update y l false)), ← hx.2, ← hy.2]
      rfl
    · have hno_pre_read : ∀ g ∈ pre, l.val ∉ g.inputs := by
        intro g hg hmem
        have hlt := elimPass_len_lt n l.val pre start
          (fun g' hg' => hnok g' (by rw [hsplit]; simp [hg']))
          (by simp [start, initStatsAt])
          ⟨false, by simp [start, initStatsAt, List.getD, l.isLt]⟩ ⟨g, hg, hmem⟩
        have hplen : pre.length = j0 := by simp [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]
        change bef.2.length + 1 ≤ 0 + pre.length at hlt
        omega
      have hno_post_l : ∀ g ∈ post, l.val ∉ g.inputs := by
        intro g hg hmem
        have hlt := elimPass_len_lt n l.val post aft
          (fun g' hg' => hnok g' (by rw [hsplit]; simp [hg']))
          (by simp [aft, elimStep, hbef_slen]; have := l.isLt; omega)
          ⟨false, by simp only [aft, elimStep]; rw [getD_snoc_lt _ _ _ _ (by have := l.isLt; omega)]; exact hbef_l⟩
          ⟨g, hg, hmem⟩
        change res.2.length + 1 ≤ aft.2.length + post.length at hlt
        omega
      have hout_l : C.output ≠ l.val := by
        intro heq
        have hres_l : res.1.getD l.val (Sum.inl false) = Sum.inl false := by
          rw [hres_eq, elimPass_stat_getD_lt _ _ _ _ (by simp [start, initStatsAt])]
          simp [start, initStatsAt, List.getD, l.isLt]
        rw [heq, hres_l] at ho'; cases ho'
      obtain ⟨x, hx⟩ := hdep
      apply hx
      change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom C.gates (List.ofFn (Function.update x l true))).getD C.output false
      rw [← wiresFrom_norm C.gates (List.ofFn (Function.update x l false)),
        ← wiresFrom_norm C.gates (List.ofFn (Function.update x l true))]
      change (wiresFrom gs (List.ofFn (Function.update x l false))).getD C.output false =
        (wiresFrom gs (List.ofFn (Function.update x l true))).getD C.output false
      rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons]
      have hpre_ag := wires_agree pre (fun i => i = l.val)
        (List.ofFn (Function.update x l false)) (List.ofFn (Function.update x l true))
        (by simp)
        (fun i hi => by
          by_cases hilt : i < n
          · have hne : (⟨i, hilt⟩ : Fin n) ≠ l := fun e => hi (congrArg Fin.val e)
            simp [List.getD, hilt, Function.update_of_ne hne]
          · simp [List.getD, hilt])
        (fun g hg i hi e => hno_pre_read g hg (e ▸ hi))
      have hwpre_len : (wiresFrom pre (List.ofFn (Function.update x l false))).length = n + j0 := by
        rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]
      have hwpre_len' : (wiresFrom pre (List.ofFn (Function.update x l true))).length = n + j0 := by
        rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]
      refine wires_agree post (fun i => i = l.val ∨ i = n + j0) _ _ (by simp [hwpre_len, hwpre_len'])
        (fun i hi => ?_) (fun g hg i hi h => by
          rcases h with rfl | rfl
          · exact hno_post_l g hg hi
          · exact hno_post_read g hg hi)
        C.output (fun h => by rcases h with h | h; exact hout_l h; exact hout_j0 h)
      have hne1 : i ≠ l.val := fun e => hi (Or.inl e)
      have hne2 : i ≠ n + j0 := fun e => hi (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hpre_ag i hne1
  obtain ⟨hg0_op, hg0_len, w, hw_mem, hw_nel, hw_lt⟩ := hg0_shape
  have hgate_j0_op : (gateAt C j0).op = GateOp.or := by
    rw [← normGate_op (gateAt C j0)]; exact hg0_op
  have hg0_eq : g0 = gateAt C j0 := normGate_of_ne_not _ (by rw [hgate_j0_op]; intro h; cases h)
  have hgate_j0_ins : (gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val] := by
    rw [← hg0_eq]
    rcases h : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp [h] at hg0_len
    · simp [h] at hg0_len
    · rw [h] at hj0_read' hw_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj0_read' hw_mem
      rcases hj0_read' with rfl | rfl <;> rcases hw_mem with rfl | rfl
      · exact absurd rfl hw_nel
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hw_nel
    · simp [h] at hg0_len
  have hpre_some := elimPass_len_eq_all_some n pre start (by
    rw [hpre_eq]; simp [start, pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)])
  have hpost_some := elimPass_len_eq_all_some n post aft hpost_eq
  have hpre_track : ∀ k ≤ j0,
      let b := elimPass n (pre.take k) start
      b.2.length = k ∧
      (∀ i < n + k, b.1.getD i (Sum.inl false) =
        if i = l.val then Sum.inl false else Sum.inr i) ∧
      (∀ j (hj' : j < k), ∃ g', b.2[j]? = some g' ∧
        (simplifyGate (pre.getD j ⟨GateOp.or, []⟩).op (n + j)
          ((pre.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
            (elimPass n (pre.take j) start).1.getD i (Sum.inl false))).1 = some g') := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨rfl, fun i hi => ?_, fun j hj => by omega⟩
      have hi' : i < n := by omega
      simp only [List.take, elimPass, List.foldl_nil, start, initStatsAt, List.getD,
        List.getElem?_ofFn, hi', ↓reduceDIte, Option.getD_some]
      by_cases hil : i = l.val
      · subst hil; simp
      · have hne : (⟨i, hi'⟩ : Fin n) ≠ l := fun e => hil (congrArg Fin.val e)
        simp [hil, hne]
    | succ k ih =>
      intro hk
      obtain ⟨hlenk, hstatk, hgk⟩ := ih (by omega)
      have hk_pre : k < pre.length := by
        simp [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]; omega
      have htake_succ : pre.take (k + 1) = pre.take k ++ [pre[k]] := List.take_succ_eq_append_getElem hk_pre
      obtain ⟨g', hg'⟩ := hpre_some k hk_pre
      have hinv_s := simplifyGate_some_inv _ _ _ g' hg'
      set bk := elimPass n (pre.take k) start
      have hbk_slen : bk.1.length = n + k := by
        rw [elimPass_stat_len]; simp [start, initStatsAt, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk_pre)]
      have hstep_eq : elimPass n (pre.take (k + 1)) start = elimStep n bk pre[k] := by
        rw [htake_succ, elimPass_append]; rfl
      rw [hstep_eq]
      have hlen_succ : (elimStep n bk pre[k]).2.length = k + 1 := by
        dsimp only [elimStep]; rw [hg']; simp [hlenk]
      refine ⟨hlen_succ, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = n + k
        · subst hik
          simp only [elimStep]
          rw [getD_snoc_eq _ _ _ _ hbk_slen.symm, hinv_s.2.1, hlenk]
          have hnel : n + k ≠ l.val := by have := l.isLt; omega
          simp [hnel]
        · simp only [elimStep]
          rw [getD_snoc_lt _ _ _ _ (by omega)]
          exact hstatk i (by omega)
      · intro j hj
        by_cases hjk : j = k
        · subst hjk
          refine ⟨g', ?_, ?_⟩
          · dsimp only [elimStep]; rw [hg']
            rw [List.getElem?_append_right (by omega : bk.2.length ≤ j)]
            simp [hlenk]
          · have hgetD : pre.getD j ⟨GateOp.or, []⟩ = pre[j] := List.getD_eq_getElem _ _ hk_pre
            rw [hgetD, show n + j = n + bk.2.length by omega]; exact hg'
        · obtain ⟨gj, hgj1, hgj2⟩ := hgk j (by omega)
          refine ⟨gj, ?_, hgj2⟩
          simp only [elimStep]
          rw [List.getElem?_append_left (by omega : j < bk.2.length)]
          exact hgj1
  have hbef_eq_take : pre.take j0 = pre := List.take_of_length_le (by simp [pre])
  obtain ⟨_, hbef_stat, hbef_gates⟩ := hpre_track j0 (le_refl j0)
  rw [hbef_eq_take] at hbef_stat hbef_gates
  have haft_j0_w : aft.1.getD (n + j0) (Sum.inl false) = Sum.inr w := by
    dsimp only [aft, elimStep]
    rw [getD_snoc_eq _ _ _ _ hbef_slen.symm]
    have hbw : bef.1.getD w (Sum.inl false) = Sum.inr w := by
      rw [hbef_stat w hw_lt, if_neg hw_nel]
    rw [hg0_eq, hgate_j0_op]
    rcases hgate_j0_ins with h | h <;> rw [h]
    · simp only [List.map_cons, List.map_nil, hbef_l, hbw, simplifyGate, simpOr]; rfl
    · simp only [List.map_cons, List.map_nil, hbef_l, hbw, simplifyGate, simpOr]; rfl
  have haft_stat : ∀ i < n + j0 + 1, aft.1.getD i (Sum.inl false) =
      if i = l.val then Sum.inl false else Sum.inr (remapW n j0 w i) := by
    intro i hi
    by_cases hij : i = n + j0
    · subst hij
      have hnel : n + j0 ≠ l.val := by have := l.isLt; omega
      rw [if_neg hnel, haft_j0_w]; simp [remapW]
    · simp only [aft, elimStep]
      rw [getD_snoc_lt _ _ _ _ (by omega), hbef_stat i (by omega)]
      by_cases hil : i = l.val
      · simp [hil]
      · simp [hil, remapW, show ¬ n + j0 < i by omega, hij]
  have hpost_track : ∀ k ≤ post.length,
      let b := elimPass n (post.take k) aft
      b.2.length = j0 + k ∧
      (∀ i < n + j0 + 1 + k, b.1.getD i (Sum.inl false) =
        if i = l.val then Sum.inl false else Sum.inr (remapW n j0 w i)) ∧
      (∀ t (ht' : t < k), ∃ g', b.2[j0 + t]? = some g' ∧
        (simplifyGate (post.getD t ⟨GateOp.or, []⟩).op (n + j0 + t)
          ((post.getD t ⟨GateOp.or, []⟩).inputs.map fun i =>
            (elimPass n (post.take t) aft).1.getD i (Sum.inl false))).1 = some g') := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [elimPass, haft_len, hpre_eq], fun i hi => by
        simpa [elimPass] using haft_stat i (by omega), fun t ht => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨hlenk, hstatk, hgk⟩ := ih (by omega)
      have hk_post : k < post.length := by omega
      have htake_succ : post.take (k + 1) = post.take k ++ [post[k]] :=
        List.take_succ_eq_append_getElem hk_post
      obtain ⟨g', hg'⟩ := hpost_some k hk_post
      have hinv_s := simplifyGate_some_inv _ _ _ g' hg'
      set bk := elimPass n (post.take k) aft
      have hbk_slen : bk.1.length = n + j0 + 1 + k := by
        rw [elimPass_stat_len]; simp [aft, elimStep, hbef_slen, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hk_post)]
      have hstep_eq : elimPass n (post.take (k + 1)) aft = elimStep n bk post[k] := by
        rw [htake_succ, elimPass_append]; rfl
      rw [hstep_eq]
      have hlen_succ : (elimStep n bk post[k]).2.length = j0 + (k + 1) := by
        dsimp only [elimStep]; rw [hg']; simp [hlenk]; omega
      refine ⟨hlen_succ, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = n + j0 + 1 + k
        · subst hik
          simp only [elimStep]
          rw [getD_snoc_eq _ _ _ _ hbk_slen.symm, hinv_s.2.1, hlenk]
          have hnel : n + j0 + 1 + k ≠ l.val := by have := l.isLt; omega
          rw [if_neg hnel]
          simp [remapW, show n + j0 + 1 + k ≠ n + j0 by omega,
            show n + j0 < n + j0 + 1 + k by omega]; omega
        · simp only [elimStep]
          rw [getD_snoc_lt _ _ _ _ (by omega)]
          exact hstatk i (by omega)
      · intro t ht
        by_cases htk : t = k
        · subst htk
          refine ⟨g', ?_, ?_⟩
          · dsimp only [elimStep]; rw [hg']
            rw [List.getElem?_append_right (by omega : bk.2.length ≤ j0 + t)]
            simp [hlenk]
          · have hgetD : post.getD t ⟨GateOp.or, []⟩ = post[t] := List.getD_eq_getElem _ _ hk_post
            rw [hgetD, show n + j0 + t = n + bk.2.length by omega]; exact hg'
        · obtain ⟨gt, hgt1, hgt2⟩ := hgk t (by omega)
          refine ⟨gt, ?_, hgt2⟩
          simp only [elimStep]
          rw [List.getElem?_append_left (by omega : j0 + t < bk.2.length)]
          exact hgt1
  have hpost_eq_take : post.take post.length = post := List.take_length
  obtain ⟨_, hres_stat, hpost_gates⟩ := hpost_track post.length (le_refl _)
  rw [hpost_eq_take] at hres_stat hpost_gates
  have hres_slen : res.1.length = n + C.gates.length := by
    rw [hres_eq, elimPass_stat_len]; simp [start, initStatsAt, gs]
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have hdef : res.1.getD C.output (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdef] at ho'; cases ho'
  have hout_spec := hres_stat C.output (by omega)
  have hout_nel : C.output ≠ l.val := by
    intro heq
    rw [heq] at hout_spec ho'
    rw [if_pos rfl] at hout_spec
    rw [hout_spec] at ho'; cases ho'
  have hout_remap : remapW n j0 w C.output = C'.output := by
    rw [if_neg hout_nel] at hout_spec
    rw [hout_spec] at ho'; injection ho'
  refine ⟨C', j0, w, hC'_min, hC'_fun, hC'_len, hj0, hw_lt, hw_nel, hgate_j0_op, hgate_j0_ins,
    hout_lt, hout_nel, hout_remap, ?_⟩
  intro j hj hjne
  dsimp only
  by_cases hlt : j < j0
  · rw [if_pos hlt]
    obtain ⟨g', hg'1, hg'2⟩ := hbef_gates j hlt
    have hpre_j : pre.getD j ⟨GateOp.or, []⟩ = normGate (gateAt C j) := by
      have hjpre : j < pre.length := by
        simp [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0_gs)]; omega
      rw [List.getD_eq_getElem _ _ hjpre]
      have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      rw [hgate]; simp [pre, gs]
    rw [hpre_j] at hg'2
    have hinv_s := simplifyGate_some_inv _ _ _ g' hg'2
    have hC'_j : gateAt C' j = g' := by
      have hres_pre : res.2[j]? = bef.2[j]? := by
        have hstep_app : ∃ tail, res.2 = bef.2 ++ tail := by
          have h1 : ∀ (l : List Gate) (a : List Stat × List Gate), ∃ t, (elimPass n l a).2 = a.2 ++ t := by
            intro l; induction l with
            | nil => intro a; exact ⟨[], by simp [elimPass]⟩
            | cons g l ih =>
              intro a; rw [elimPass_cons]
              obtain ⟨t, ht⟩ := ih (elimStep n a g)
              exact ⟨(simplifyGate g.op (n + a.2.length)
                (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1.toList ++ t,
                by rw [ht]; simp [elimStep, List.append_assoc]⟩
          obtain ⟨t, ht⟩ := h1 post aft
          exact ⟨t, by rw [ht]; dsimp only [aft, elimStep]; rw [hg0_none]; simp⟩
        obtain ⟨tail, htail⟩ := hstep_app
        rw [htail, List.getElem?_append_left (by omega : j < bef.2.length)]
      have : C'.gates[j]? = some g' := by change res.2[j]? = some g'; rw [hres_pre, hg'1]
      simp [gateAt, List.getD, this]
    have hnorm_op : (normGate (gateAt C j)).op = (gateAt C j).op := normGate_op (gateAt C j)
    refine ⟨by rw [hC'_j, hinv_s.1, hnorm_op], ?_⟩
    intro hnot
    have hne_not : (gateAt C j).op ≠ GateOp.not := by
      rw [← hnorm_op, ← hinv_s.1, ← hC'_j]; exact hnot
    have hnorm_id : normGate (gateAt C j) = gateAt C j := normGate_of_ne_not _ hne_not
    rw [hnorm_id] at hg'2 hinv_s
    set bj := elimPass n (pre.take j) start
    have hbj_slen : bj.1.length = n + j := by
      rw [elimPass_stat_len]; simp [start, initStatsAt, pre, List.length_take]
      omega
    obtain ⟨_, hbj_stat, _⟩ := hpre_track j (by omega)
    have hmap_eq : ∃ a b, (gateAt C j).inputs.map (fun i => bj.1.getD i (Sum.inl false)) =
        [Sum.inr a, Sum.inr b] ∧ g'.inputs = [a, b] := by
      rcases hinv_s.2.2 with ⟨_, a, b, hm, rfl⟩ | ⟨_, a, b, hm, rfl⟩ | ⟨h1, _⟩
      · exact ⟨a, b, hm, rfl⟩
      · exact ⟨a, b, hm, rfl⟩
      · exact absurd h1 hne_not
    obtain ⟨a, b, hm, hgin⟩ := hmap_eq
    rcases hins : (gateAt C j).inputs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩
    · simp [hins] at hm
    · simp [hins] at hm
    · rw [hins] at hm
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      have harg : ∀ x y, bj.1.getD x (Sum.inl false) = Sum.inr y →
          x < n + j ∧ x ≠ l.val ∧ remapW n j0 w x = y := by
        intro x y hxy
        have hxlt : x < n + j := by
          by_contra hge
          have := List.getD_eq_default bj.1 (Sum.inl false) (by omega : bj.1.length ≤ x)
          rw [this] at hxy; cases hxy
        have hsx := hbj_stat x hxlt
        have hxnel : x ≠ l.val := by
          intro e; rw [e] at hsx hxy; rw [if_pos rfl] at hsx; rw [hsx] at hxy; cases hxy
        rw [if_neg hxnel] at hsx
        rw [hsx] at hxy; injection hxy with heq
        refine ⟨hxlt, hxnel, ?_⟩
        unfold remapW; rw [if_neg (by omega), if_neg (by omega)]; exact heq
      obtain ⟨hx1lt, hx1l, hx1r⟩ := harg x1 a hm.1
      obtain ⟨hx2lt, hx2l, hx2r⟩ := harg x2 b hm.2
      refine ⟨rfl, ?_, ?_⟩
      · rw [hC'_j, hgin]; simp [hx1r, hx2r]
      · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hx1lt, hx1l⟩
        · exact ⟨hx2lt, hx2l⟩
    · simp [hins] at hm
  · rw [if_neg hlt]
    set t := j - 1 - j0
    have hjt : j = j0 + 1 + t := by omega
    have ht_lt : t < post.length := by omega
    obtain ⟨g', hg'1, hg'2⟩ := hpost_gates t ht_lt
    have hpost_t : post.getD t ⟨GateOp.or, []⟩ = normGate (gateAt C j) := by
      rw [List.getD_eq_getElem _ _ ht_lt]
      have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      rw [hgate]; simp [post, gs, hjt]
    rw [hpost_t] at hg'2
    have hinv_s := simplifyGate_some_inv _ _ _ g' hg'2
    have hidx : j - 1 = j0 + t := by omega
    have hC'_j : gateAt C' (j - 1) = g' := by
      have : C'.gates[j - 1]? = some g' := by change res.2[j - 1]? = some g'; rw [hidx]; exact hg'1
      simp [gateAt, List.getD, this]
    have hnorm_op : (normGate (gateAt C j)).op = (gateAt C j).op := normGate_op (gateAt C j)
    refine ⟨by rw [hC'_j, hinv_s.1, hnorm_op], ?_⟩
    intro hnot
    have hne_not : (gateAt C j).op ≠ GateOp.not := by
      rw [← hnorm_op, ← hinv_s.1, ← hC'_j]; exact hnot
    have hnorm_id : normGate (gateAt C j) = gateAt C j := normGate_of_ne_not _ hne_not
    rw [hnorm_id] at hg'2 hinv_s
    set bt := elimPass n (post.take t) aft
    have hbt_slen : bt.1.length = n + j := by
      rw [elimPass_stat_len]; simp [aft, elimStep, hbef_slen, List.length_take,
        Nat.min_eq_left (by omega : t ≤ post.length)]; omega
    obtain ⟨_, hbt_stat, _⟩ := hpost_track t (by omega)
    have hmap_eq : ∃ a b, (gateAt C j).inputs.map (fun i => bt.1.getD i (Sum.inl false)) =
        [Sum.inr a, Sum.inr b] ∧ g'.inputs = [a, b] := by
      rcases hinv_s.2.2 with ⟨_, a, b, hm, rfl⟩ | ⟨_, a, b, hm, rfl⟩ | ⟨h1, _⟩
      · exact ⟨a, b, hm, rfl⟩
      · exact ⟨a, b, hm, rfl⟩
      · exact absurd h1 hne_not
    obtain ⟨a, b, hm, hgin⟩ := hmap_eq
    rcases hins : (gateAt C j).inputs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩
    · simp [hins] at hm
    · simp [hins] at hm
    · rw [hins] at hm
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      have harg : ∀ x y, bt.1.getD x (Sum.inl false) = Sum.inr y →
          x < n + j ∧ x ≠ l.val ∧ remapW n j0 w x = y := by
        intro x y hxy
        have hxlt : x < n + j := by
          by_contra hge
          have := List.getD_eq_default bt.1 (Sum.inl false) (by omega : bt.1.length ≤ x)
          rw [this] at hxy; cases hxy
        have hsx := hbt_stat x (by omega)
        have hxnel : x ≠ l.val := by
          intro e; rw [e] at hsx hxy; rw [if_pos rfl] at hsx; rw [hsx] at hxy; cases hxy
        rw [if_neg hxnel] at hsx
        rw [hsx] at hxy; injection hxy with heq
        exact ⟨hxlt, hxnel, heq⟩
      obtain ⟨hx1lt, hx1l, hx1r⟩ := harg x1 a hm.1
      obtain ⟨hx2lt, hx2l, hx2r⟩ := harg x2 b hm.2
      refine ⟨rfl, ?_, ?_⟩
      · rw [hC'_j, hgin]; simp [hx1r, hx2r]
      · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hx1lt, hx1l⟩
        · exact ⟨hx2lt, hx2l⟩
    · simp [hins] at hm

/-! ### Section 4: Wire Shift Helpers, Splice-Back Analysis, and Main Theorem -/

private def shiftW (n j0 a : ℕ) : ℕ :=
  if a < n + j0 then a else a + 1

private def shiftG (j0 j' : ℕ) : ℕ :=
  if j' < j0 then j' else j' + 1

private def unshiftG (j0 j : ℕ) : ℕ :=
  if j < j0 then j else j - 1

private lemma shiftW_add (n j0 j' : ℕ) : shiftW n j0 (n + j') = n + shiftG j0 j' := by
  unfold shiftW shiftG
  by_cases h : j' < j0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]; omega

private lemma shiftW_lt_n (n j0 a : ℕ) (ha : a < n) : shiftW n j0 a = a := by
  unfold shiftW; rw [if_pos (by omega)]

private lemma shiftW_ne_j0 (n j0 a : ℕ) : shiftW n j0 a ≠ n + j0 := by
  unfold shiftW; split_ifs <;> omega

private lemma shiftG_ne (j0 j' : ℕ) : shiftG j0 j' ≠ j0 := by
  unfold shiftG; split_ifs <;> omega

private lemma shiftG_inj (j0 : ℕ) : Function.Injective (shiftG j0) := by
  intro a b h
  unfold shiftG at h
  split_ifs at h <;> omega

private lemma shiftW_inj (n j0 : ℕ) : Function.Injective (shiftW n j0) := by
  intro a b h
  unfold shiftW at h
  split_ifs at h <;> omega

private lemma unshiftG_shiftG (j0 j' : ℕ) : unshiftG j0 (shiftG j0 j') = j' := by
  unfold unshiftG shiftG
  by_cases h : j' < j0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg (by omega)]; omega

private lemma shiftG_unshiftG (j0 j : ℕ) (h : j ≠ j0) : shiftG j0 (unshiftG j0 j) = j := by
  unfold unshiftG shiftG
  by_cases hlt : j < j0
  · rw [if_pos hlt, if_pos hlt]
  · rw [if_neg hlt, if_neg (by omega)]; omega

private lemma remapW_shiftW (n j0 w a : ℕ) : remapW n j0 w (shiftW n j0 a) = a := by
  unfold remapW shiftW
  by_cases h : a < n + j0
  · rw [if_pos h, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h, if_neg (by omega), if_pos (by omega)]; omega

private lemma remapW_eq_iff (n j0 w i a : ℕ) (h : remapW n j0 w i = a) :
    i = shiftW n j0 a ∨ (a = w ∧ i = n + j0) := by
  unfold remapW at h
  by_cases h1 : i = n + j0
  · rw [if_pos h1] at h
    exact Or.inr ⟨h.symm, h1⟩
  · rw [if_neg h1] at h
    left
    unfold shiftW
    by_cases h2 : n + j0 < i
    · rw [if_pos h2] at h; rw [if_neg (by omega)]; omega
    · rw [if_neg h2] at h; rw [if_pos (by omega)]; exact h

private lemma shiftW_remapW_of_ne (n j0 w i : ℕ) (hne : i ≠ n + j0) :
    shiftW n j0 (remapW n j0 w i) = i := by
  rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with h | ⟨_, h⟩
  · exact h.symm
  · exact absurd h hne

private lemma valid_gate_op {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.or ∨ (gateAt C j).op = GateOp.and := by
  rcases hv.2.2.2.2.1 j hj with htop | ⟨t, ht, heq, hb⟩
  · have hmem : j ∈ topGates d C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, htop⟩
    exact Or.inl (hv.2.2.2.2.2.2.1 j hmem).1
  · cases hkind : (d.role j).1 with
    | top =>
      have hmem : j ∈ topGates d C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hkind⟩
      exact Or.inl (hv.2.2.2.2.2.2.1 j hmem).1
    | z =>
      have hmem : j ∈ gatesOf d C Kind.z t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hkind heq⟩
      exact Or.inl ((hv.2.2.2.2.2.1 t ht).2.1.1 j hmem).1
    | o =>
      have hmem : j ∈ gatesOf d C Kind.o t.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hkind heq⟩
      exact Or.inl ((hv.2.2.2.2.2.1 t ht).2.2.1.1 j hmem).1
    | b =>
      have hbw := hb hkind
      obtain ⟨jb, _, hbw', _, hop, _⟩ := (hv.2.2.2.2.2.1 t ht).1
      have : j = jb := by omega
      subst this; exact Or.inr hop

private lemma exists_minimal_of_circuit {n : ℕ} (D : Circuit) (hDf : FanInTwo D) :
    ∃ Dmin : Circuit, IsMinimalCircuit n Dmin ∧ circuitFun n Dmin = circuitFun n D ∧
      Dmin.size ≤ D.size := by
  classical
  have hex : ∃ s : ℕ, ∃ E : Circuit, FanInTwo E ∧ circuitFun n E = circuitFun n D ∧ E.size = s :=
    ⟨D.size, D, hDf, rfl, rfl⟩
  obtain ⟨Dmin, hEf, hEfun, hEsz⟩ := Nat.find_spec hex
  refine ⟨Dmin, ⟨hEf, fun E hEf' hEfun' => ?_⟩, hEfun, ?_⟩
  · rw [hEsz]
    exact Nat.find_min' hex ⟨E, hEf', hEfun'.trans hEfun, rfl⟩
  · rw [hEsz]
    exact Nat.find_min' hex ⟨D, hDf, rfl, rfl⟩

private lemma list_count_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (a : α) :
    (l.map f).count (f a) = l.count a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.count_cons, ih]
    by_cases h : x = a
    · subst h; simp
    · have hne : f x ≠ f a := fun e => h (hf e)
      simp [beq_iff_eq, h, hne]

private lemma list_count_map_not_mem {α β : Type*} [DecidableEq β]
    (f : α → β) (l : List α) (b : β) (hb : ∀ a ∈ l, f a ≠ b) :
    (l.map f).count b = 0 := by
  apply List.count_eq_zero.mpr
  intro h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  exact hb a ha rfl

private lemma orTree_shift {n j0 : ℕ} {C C' : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (htree : IsOrTree n C' G L ρ)
    (hgate : ∀ j' ∈ G, (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0)) :
    IsOrTree n C (G.image (shiftG j0)) (L.image (shiftW n j0)) (shiftW n j0 ρ) := by
  obtain ⟨hg, hl, hgg, hroot⟩ := htree
  have hreads_img : ∀ u : ℕ, readsIn C (G.image (shiftG j0)) (shiftW n j0 u) = readsIn C' G u := by
    intro u
    unfold readsIn
    rw [Finset.sum_image (fun a _ b _ h => shiftG_inj j0 h)]
    apply Finset.sum_congr rfl
    intro j' hj'
    rw [(hgate j' hj').2]
    exact list_count_map_inj (shiftW n j0) (shiftW_inj n j0) _ u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hop, hin⟩ := hgate j' hj'
    obtain ⟨hop', hlen', hmem'⟩ := hg j' hj'
    refine ⟨hop.trans hop', by rw [hin, List.length_map, hlen'], ?_⟩
    intro i hi
    rw [hin] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    rcases hmem' a ha with h1 | ⟨h1, h2⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨a, h1, rfl⟩)
    · right
      have ha_eq : a = n + (a - n) := by omega
      rw [ha_eq, shiftW_add]
      exact ⟨Nat.le_add_right _ _, by simpa using Finset.mem_image.mpr ⟨a - n, h2, rfl⟩⟩
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hnot, hrc⟩ := hl a ha
    refine ⟨?_, ?_⟩
    · rintro ⟨hnu, hmem⟩
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hmem
      have hsh : shiftW n j0 a = shiftW n j0 (n + j') := by rw [shiftW_add]; omega
      have ha_eq : a = n + j' := shiftW_inj n j0 hsh
      exact hnot ⟨by omega, by simpa [ha_eq] using hj'⟩
    · rw [hreads_img a, hrc]
      by_cases h : a = ρ
      · simp [h]
      · have hne : shiftW n j0 a ≠ shiftW n j0 ρ := fun e => h (shiftW_inj n j0 e)
        simp [h, hne]
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    rw [← shiftW_add, hreads_img (n + j'), hgg j' hj']
    by_cases h : n + j' = ρ
    · simp [h]
    · have hne : shiftW n j0 (n + j') ≠ shiftW n j0 ρ := fun e => h (shiftW_inj n j0 e)
      simp [h, hne]
  · by_cases hG : G = ∅
    · subst hG
      rw [if_pos rfl] at hroot
      simp [hroot]
    · have hG' : G.image (shiftG j0) ≠ ∅ := by
        intro h; exact hG (Finset.image_eq_empty.mp h)
      rw [if_neg hG] at hroot
      rw [if_neg hG']
      obtain ⟨j', hj', rfl⟩ := hroot
      exact ⟨shiftG j0 j', Finset.mem_image.mpr ⟨j', hj', rfl⟩, shiftW_add n j0 j'⟩

private lemma orTree_splice_root {n j0 w : ℕ} {l : Fin n} {C C' : Circuit} {G L : Finset ℕ}
    (htree : IsOrTree n C' G L w)
    (hw_lt : w < n + j0) (hw_nel : w ≠ l.val) (hl_not : l.val ∉ L)
    (hj0_op : (gateAt C j0).op = GateOp.or)
    (hj0_ins : (gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val])
    (hgate : ∀ j' ∈ G, (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0)) :
    IsOrTree n C (insert j0 (G.image (shiftG j0)))
      (insert l.val (L.image (shiftW n j0))) (n + j0) := by
  have hsh := orTree_shift htree hgate
  have hw_sh : shiftW n j0 w = w := by unfold shiftW; rw [if_pos hw_lt]
  rw [hw_sh] at hsh
  have hj0_not : j0 ∉ G.image (shiftG j0) := by
    intro h; obtain ⟨j', _, heq⟩ := Finset.mem_image.mp h; exact shiftG_ne j0 j' heq
  have hj0_cnt : ∀ u, (gateAt C j0).inputs.count u =
      (if u = l.val then 1 else 0) + (if u = w then 1 else 0) := by
    intro u
    rcases hj0_ins with h | h <;> rw [h]
    · by_cases h1 : u = l.val <;> by_cases h2 : u = w
      · exact absurd (h2.symm.trans h1) hw_nel
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel]
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel, Ne.symm h1]
      · simp [h1, h2, beq_iff_eq, Ne.symm h1, Ne.symm h2]
    · by_cases h1 : u = l.val <;> by_cases h2 : u = w
      · exact absurd (h2.symm.trans h1) hw_nel
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel]
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel, Ne.symm h1]
      · simp [h1, h2, beq_iff_eq, Ne.symm h1, Ne.symm h2]
  have hreads_ins : ∀ u, readsIn C (insert j0 (G.image (shiftG j0))) u =
      (gateAt C j0).inputs.count u + readsIn C (G.image (shiftG j0)) u := fun u =>
    Finset.sum_insert hj0_not
  have hreads_l : readsIn C (G.image (shiftG j0)) l.val = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    rw [(hgate j' hj').2]
    apply list_count_map_not_mem
    intro a ha heq
    have ha_l : a = l.val := shiftW_inj n j0 (heq.trans (shiftW_lt_n n j0 l.val l.isLt).symm)
    subst ha_l
    rcases (htree.1 j' hj').2.2 l.val ha with h1 | ⟨h1, _⟩
    · exact hl_not h1
    · have := l.isLt; omega
  have hreads_j0 : readsIn C (G.image (shiftG j0)) (n + j0) = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    rw [(hgate j' hj').2]
    exact list_count_map_not_mem _ _ _ (fun a _ => shiftW_ne_j0 n j0 a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · refine ⟨hj0_op, by rcases hj0_ins with h | h <;> simp [h], ?_⟩
      intro i hi
      have hm : i = l.val ∨ i = w := by
        rcases hj0_ins with h | h <;> rw [h] at hi <;> simp at hi <;> tauto
      rcases hm with rfl | rfl
      · exact Or.inl (Finset.mem_insert_self _ _)
      · rcases orTree_top_mem hsh with hwL | ⟨h1, h2⟩
        · exact Or.inl (Finset.mem_insert_of_mem hwL)
        · exact Or.inr ⟨h1, Finset.mem_insert_of_mem h2⟩
    · obtain ⟨hop, hlen, hmem⟩ := hsh.1 j hj'
      refine ⟨hop, hlen, fun i hi => ?_⟩
      rcases hmem i hi with h1 | ⟨h1, h2⟩
      · exact Or.inl (Finset.mem_insert_of_mem h1)
      · exact Or.inr ⟨h1, Finset.mem_insert_of_mem h2⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu'
    · have hne : l.val ≠ n + j0 := by have := l.isLt; omega
      refine ⟨fun ⟨h1, _⟩ => by have := l.isLt; omega, ?_⟩
      rw [hreads_ins, hj0_cnt, hreads_l, if_pos rfl, if_neg hw_nel.symm, if_neg hne]
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu'
      have hne_j0 : shiftW n j0 a ≠ n + j0 := shiftW_ne_j0 n j0 a
      have hne_l : shiftW n j0 a ≠ l.val := by
        intro e
        have : a = l.val := shiftW_inj n j0 (e.trans (shiftW_lt_n n j0 l.val l.isLt).symm)
        exact hl_not (this ▸ ha)
      obtain ⟨hnot, hrc⟩ := hsh.2.1 (shiftW n j0 a) hu'
      refine ⟨?_, ?_⟩
      · rintro ⟨h1, h2⟩
        rcases Finset.mem_insert.mp h2 with heq | hmem
        · exact hne_j0 (by omega)
        · exact hnot ⟨h1, hmem⟩
      · rw [hreads_ins, hj0_cnt, if_neg hne_l, hrc, if_neg hne_j0]
        by_cases haw : shiftW n j0 a = w <;> simp [haw]
  · intro j hj
    rcases Finset.mem_insert.mp hj with hj_eq | hj'
    · rw [hj_eq, hreads_ins, hj0_cnt, hreads_j0, if_pos rfl, if_neg (by have := l.isLt; omega),
        if_neg (by omega)]
    · have hne_j0 : n + j ≠ n + j0 := fun e => hj0_not ((show j = j0 by omega) ▸ hj')
      have hne_l : n + j ≠ l.val := by have := l.isLt; omega
      rw [hreads_ins, hj0_cnt, if_neg hne_l, hsh.2.2.1 j hj', if_neg hne_j0]
      by_cases hjw : n + j = w <;> simp [hjw]
  · rw [if_neg (Finset.insert_ne_empty _ _)]
    exact ⟨j0, Finset.mem_insert_self _ _, rfl⟩

private lemma orTree_splice_inner {n j0 w : ℕ} {l : Fin n} {C C' : Circuit} {G L : Finset ℕ}
    {ρ g1 : ℕ}
    (htree : IsOrTree n C' G L ρ) (hw_ne : w ≠ ρ) (hw_lt : w < n + j0) (hw_nel : w ≠ l.val)
    (hl_not : l.val ∉ L) (hw_mem : w ∈ L ∨ (n ≤ w ∧ w - n ∈ G))
    (hg1 : g1 ∈ G) (hg1_op : (gateAt C (shiftG j0 g1)).op = (gateAt C' g1).op)
    (hg1_in : ∃ b, b ≠ w ∧
      ((gateAt C' g1).inputs = [w, b] ∧ (gateAt C (shiftG j0 g1)).inputs = [n + j0, shiftW n j0 b] ∨
       (gateAt C' g1).inputs = [b, w] ∧ (gateAt C (shiftG j0 g1)).inputs = [shiftW n j0 b, n + j0]))
    (hj0_op : (gateAt C j0).op = GateOp.or)
    (hj0_ins : (gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val])
    (hother : ∀ j' ∈ G, j' ≠ g1 → (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0)) :
    IsOrTree n C (insert j0 (G.image (shiftG j0)))
      (insert l.val (L.image (shiftW n j0))) (shiftW n j0 ρ) := by
  obtain ⟨b, hbw, hg1_cases⟩ := hg1_in
  have hw_sh : shiftW n j0 w = w := by unfold shiftW; rw [if_pos hw_lt]
  have hj0_not : j0 ∉ G.image (shiftG j0) := by
    intro h; obtain ⟨j', _, heq⟩ := Finset.mem_image.mp h; exact shiftG_ne j0 j' heq
  have hg1_cnt_sh : ∀ u, (gateAt C (shiftG j0 g1)).inputs.count (shiftW n j0 u) =
      (if u = w then 0 else (gateAt C' g1).inputs.count u) := by
    intro u
    rcases hg1_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · by_cases huw : u = w
      · rw [huw, hw_sh, if_pos rfl]
        have hne1 : n + j0 ≠ w := by omega
        have hne2 : shiftW n j0 b ≠ w := fun e => hbw (shiftW_inj n j0 (e.trans hw_sh.symm))
        simp [beq_iff_eq, hne1, hne2]
      · have hne1 : n + j0 ≠ shiftW n j0 u := (shiftW_ne_j0 n j0 u).symm
        by_cases hub : u = b
        · rw [hub, if_neg hbw]; simp [beq_iff_eq, (shiftW_ne_j0 n j0 b).symm, hbw.symm]
        · have hne2 : shiftW n j0 b ≠ shiftW n j0 u := fun e => hub (shiftW_inj n j0 e).symm
          simp [beq_iff_eq, hne1, hne2, huw, hub, Ne.symm huw, Ne.symm hub]
    · by_cases huw : u = w
      · rw [huw, hw_sh, if_pos rfl]
        have hne1 : n + j0 ≠ w := by omega
        have hne2 : shiftW n j0 b ≠ w := fun e => hbw (shiftW_inj n j0 (e.trans hw_sh.symm))
        simp [beq_iff_eq, hne1, hne2]
      · have hne1 : n + j0 ≠ shiftW n j0 u := (shiftW_ne_j0 n j0 u).symm
        by_cases hub : u = b
        · rw [hub, if_neg hbw]; simp [beq_iff_eq, (shiftW_ne_j0 n j0 b).symm, hbw.symm]
        · have hne2 : shiftW n j0 b ≠ shiftW n j0 u := fun e => hub (shiftW_inj n j0 e).symm
          simp [beq_iff_eq, hne1, hne2, huw, hub, Ne.symm huw, Ne.symm hub]
  have hg1_cnt_j0 : (gateAt C (shiftG j0 g1)).inputs.count (n + j0) = 1 := by
    have hne : shiftW n j0 b ≠ n + j0 := shiftW_ne_j0 n j0 b
    rcases hg1_cases with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> simp [beq_iff_eq, hne]
  have hg1_cnt_w' : (gateAt C' g1).inputs.count w = 1 := by
    rcases hg1_cases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> simp [beq_iff_eq, hbw]
  have hreads_sh : ∀ u, readsIn C (G.image (shiftG j0)) (shiftW n j0 u) =
      if u = w then readsIn C' G w - 1 else readsIn C' G u := by
    intro u
    unfold readsIn
    rw [Finset.sum_image (fun a _ b _ h => shiftG_inj j0 h)]
    rw [← Finset.add_sum_erase G (fun j' => (gateAt C (shiftG j0 j')).inputs.count (shiftW n j0 u)) hg1]
    have hsum_er : ∑ j' ∈ G.erase g1, (gateAt C (shiftG j0 j')).inputs.count (shiftW n j0 u) =
        ∑ j' ∈ G.erase g1, (gateAt C' j').inputs.count u := by
      apply Finset.sum_congr rfl
      intro j' hj'
      rw [(hother j' (Finset.mem_of_mem_erase hj') (Finset.ne_of_mem_erase hj')).2]
      exact list_count_map_inj (shiftW n j0) (shiftW_inj n j0) _ u
    rw [hsum_er, hg1_cnt_sh u]
    by_cases huw : u = w
    · rw [huw, if_pos rfl, if_pos rfl, Nat.zero_add]
      have htot := Finset.add_sum_erase G (fun j' => (gateAt C' j').inputs.count w) hg1
      rw [hg1_cnt_w'] at htot; omega
    · rw [if_neg huw, if_neg huw,
        Finset.add_sum_erase G (fun j' => (gateAt C' j').inputs.count u) hg1]
  have hreads_j0 : readsIn C (G.image (shiftG j0)) (n + j0) = 1 := by
    unfold readsIn
    rw [Finset.sum_image (fun a _ b _ h => shiftG_inj j0 h),
      ← Finset.add_sum_erase G (fun j' => (gateAt C (shiftG j0 j')).inputs.count (n + j0)) hg1]
    have h0 : ∑ j' ∈ G.erase g1, (gateAt C (shiftG j0 j')).inputs.count (n + j0) = 0 := by
      apply Finset.sum_eq_zero; intro j' hj'
      rw [(hother j' (Finset.mem_of_mem_erase hj') (Finset.ne_of_mem_erase hj')).2]
      exact list_count_map_not_mem _ _ _ (fun a _ => shiftW_ne_j0 n j0 a)
    rw [h0, hg1_cnt_j0]
  have hreads_l : readsIn C (G.image (shiftG j0)) l.val = 0 := by
    have hl_sh : shiftW n j0 l.val = l.val := shiftW_lt_n n j0 l.val l.isLt
    rw [← hl_sh, hreads_sh l.val, if_neg hw_nel.symm]
    unfold readsIn
    apply Finset.sum_eq_zero; intro j' hj'
    apply List.count_eq_zero.mpr; intro hl_in
    rcases (htree.1 j' hj').2.2 l.val hl_in with h1 | ⟨h1, _⟩
    · exact hl_not h1
    · have := l.isLt; omega
  have hj0_cnt : ∀ u, (gateAt C j0).inputs.count u =
      (if u = l.val then 1 else 0) + (if u = w then 1 else 0) := by
    intro u
    rcases hj0_ins with h | h <;> rw [h]
    · by_cases h1 : u = l.val <;> by_cases h2 : u = w
      · exact absurd (h2.symm.trans h1) hw_nel
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel]
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel, Ne.symm h1]
      · simp [h1, h2, beq_iff_eq, Ne.symm h1, Ne.symm h2]
    · by_cases h1 : u = l.val <;> by_cases h2 : u = w
      · exact absurd (h2.symm.trans h1) hw_nel
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel]
      · simp [h1, h2, beq_iff_eq, hw_nel, Ne.symm hw_nel, Ne.symm h1]
      · simp [h1, h2, beq_iff_eq, Ne.symm h1, Ne.symm h2]
  have hreads_ins : ∀ u, readsIn C (insert j0 (G.image (shiftG j0))) u =
      (gateAt C j0).inputs.count u + readsIn C (G.image (shiftG j0)) u := fun u =>
    Finset.sum_insert hj0_not
  have hrc_w : readsIn C' G w = 1 := by
    rcases hw_mem with hwL | ⟨h1, h2⟩
    · have := (htree.2.1 w hwL).2; rw [if_neg hw_ne] at this; exact this
    · have hsub : n + (w - n) = w := by omega
      have := htree.2.2.1 (w - n) h2; rw [hsub, if_neg hw_ne] at this; exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with hj_eq | hj'
    · rw [hj_eq]
      refine ⟨hj0_op, by rcases hj0_ins with h | h <;> simp [h], ?_⟩
      intro i hi
      have hm : i = l.val ∨ i = w := by
        rcases hj0_ins with h | h <;> rw [h] at hi <;> simp at hi <;> tauto
      rcases hm with hil | hiw
      · rw [hil]; exact Or.inl (Finset.mem_insert_self _ _)
      · rw [hiw]
        rcases hw_mem with hwL | ⟨h1, h2⟩
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hwL, hw_sh⟩))
        · right
          have hweq : w = n + (w - n) := by omega
          have hwsh' : w = n + shiftG j0 (w - n) := by
            calc w = shiftW n j0 w := hw_sh.symm
              _ = shiftW n j0 (n + (w - n)) := by rw [← hweq]
              _ = n + shiftG j0 (w - n) := shiftW_add n j0 (w - n)
          exact ⟨by omega, Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨w - n, h2, by omega⟩)⟩
    · obtain ⟨j', hj'G, rfl⟩ := Finset.mem_image.mp hj'
      by_cases hjg : j' = g1
      · subst hjg
        refine ⟨hg1_op.trans (htree.1 j' hj'G).1, ?_, ?_⟩
        · rcases hg1_cases with ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp [h2]
        · intro i hi
          have hm : i = n + j0 ∨ i = shiftW n j0 b := by
            rcases hg1_cases with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] at hi <;> simp at hi <;> tauto
          rcases hm with rfl | rfl
          · exact Or.inr ⟨Nat.le_add_right _ _, by simp⟩
          · have hb_in : b ∈ (gateAt C' j').inputs := by
              rcases hg1_cases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> simp
            rcases (htree.1 j' hj'G).2.2 b hb_in with h1 | ⟨h1, h2⟩
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, h1, rfl⟩))
            · right
              have hbeq : b = n + (b - n) := by omega
              rw [hbeq, shiftW_add]
              exact ⟨Nat.le_add_right _ _,
                by simpa using Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b - n, h2, rfl⟩)⟩
      · obtain ⟨hop, hin⟩ := hother j' hj'G hjg
        obtain ⟨hop', hlen', hmem'⟩ := htree.1 j' hj'G
        refine ⟨hop.trans hop', by rw [hin, List.length_map, hlen'], ?_⟩
        intro i hi
        rw [hin] at hi
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
        rcases hmem' a ha with h1 | ⟨h1, h2⟩
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, h1, rfl⟩))
        · right
          have ha_eq : a = n + (a - n) := by omega
          rw [ha_eq, shiftW_add]
          exact ⟨Nat.le_add_right _ _,
            by simpa using Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a - n, h2, rfl⟩)⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with hu_eq | hu'
    · rw [hu_eq]
      have hne_ρ : l.val ≠ shiftW n j0 ρ := by
        intro e
        have : ρ = l.val := shiftW_inj n j0 (e.symm.trans (shiftW_lt_n n j0 l.val l.isLt).symm)
        rcases orTree_top_mem htree with h1 | ⟨h1, _⟩
        · exact hl_not (this ▸ h1)
        · have := l.isLt; omega
      refine ⟨fun ⟨h1, _⟩ => by have := l.isLt; omega, ?_⟩
      rw [hreads_ins, hj0_cnt, hreads_l, if_pos rfl, if_neg hw_nel.symm, if_neg hne_ρ]
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu'
      have hne_l : shiftW n j0 a ≠ l.val := by
        intro e
        have : a = l.val := shiftW_inj n j0 (e.trans (shiftW_lt_n n j0 l.val l.isLt).symm)
        exact hl_not (this ▸ ha)
      obtain ⟨hnot, hrc⟩ := htree.2.1 a ha
      refine ⟨?_, ?_⟩
      · rintro ⟨h1, h2⟩
        rcases Finset.mem_insert.mp h2 with heq | hmem
        · exact shiftW_ne_j0 n j0 a (by omega)
        · obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hmem
          have hsh : shiftW n j0 a = shiftW n j0 (n + j') := by rw [shiftW_add]; omega
          have ha_eq : a = n + j' := shiftW_inj n j0 hsh
          exact hnot ⟨by omega, by simpa [ha_eq] using hj'⟩
      · rw [hreads_ins, hj0_cnt, if_neg hne_l, hreads_sh a]
        by_cases haw : a = w
        · rw [haw, hw_sh, if_pos rfl, if_pos rfl, hrc_w]
          have hne_ρ' : w ≠ shiftW n j0 ρ := fun e => hw_ne (shiftW_inj n j0 (hw_sh.trans e))
          rw [if_neg hne_ρ']
        · have hne_w : shiftW n j0 a ≠ w := fun e => haw (shiftW_inj n j0 (e.trans hw_sh.symm))
          rw [if_neg hne_w, if_neg haw, hrc]
          by_cases hρ : a = ρ
          · simp [hρ]
          · have hne_ρ : shiftW n j0 a ≠ shiftW n j0 ρ := fun e => hρ (shiftW_inj n j0 e)
            simp [hρ, hne_ρ]
  · intro j hj
    rcases Finset.mem_insert.mp hj with hj_eq | hj'
    · rw [hj_eq]
      have hne_ρ : n + j0 ≠ shiftW n j0 ρ := (shiftW_ne_j0 n j0 ρ).symm
      rw [hreads_ins, hj0_cnt, hreads_j0, if_neg (by have := l.isLt; omega), if_neg (by omega),
        if_neg hne_ρ]
    · obtain ⟨j', hj'G, rfl⟩ := Finset.mem_image.mp hj'
      have hne_l : n + shiftG j0 j' ≠ l.val := by have := l.isLt; omega
      rw [hreads_ins, hj0_cnt, if_neg hne_l, ← shiftW_add, hreads_sh (n + j')]
      by_cases hjw : n + j' = w
      · rw [hjw, hw_sh, if_pos rfl, if_pos rfl, hrc_w]
        have hne_ρ' : w ≠ shiftW n j0 ρ := fun e => hw_ne (shiftW_inj n j0 (hw_sh.trans e))
        rw [if_neg hne_ρ']
      · have hne_w : shiftW n j0 (n + j') ≠ w := fun e => hjw (shiftW_inj n j0 (e.trans hw_sh.symm))
        rw [if_neg hne_w, if_neg hjw, htree.2.2.1 j' hj'G]
        by_cases hρ : n + j' = ρ
        · simp [hρ]
        · have hne_ρ : shiftW n j0 (n + j') ≠ shiftW n j0 ρ := fun e => hρ (shiftW_inj n j0 e)
          simp [hρ, hne_ρ]
  · rw [if_neg (Finset.insert_ne_empty _ _)]
    have hGne : G ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨g1, hg1⟩
    have hr := htree.2.2.2; rw [if_neg hGne] at hr
    obtain ⟨j', hj', rfl⟩ := hr
    exact ⟨shiftG j0 j', Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j', hj', rfl⟩),
      shiftW_add n j0 j'⟩

private lemma centred_shift_z {n j0 : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C C' : Circuit} {d d' : NCCData n}
    (hRB : ReadsBack n C) (hv' : Valid n K' A C' d')
    (hClen : C'.gates.length + 1 = C.gates.length) (hj0 : j0 < C.gates.length)
    (r : Fin n) (hr' : r ∈ d'.cover) (hr : r ∈ d.cover)
    (hrole_z : ∀ j' ∈ gatesOf d' C' Kind.z r.val,
      d.role (shiftG j0 j') = (Kind.z, r.val) ∧
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0))
    (hrole_b : ∀ s ∈ d'.cover, d'.tie s = some r →
      ∃ jb < C'.gates.length, d'.bw s = n + jb ∧ (d.role (shiftG j0 jb)).1 = Kind.b) :
    ∀ a, (a = r.val ∨ ∃ j' < C'.gates.length, a = n + j' ∧ d'.role j' = (Kind.z, r.val)) →
      (IsCentred n C d (shiftW n j0 a) ↔ IsCentred n C' d' a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rintro (rfl | ⟨j', hj', rfl, hrj⟩)
    · rw [shiftW_lt_n n j0 r.val r.isLt, isCentred_input, isCentred_input]
      exact ⟨fun _ => hr', fun _ => hr⟩
    · have hj'mem : j' ∈ gatesOf d' C' Kind.z r.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', hrj⟩
      obtain ⟨hroleC, hinC⟩ := hrole_z j' hj'mem
      have hsh_lt : shiftG j0 j' < C.gates.length := by unfold shiftG; split_ifs <;> omega
      rw [shiftW_add, isCentred_gate C d hRB (shiftG j0 j') hsh_lt,
        isCentred_gate C' d' hv'.1 j' hj', hroleC, hrj, hinC]
      simp only [true_and, List.mem_map]
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, hci⟩
        refine ⟨i, hi, ?_⟩
        have hilt : i < n + j' := hv'.1 j' hj' i hi
        have htree := (hv'.2.2.2.2.2.1 r hr').2.1
        rcases (htree.1 j' hj'mem).2.2 i hi with hiL | ⟨hni, hig⟩
        · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hiL
          rcases hiL with rfl | ⟨s, ⟨hs, htie⟩, rfl⟩
          · exact (ih r.val hilt (Or.inl rfl)).mp hci
          · obtain ⟨jb, hjb, hbw, hrb⟩ := hrole_b s hs htie
            rw [hbw, shiftW_add] at hci
            have hsh_b : shiftG j0 jb < C.gates.length := by unfold shiftG; split_ifs <;> omega
            have hz := ((isCentred_gate C d hRB (shiftG j0 jb) hsh_b).mp hci).1
            rw [hrb] at hz; cases hz
        · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
          exact (ih i hilt (Or.inr ⟨i - n, hig.1, by omega, hig.2⟩)).mp hci
      · rintro ⟨i, hi, hci⟩
        refine ⟨shiftW n j0 i, ⟨i, hi, rfl⟩, ?_⟩
        have hilt : i < n + j' := hv'.1 j' hj' i hi
        have htree := (hv'.2.2.2.2.2.1 r hr').2.1
        rcases (htree.1 j' hj'mem).2.2 i hi with hiL | ⟨hni, hig⟩
        · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hiL
          rcases hiL with rfl | ⟨s, ⟨hs, htie⟩, rfl⟩
          · exact (ih r.val hilt (Or.inl rfl)).mpr hci
          · obtain ⟨jb, hjb, hbw, hrb⟩ := bw_spec hv' s hs
            rw [hbw] at hci
            have hz := ((isCentred_gate C' d' hv'.1 jb hjb).mp hci).1
            rw [hrb] at hz; cases hz
        · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
          exact (ih i hilt (Or.inr ⟨i - n, hig.1, by omega, hig.2⟩)).mpr hci

private lemma zroot_mem_z {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) {t : Fin n} (ht : t ∈ d.cover) :
    d.zroot t = t.val ∨ ∃ j < C.gates.length, d.zroot t = n + j ∧ d.role j = (Kind.z, t.val) := by
  have ht_tree := (hv.2.2.2.2.2.1 t ht).2.1
  have hr := ht_tree.2.2.2
  by_cases hG : gatesOf d C Kind.z t.val = ∅
  · rw [if_pos hG] at hr
    have hmem : t.val ∈ zLeaves d t := Finset.mem_insert_self _ _
    rw [hr, Finset.mem_singleton] at hmem
    exact Or.inl hmem.symm
  · rw [if_neg hG] at hr
    obtain ⟨j, hj, hzr⟩ := hr
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hj
    exact Or.inr ⟨j, hj.1, hzr, hj.2⟩

private lemma oroot_mem_o {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) {t : Fin n} (ht : t ∈ d.cover) :
    (∃ r, d.owns t r = true ∧ d.oroot t = d.lam t r) ∨
    (∃ j < C.gates.length, d.oroot t = n + j ∧ d.role j = (Kind.o, t.val)) := by
  rcases orTree_top_mem (hv.2.2.2.2.2.1 t ht).2.2.1 with hL | ⟨h1, h2⟩
  · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    obtain ⟨r, hown, heq⟩ := hL
    exact Or.inl ⟨r, hown, heq.symm⟩
  · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at h2
    exact Or.inr ⟨d.oroot t - n, h2.1, by omega, h2.2⟩

private lemma zroot_ne_oroot {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) {t : Fin n} (ht : t ∈ d.cover) :
    d.zroot t ≠ d.oroot t := by
  intro heq
  rcases zroot_mem_z hv ht with hz | ⟨jz, _, hz, hrz⟩ <;>
    rcases oroot_mem_o hv ht with ⟨r, hown, ho⟩ | ⟨jo, _, ho, hro⟩
  · have hrt : r ≠ t := (hv.2.2.1.1 t r hown).1.ne.symm
    have hlam := (hv.2.2.2.2.2.1 t ht).2.2.2 r hown
    unfold LamOK at hlam
    split_ifs at hlam with hr
    · rcases hlam.2.1 with h1 | ⟨j, _, h1, _⟩
      · exact hrt (Fin.ext (by omega))
      · have := t.isLt; omega
    · exact hrt (Fin.ext (by omega))
  · have := t.isLt; omega
  · have hrt : r ≠ t := (hv.2.2.1.1 t r hown).1.ne.symm
    have hlam := (hv.2.2.2.2.2.1 t ht).2.2.2 r hown
    unfold LamOK at hlam
    split_ifs at hlam with hr
    · rcases hlam.2.1 with h1 | ⟨j, _, h1, h2⟩
      · have := r.isLt; omega
      · have hjj : jz = j := by omega
        subst hjj; rw [hrz] at h2
        exact hrt (Fin.ext (Prod.ext_iff.mp h2).2.symm)
    · have := r.isLt; omega
  · have hjj : jz = jo := by omega
    subst hjj; rw [hrz] at hro; cases hro

private lemma zroot_inj {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) {t1 t2 : Fin n} (h1 : t1 ∈ d.cover) (h2 : t2 ∈ d.cover)
    (heq : d.zroot t1 = d.zroot t2) : t1 = t2 := by
  rcases zroot_mem_z hv h1 with hz1 | ⟨j1, _, hz1, hr1⟩ <;>
    rcases zroot_mem_z hv h2 with hz2 | ⟨j2, _, hz2, hr2⟩
  · exact Fin.ext (by omega)
  · have := t1.isLt; omega
  · have := t2.isLt; omega
  · have hjj : j1 = j2 := by omega
    subst hjj; rw [hr1] at hr2
    exact Fin.ext (Prod.ext_iff.mp hr2).2

private def readsJ0 (n j0 : ℕ) (C : Circuit) (j' : ℕ) : Prop :=
  n + j0 ∈ (gateAt C (shiftG j0 j')).inputs

private lemma fwd_b_zroot_tie_none {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {A : Finset (Fin n)} {l p : Fin n}
    {C C' : Circuit} {j0 w : ℕ} {d' : NCCData n}
    (hK_tf : ∀ a b c : Fin n, K.Adj a b → K.Adj b c → K.Adj c a → False)
    (hA : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (hfun : circuitFun n C = graphFun K A)
    (hC'_len : C'.gates.length + 1 = C.gates.length)
    (hj0 : j0 < C.gates.length)
    (hRB : ReadsBack n C)
    (hv' : Valid n K' A C' d')
    (hgate_C' : ∀ j' < C'.gates.length,
      (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs.length = 2 ∧
      (gateAt C' j').inputs = (gateAt C (shiftG j0 j')).inputs.map (remapW n j0 w) ∧
      ∀ i ∈ (gateAt C (shiftG j0 j')).inputs, i < n + shiftG j0 j' ∧ i ≠ l.val)
    (hnot_R1_ins : ∀ j' < C'.gates.length, ¬ readsJ0 n j0 C j' →
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0))
    (hR1_mem_w : ∀ j' < C'.gates.length, readsJ0 n j0 C j' → w ∈ (gateAt C' j').inputs)
    (hR1_ins_cases : ∀ j' < C'.gates.length, readsJ0 n j0 C j' →
      ∀ a b, (gateAt C' j').inputs = [a, b] → a ≠ b →
        (a = w ∧ (gateAt C (shiftG j0 j')).inputs = [n + j0, shiftW n j0 b]) ∨
        (b = w ∧ (gateAt C (shiftG j0 j')).inputs = [shiftW n j0 a, n + j0]))
    (hwval_j0 : ∀ x : Fin n → Bool, wval C x (n + j0) = (x l || wval C x w))
    (horTree_climb_C : ∀ {G L : Finset ℕ} {ρ : ℕ},
      (∀ j' ∈ G, j' < C'.gates.length) → IsOrTree n C' G L ρ →
      ∀ (x : Fin n → Bool), x l = true →
      ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) →
        wval C x (shiftW n j0 u) = true → wval C x (shiftW n j0 ρ) = true)
    (hbw_prop_C : ∀ (x : Fin n → Bool), x l = true → ∀ t ∈ d'.cover,
      wval C x (shiftW n j0 (d'.bw t)) = true →
      wval C x (shiftW n j0 (d'.zroot t)) = true →
      wval C x (shiftW n j0 C'.output) = true)
    (hout_eq_sh : C.output = shiftW n j0 C'.output)
    (hpair_eval : ∀ v : Fin n, v ∉ A →
      graphFun K A (fun i => decide (i = l ∨ i = v)) = decide (v = p))
    (horoot_of_xr : ∀ (x : Fin n → Bool) (t r : Fin n), t ∈ d'.cover →
      d'.owns t r = true → x r = true → wval C x (shiftW n j0 (d'.oroot t)) = true)
    (hR1_no_top : ∀ j' ∈ topGates d' C', ¬ readsJ0 n j0 C j')
    (hR1_no_z : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.z t.val, ¬ readsJ0 n j0 C j')
    (hR1_o_eq_p : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.o t.val, readsJ0 n j0 C j' → t = p)
    (hR1_b_oroot_eq_p : ∀ t ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw t = n + jb → readsJ0 n j0 C jb → w = d'.oroot t → t = p)
    {t : Fin n} (ht : t ∈ d'.cover) {jb : ℕ} (hjb : jb < C'.gates.length)
    (hbw : d'.bw t = n + jb) (hR : readsJ0 n j0 C jb) (hwz : w = d'.zroot t)
    (hbt_of_oroot : ∀ x : Fin n → Bool, x l = true →
      wval C x (shiftW n j0 (d'.oroot t)) = true → wval C x (shiftW n j0 (d'.bw t)) = true) :
    d'.tie t = none := by
  classical
  have hlp_adj : K.Adj l p := (hlp p).mpr rfl
  have hl_notA : l ∉ A := fun h => hA l h p hlp_adj
  have hp_notA : p ∉ A := fun h => hA p h l hlp_adj.symm
  have hshG_lt : ∀ j' < C'.gates.length, shiftG j0 j' < C.gates.length := by
    intro j' hj'; unfold shiftG; split_ifs <;> omega
  have hg_lt : ∀ k s, ∀ j' ∈ gatesOf d' C' k s, j' < C'.gates.length :=
    fun _ _ j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have howned_notA : ∀ s r : Fin n, d'.owns s r = true → r ∉ A := by
    intro s r hown hrA
    exact hA r hrA s ((hK' s r).mp (hv'.2.2.1.1 s r hown).1).1.symm
  have hzne : d'.zroot t ≠ d'.oroot t := zroot_ne_oroot hv' ht
  cases htie : d'.tie t with
  | none => rfl
  | some u =>
    exfalso
    have hown_ut : d'.owns u t = true := (hv'.2.2.2.1 t u htie).2
    have hu : u ∈ d'.cover := (hv'.2.2.1.1 u t hown_ut).2
    obtain ⟨r, hr_not, hr_own⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 ht
    obtain ⟨q, hq_not, hq_own⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 hu
    have hnot_adj_rq : ¬ K'.Adj r q := by
      intro hadj
      rcases hv'.2.1.1 hadj with h1 | h1
      · exact hr_not h1
      · exact hq_not h1
    let x3 : Fin n → Bool := fun i => decide (i = l ∨ i = r ∨ i = q)
    have hxl3 : x3 l = true := by simp [x3]
    have hxr3 : x3 r = true := by simp [x3]
    have hxq3 : x3 q = true := by simp [x3]
    have hbt3 : wval C x3 (shiftW n j0 (d'.bw t)) = true :=
      hbt_of_oroot x3 hxl3 (horoot_of_xr x3 t r ht hr_own hxr3)
    have hbt_in : d'.bw t ∈ zLeaves d' u := by
      simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
      exact Or.inr ⟨t, ⟨ht, htie⟩, rfl⟩
    have hzu3 : wval C x3 (shiftW n j0 (d'.zroot u)) = true :=
      horTree_climb_C (hg_lt _ _) (hv'.2.2.2.2.2.1 u hu).2.1 x3 hxl3 (d'.bw t) (Or.inl hbt_in) hbt3
    have hou3 : wval C x3 (shiftW n j0 (d'.oroot u)) = true :=
      horoot_of_xr x3 u q hu hq_own hxq3
    obtain ⟨jbu, hjbu, hbwu, _, hopu, hinu⟩ := (hv'.2.2.2.2.2.1 u hu).1
    obtain ⟨hopCu, _, hmapCu, _⟩ := hgate_C' jbu hjbu
    have hbu3 : wval C x3 (shiftW n j0 (d'.bw u)) = true := by
      rw [hbwu, shiftW_add, wval_gate C hRB x3 (shiftG j0 jbu) (hshG_lt jbu hjbu), hopCu, hopu]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro i hi
      have hrem : remapW n j0 w i ∈ (gateAt C' jbu).inputs := by
        rw [hmapCu]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
      have hmem : remapW n j0 w i = d'.zroot u ∨ remapW n j0 w i = d'.oroot u := by
        rcases hinu with h | h <;> rw [h] at hrem <;> simp at hrem <;> tauto
      rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with hi_eq | ⟨_, hi_eq⟩
      · rw [hi_eq]; rcases hmem with h1 | h1 <;> rw [h1]; exact hzu3; exact hou3
      · rw [hi_eq, hwval_j0, hxl3]; rfl
    have hout3 := hbw_prop_C x3 hxl3 u hu hbu3 hzu3
    rw [← hout_eq_sh] at hout3
    have hF3 : graphFun K A x3 = true := by rw [← congrFun hfun x3]; exact hout3
    have hp_not : p ∉ d'.cover := by
      unfold graphFun at hF3
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hF3
      rcases hF3 with ⟨a, ha, hxa⟩ | ⟨a, b, hab, hxa, hxb⟩
      · simp only [x3, decide_eq_true_eq] at hxa
        rcases hxa with ha1 | ha2 | ha3
        · exact absurd (ha1 ▸ ha) hl_notA
        · exact absurd (ha2 ▸ ha) (howned_notA t r hr_own)
        · exact absurd (ha3 ▸ ha) (howned_notA u q hq_own)
      · simp only [x3, decide_eq_true_eq] at hxa hxb
        have hK_adj_rq : ¬ K.Adj r q := by
          intro h1
          have hrl : r ≠ l := by
            intro e; exact ((hK' t l).mp (hv'.2.2.1.1 t l (e ▸ hr_own)).1).2.2 rfl
          have hql : q ≠ l := by
            intro e; exact ((hK' u l).mp (hv'.2.2.1.1 u l (e ▸ hq_own)).1).2.2 rfl
          exact hnot_adj_rq ((hK' r q).mpr ⟨h1, hrl, hql⟩)
        rcases hxa with ha1 | ha2 | ha3 <;> rcases hxb with hb1 | hb2 | hb3
        · rw [ha1, hb1] at hab; exact absurd rfl hab.ne
        · rw [ha1, hb2] at hab; exact ((hlp r).mp hab) ▸ hr_not
        · rw [ha1, hb3] at hab; exact ((hlp q).mp hab) ▸ hq_not
        · rw [ha2, hb1] at hab; exact ((hlp r).mp hab.symm) ▸ hr_not
        · rw [ha2, hb2] at hab; exact absurd rfl hab.ne
        · rw [ha2, hb3] at hab; exact absurd hab hK_adj_rq
        · rw [ha3, hb1] at hab; exact ((hlp q).mp hab.symm) ▸ hq_not
        · rw [ha3, hb2] at hab; exact absurd hab.symm hK_adj_rq
        · rw [ha3, hb3] at hab; exact absurd rfl hab.ne
    have hR1_only : ∀ j1 < C'.gates.length, readsJ0 n j0 C j1 → j1 = jb := by
      intro j1 hj1 hR1
      rcases hv'.2.2.2.2.1 j1 hj1 with htop | ⟨s, hs, heq, hbf⟩
      · exact absurd hR1 (hR1_no_top j1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, htop⟩))
      · cases hkind : (d'.role j1).1 with
        | top =>
          exact absurd hR1 (hR1_no_top j1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hkind⟩))
        | z =>
          exact absurd hR1 (hR1_no_z s hs j1
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, Prod.ext hkind heq⟩))
        | o =>
          have hsp := hR1_o_eq_p s hs j1
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, Prod.ext hkind heq⟩) hR1
          exact absurd (hsp ▸ hs) hp_not
        | b =>
          have hbw_s : d'.bw s = n + j1 := hbf hkind
          obtain ⟨jb_s, _, hbw_s', _, _, hin_s⟩ := (hv'.2.2.2.2.2.1 s hs).1
          have hjs : j1 = jb_s := by omega
          have hwm := hR1_mem_w j1 hj1 hR1
          rw [hjs] at hwm
          have hmem_s : w = d'.zroot s ∨ w = d'.oroot s := by
            rcases hin_s with h | h <;> rw [h] at hwm <;> simp at hwm <;> tauto
          rcases hmem_s with hzs | hos
          · have hst : s = t := zroot_inj hv' hs ht (hzs.symm.trans hwz)
            subst hst; omega
          · have hsp := hR1_b_oroot_eq_p s hs j1 hj1 hbw_s hR1 hos
            exact absurd (hsp ▸ hs) hp_not
    let xp : Fin n → Bool := fun i => decide (i = l ∨ i = p)
    have hnot_both : ¬ (d'.owns t p = true ∧ d'.owns u p = true) := by
      rintro ⟨h1, h2⟩
      exact hK_tf u t p
        ((hK' u t).mp (hv'.2.2.1.1 u t hown_ut).1).1
        ((hK' t p).mp (hv'.2.2.1.1 t p h1).1).1
        ((hK' u p).mp (hv'.2.2.1.1 u p h2).1).1.symm
    have hl_not_cov : l ∉ d'.cover := by
      intro hlcov
      obtain ⟨r1, _, h1⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 hlcov
      exact ((hK' l r1).mp (hv'.2.2.1.1 l r1 h1).1).2.1 rfl
    have hzero_inv : ∀ a < n + C'.gates.length,
        (a < n → wval C xp (shiftW n j0 a) = true → a = l.val ∨ a = p.val) ∧
        (∀ j1, a = n + j1 → (d'.role j1).1 = Kind.top →
          wval C xp (shiftW n j0 a) = false) ∧
        (∀ j1 (s : Fin n), a = n + j1 → s ∈ d'.cover → d'.role j1 = (Kind.b, s.val) →
          (s ≠ t ∨ d'.owns t p = false) → wval C xp (shiftW n j0 a) = false) ∧
        (∀ j1 (s : Fin n), a = n + j1 → s ∈ d'.cover → d'.role j1 = (Kind.z, s.val) →
          (s ≠ u ∨ d'.owns t p = false) → wval C xp (shiftW n j0 a) = false) ∧
        (∀ j1 (s : Fin n), a = n + j1 → s ∈ d'.cover → d'.role j1 = (Kind.o, s.val) →
          (d'.owns s p = false ∧ (s = u ∨ d'.owns t p = false)) →
          wval C xp (shiftW n j0 a) = false) := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        intro halt
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro han hwa
          rw [shiftW_lt_n n j0 a han, wval_input C xp a han] at hwa
          simp only [xp, decide_eq_true_eq] at hwa
          rcases hwa with h | h
          · exact Or.inl (congrArg Fin.val h)
          · exact Or.inr (congrArg Fin.val h)
        · intro j1 rfl htop
          have hj1 : j1 < C'.gates.length := by omega
          have hnoR : ¬ readsJ0 n j0 C j1 := fun h => by
            have heq := hR1_only j1 hj1 h; subst heq
            obtain ⟨jb2, _, hbw2, hrb2, _⟩ := (hv'.2.2.2.2.2.1 t ht).1
            have : j1 = jb2 := by omega
            subst this; rw [hrb2] at htop; cases htop
          have hmem : j1 ∈ topGates d' C' := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, htop⟩
          obtain ⟨hopC, _, _, _⟩ := hgate_C' j1 hj1
          rw [shiftW_add, wval_gate C hRB xp (shiftG j0 j1) (hshG_lt j1 hj1), hopC,
            (hv'.2.2.2.2.2.2.1 j1 hmem).1, hnot_R1_ins j1 hj1 hnoR]
          simp only [GateOp.eval, List.map_map, List.any_map, List.any_eq_false, Function.comp_apply,
            id_eq, Bool.not_eq_true]
          intro i hi
          have hilt : i < n + j1 := hv'.1 j1 hj1 i hi
          rcases (hv'.2.2.2.2.2.2.1 j1 hmem).2.2 i hi with hiL | ⟨hni, hig⟩
          · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hiL
            rcases hiL with ⟨a0, ha0, rfl⟩ | ⟨s, ⟨hs, hstie⟩, rfl⟩
            · rw [shiftW_lt_n n j0 a0.val a0.isLt, wval_input C xp a0.val a0.isLt]
              simp only [xp, decide_eq_false_iff_not]
              rintro (h1 | h2); exact hl_notA (h1 ▸ ha0); exact hp_notA (h2 ▸ ha0)
            · obtain ⟨js, hjs, hbws, hrbs⟩ := bw_spec hv' s hs
              have hst : s ≠ t := by intro e; rw [e, htie] at hstie; cases hstie
              exact (ih (d'.bw s) hilt (by omega)).2.2.1 js s hbws hs hrbs (Or.inl hst)
          · simp only [topGates, Finset.mem_filter, Finset.mem_range] at hig
            exact (ih i hilt (by omega)).2.1 (i - n) (by omega) hig.2
        · intro j1 s rfl hs hrole hcond
          have hj1 : j1 < C'.gates.length := by omega
          obtain ⟨jbs, hjbs, hbws, _, hops, hins⟩ := (hv'.2.2.2.2.2.1 s hs).1
          have hjeq : j1 = jbs := by
            rcases hv'.2.2.2.2.1 j1 hj1 with htop | ⟨s', _, heq, hbf⟩
            · rw [hrole] at htop; cases htop
            · rw [hrole] at heq hbf; have : s' = s := Fin.ext heq.symm; subst this
              have := hbf rfl; omega
          subst hjeq
          by_cases hst : s = t
          · subst s
            have hno_tp : d'.owns t p = false := by
              rcases hcond with h | h; exact absurd rfl h; exact h
            have hor_lt : d'.oroot t < n + j1 :=
              hv'.1 j1 hj1 (d'.oroot t) (by rcases hins with h | h <;> rw [h] <;> simp)
            have hor_false : wval C xp (shiftW n j0 (d'.oroot t)) = false := by
              rcases oroot_mem_o hv' ht with ⟨r1, hown1, ho1⟩ | ⟨jo, hjo, ho1, hro1⟩
              · have hlam := (hv'.2.2.2.2.2.1 t ht).2.2.2 r1 hown1
                have hr1_nep : r1 ≠ p := by intro e; rw [e] at hown1; rw [hown1] at hno_tp; cases hno_tp
                have hr1_nel : r1 ≠ l := by
                  intro e; exact ((hK' t l).mp (hv'.2.2.1.1 t l (e ▸ hown1)).1).2.2 rfl
                have hr1_neu : r1 ≠ u := by
                  intro e; rw [e] at hown1
                  exact hv'.2.2.1.2 u t (hv'.2.2.1.1 u t hown_ut).1 (by rw [hown_ut, hown1])
                unfold LamOK at hlam
                split_ifs at hlam with hr1
                · rcases hlam.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
                  · rw [ho1, h1, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
                    simp [xp, hr1_nel, hr1_nep]
                  · exact (ih (d'.oroot t) hor_lt (by omega)).2.2.2.1 jz r1 (ho1.trans h1) hr1 h2
                      (Or.inl hr1_neu)
                · rw [ho1, hlam, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
                  simp [xp, hr1_nel, hr1_nep]
              · exact (ih (d'.oroot t) hor_lt (by omega)).2.2.2.2 jo t ho1 ht hro1 ⟨hno_tp, Or.inr hno_tp⟩
            obtain ⟨hopC, _, _, _⟩ := hgate_C' j1 hj1
            have hj1_jb : j1 = jb := by omega
            subst hj1_jb
            rw [shiftW_add, wval_gate C hRB xp (shiftG j0 j1) (hshG_lt j1 hj1), hopC, hops]
            rcases hins with h | h
            · rcases hR1_ins_cases j1 hj1 hR (d'.zroot t) (d'.oroot t) h hzne with ⟨_, h2⟩ | ⟨h1, _⟩
              · rw [h2]; simp [GateOp.eval, hor_false]
              · exact absurd (h1.trans hwz).symm hzne
            · rcases hR1_ins_cases j1 hj1 hR (d'.oroot t) (d'.zroot t) h hzne.symm with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact absurd (h1.trans hwz).symm hzne
              · rw [h2]; simp [GateOp.eval, hor_false]
          · have hnoR : ¬ readsJ0 n j0 C j1 := fun h => by
              have heq := hR1_only j1 hj1 h; subst heq
              exact hst (bw_injOn hv' d'.cover (Finset.Subset.refl _) hs ht (hbws.trans hbw.symm))
            obtain ⟨hopC, _, _, _⟩ := hgate_C' j1 hj1
            rw [shiftW_add, wval_gate C hRB xp (shiftG j0 j1) (hshG_lt j1 hj1), hopC, hops,
              hnot_R1_ins j1 hj1 hnoR]
            by_cases hsu : s = u
            · subst s
              cases htp : d'.owns t p with
              | false =>
                have hzl : d'.zroot u < n + j1 :=
                  hv'.1 j1 hj1 (d'.zroot u) (by rcases hins with h | h <;> rw [h] <;> simp)
                have hz_false : wval C xp (shiftW n j0 (d'.zroot u)) = false := by
                  rcases zroot_mem_z hv' hu with hz | ⟨jz, hjz, hz, hrz⟩
                  · rw [hz, shiftW_lt_n n j0 u.val u.isLt, wval_input C xp u.val u.isLt]
                    have hunl : u ≠ l := fun e => hl_not_cov (e ▸ hu)
                    have hunp : u ≠ p := fun e => hp_not (e ▸ hu)
                    simp [xp, hunl, hunp]
                  · exact (ih (d'.zroot u) hzl (by omega)).2.2.2.1 jz u hz hu hrz (Or.inr htp)
                rcases hins with h | h <;> rw [h] <;> simp [GateOp.eval, hz_false]
              | true =>
                have hno_up : d'.owns u p = false := by
                  cases h : d'.owns u p with
                  | false => rfl
                  | true => exact absurd ⟨htp, h⟩ hnot_both
                have hol : d'.oroot u < n + j1 :=
                  hv'.1 j1 hj1 (d'.oroot u) (by rcases hins with h | h <;> rw [h] <;> simp)
                have ho_false : wval C xp (shiftW n j0 (d'.oroot u)) = false := by
                  rcases oroot_mem_o hv' hu with ⟨r1, hown1, ho1⟩ | ⟨jo, hjo, ho1, hro1⟩
                  · have hlam := (hv'.2.2.2.2.2.1 u hu).2.2.2 r1 hown1
                    have hr1_nep : r1 ≠ p := by intro e; rw [e] at hown1; rw [hown1] at hno_up; cases hno_up
                    have hr1_nel : r1 ≠ l := by
                      intro e; exact ((hK' u l).mp (hv'.2.2.1.1 u l (e ▸ hown1)).1).2.2 rfl
                    have hr1_neu : r1 ≠ u := (hv'.2.2.1.1 u r1 hown1).1.ne.symm
                    unfold LamOK at hlam
                    split_ifs at hlam with hr1
                    · rcases hlam.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
                      · rw [ho1, h1, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
                        simp [xp, hr1_nel, hr1_nep]
                      · exact (ih (d'.oroot u) hol (by omega)).2.2.2.1 jz r1 (ho1.trans h1) hr1 h2
                          (Or.inl hr1_neu)
                    · rw [ho1, hlam, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
                      simp [xp, hr1_nel, hr1_nep]
                  · exact (ih (d'.oroot u) hol (by omega)).2.2.2.2 jo u ho1 hu hro1
                      ⟨hno_up, Or.inl rfl⟩
                rcases hins with h | h <;> rw [h] <;> simp [GateOp.eval, ho_false]
            · have hzl : d'.zroot s < n + j1 :=
                hv'.1 j1 hj1 (d'.zroot s) (by rcases hins with h | h <;> rw [h] <;> simp)
              have hz_false : wval C xp (shiftW n j0 (d'.zroot s)) = false := by
                rcases zroot_mem_z hv' hs with hz | ⟨jz, hjz, hz, hrz⟩
                · rw [hz, shiftW_lt_n n j0 s.val s.isLt, wval_input C xp s.val s.isLt]
                  have hsnl : s ≠ l := fun e => hl_not_cov (e ▸ hs)
                  have hsnp : s ≠ p := fun e => hp_not (e ▸ hs)
                  simp [xp, hsnl, hsnp]
                · exact (ih (d'.zroot s) hzl (by omega)).2.2.2.1 jz s hz hs hrz (Or.inl hsu)
              rcases hins with h | h <;> rw [h] <;> simp [GateOp.eval, hz_false]
        · intro j1 s rfl hs hrole hcond
          have hj1 : j1 < C'.gates.length := by omega
          have hmem : j1 ∈ gatesOf d' C' Kind.z s.val :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hrole⟩
          have hnoR : ¬ readsJ0 n j0 C j1 := hR1_no_z s hs j1 hmem
          obtain ⟨hopC, _, _, _⟩ := hgate_C' j1 hj1
          have htree := (hv'.2.2.2.2.2.1 s hs).2.1
          rw [shiftW_add, wval_gate C hRB xp (shiftG j0 j1) (hshG_lt j1 hj1), hopC,
            (htree.1 j1 hmem).1, hnot_R1_ins j1 hj1 hnoR]
          simp only [GateOp.eval, List.map_map, List.any_map, List.any_eq_false, Function.comp_apply,
            id_eq, Bool.not_eq_true]
          intro i hi
          have hilt : i < n + j1 := hv'.1 j1 hj1 i hi
          rcases (htree.1 j1 hmem).2.2 i hi with hiL | ⟨hni, hig⟩
          · simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hiL
            rcases hiL with rfl | ⟨s', ⟨hs', hstie⟩, rfl⟩
            · rw [shiftW_lt_n n j0 s.val s.isLt, wval_input C xp s.val s.isLt]
              have hsnl : s ≠ l := fun e => hl_not_cov (e ▸ hs)
              have hsnp : s ≠ p := fun e => hp_not (e ▸ hs)
              simp [xp, hsnl, hsnp]
            · obtain ⟨js', hjs', hbws', hrbs'⟩ := bw_spec hv' s' hs'
              have hcond' : s' ≠ t ∨ d'.owns t p = false := by
                rcases hcond with hsu | htp
                · left; intro e; rw [e, htie] at hstie; exact hsu (Option.some_injective _ hstie).symm
                · exact Or.inr htp
              exact (ih (d'.bw s') hilt (by omega)).2.2.1 js' s' hbws' hs' hrbs' hcond'
          · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
            exact (ih i hilt (by omega)).2.2.2.1 (i - n) s (by omega) hs hig.2 hcond
        · intro j1 s rfl hs hrole ⟨hno_sp, hcond⟩
          have hj1 : j1 < C'.gates.length := by omega
          have hmem : j1 ∈ gatesOf d' C' Kind.o s.val :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hrole⟩
          have hnoR : ¬ readsJ0 n j0 C j1 := fun h => hp_not ((hR1_o_eq_p s hs j1 hmem h) ▸ hs)
          obtain ⟨hopC, _, _, _⟩ := hgate_C' j1 hj1
          have htree := (hv'.2.2.2.2.2.1 s hs).2.2.1
          rw [shiftW_add, wval_gate C hRB xp (shiftG j0 j1) (hshG_lt j1 hj1), hopC,
            (htree.1 j1 hmem).1, hnot_R1_ins j1 hj1 hnoR]
          simp only [GateOp.eval, List.map_map, List.any_map, List.any_eq_false, Function.comp_apply,
            id_eq, Bool.not_eq_true]
          intro i hi
          have hilt : i < n + j1 := hv'.1 j1 hj1 i hi
          rcases (htree.1 j1 hmem).2.2 i hi with hiL | ⟨hni, hig⟩
          · simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hiL
            obtain ⟨r1, hown1, rfl⟩ := hiL
            have hlam := (hv'.2.2.2.2.2.1 s hs).2.2.2 r1 hown1
            have hr1_nep : r1 ≠ p := by intro e; rw [e] at hown1; rw [hown1] at hno_sp; cases hno_sp
            have hr1_nel : r1 ≠ l := by
              intro e; exact ((hK' s l).mp (hv'.2.2.1.1 s l (e ▸ hown1)).1).2.2 rfl
            unfold LamOK at hlam
            split_ifs at hlam with hr1
            · rcases hlam.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
              · rw [h1, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
                simp [xp, hr1_nel, hr1_nep]
              · have hcond' : r1 ≠ u ∨ d'.owns t p = false := by
                  rcases hcond with hsu | htp
                  · rw [hsu] at hown1
                    exact Or.inl (hv'.2.2.1.1 u r1 hown1).1.ne.symm
                  · exact Or.inr htp
                exact (ih (d'.lam s r1) hilt (by omega)).2.2.2.1 jz r1 h1 hr1 h2 hcond'
            · rw [hlam, shiftW_lt_n n j0 r1.val r1.isLt, wval_input C xp r1.val r1.isLt]
              simp [xp, hr1_nel, hr1_nep]
          · simp only [gatesOf, Finset.mem_filter, Finset.mem_range] at hig
            exact (ih i hilt (by omega)).2.2.2.2 (i - n) s (by omega) hs hig.2 ⟨hno_sp, hcond⟩
    have hout_false : wval C xp C.output = false := by
      rw [hout_eq_sh]
      rcases orTree_top_mem hv'.2.2.2.2.2.2 with hL | ⟨h1, h2⟩
      · simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hL
        rcases hL with ⟨a0, ha0, heq⟩ | ⟨s, ⟨hs, hstie⟩, heq⟩
        · rw [← heq, shiftW_lt_n n j0 a0.val a0.isLt, wval_input C xp a0.val a0.isLt]
          simp only [xp, decide_eq_false_iff_not]
          rintro (h1 | h2); exact hl_notA (h1 ▸ ha0); exact hp_notA (h2 ▸ ha0)
        · obtain ⟨js, hjs, hbws, hrbs⟩ := bw_spec hv' s hs
          have hst : s ≠ t := by intro e; rw [e, htie] at hstie; cases hstie
          exact (hzero_inv C'.output (by omega)).2.2.1 js s (heq ▸ hbws) hs hrbs (Or.inl hst)
      · simp only [topGates, Finset.mem_filter, Finset.mem_range] at h2
        exact (hzero_inv C'.output (by omega)).2.1 (C'.output - n) (by omega) h2.2
    have hout_true : wval C xp C.output = true := by
      change circuitFun n C xp = true
      rw [hfun, hpair_eval p hp_notA]; simp
    rw [hout_false] at hout_true; cases hout_true

private lemma fwd_branch_flip {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {A : Finset (Fin n)} {l p : Fin n}
    {C C' : Circuit} {j0 w : ℕ} {d' : NCCData n} {T0 : Finset (Fin n)}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (hT0 : IsMinCover K T0)
    (hC'_len : C'.gates.length + 1 = C.gates.length)
    (hj0 : j0 < C.gates.length)
    (hw_nel : w ≠ l.val)
    (hj0_op : (gateAt C j0).op = GateOp.or)
    (hj0_ins : (gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val])
    (hRB : ReadsBack n C)
    (hv' : Valid n K' A C' d')
    (hgate_C' : ∀ j' < C'.gates.length,
      (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs.length = 2 ∧
      (gateAt C' j').inputs = (gateAt C (shiftG j0 j')).inputs.map (remapW n j0 w) ∧
      ∀ i ∈ (gateAt C (shiftG j0 j')).inputs, i < n + shiftG j0 j' ∧ i ≠ l.val)
    (hnot_R1_ins : ∀ j' < C'.gates.length, ¬ readsJ0 n j0 C j' →
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0))
    (hR1_mem_w : ∀ j' < C'.gates.length, readsJ0 n j0 C j' → w ∈ (gateAt C' j').inputs)
    (hR1_ins_cases : ∀ j' < C'.gates.length, readsJ0 n j0 C j' →
      ∀ a b, (gateAt C' j').inputs = [a, b] → a ≠ b →
        (a = w ∧ (gateAt C (shiftG j0 j')).inputs = [n + j0, shiftW n j0 b]) ∨
        (b = w ∧ (gateAt C (shiftG j0 j')).inputs = [shiftW n j0 a, n + j0]))
    (hout_eq_sh : C.output = shiftW n j0 C'.output)
    (hR1_no_top : ∀ j' ∈ topGates d' C', ¬ readsJ0 n j0 C j')
    (hR1_no_z : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.z t.val, ¬ readsJ0 n j0 C j')
    (hR1_o_eq_p : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.o t.val, readsJ0 n j0 C j' → t = p)
    (hR1_b_oroot_eq_p : ∀ t ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw t = n + jb → readsJ0 n j0 C jb → w = d'.oroot t → t = p)
    {v : Fin n} (hv_cov : v ∈ d'.cover) {jbv : ℕ} (hjbv : jbv < C'.gates.length)
    (hbwv : d'.bw v = n + jbv) (hRv : readsJ0 n j0 C jbv) (hwv : w = d'.zroot v)
    (htie_v : d'.tie v = none) (hp_not : p ∉ d'.cover)
    (hown_v : ∀ r, d'.owns v r = true ↔ r = p) :
    IsNestedCoverCircuit n K A C := by
  classical
  have hlp_adj : K.Adj l p := (hlp p).mpr rfl
  have hl_nep : l ≠ p := hlp_adj.ne
  have hshG_lt : ∀ j' < C'.gates.length, shiftG j0 j' < C.gates.length := by
    intro j' hj'; unfold shiftG; split_ifs <;> omega
  have htop_lt : ∀ j' ∈ topGates d' C', j' < C'.gates.length :=
    fun j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hg_lt : ∀ k t, ∀ j' ∈ gatesOf d' C' k t, j' < C'.gates.length :=
    fun _ _ j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hrole_jbv : d'.role jbv = (Kind.b, v.val) := by
    obtain ⟨j1, _, h1, h2, _⟩ := (hv'.2.2.2.2.2.1 v hv_cov).1
    have : jbv = j1 := by omega
    exact this ▸ h2
  have hR1_only : ∀ j1 < C'.gates.length, readsJ0 n j0 C j1 → j1 = jbv := by
    intro j1 hj1 hR1
    rcases hv'.2.2.2.2.1 j1 hj1 with htop | ⟨s, hs, heq, hbf⟩
    · exact absurd hR1 (hR1_no_top j1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, htop⟩))
    · cases hkind : (d'.role j1).1 with
      | top =>
        exact absurd hR1 (hR1_no_top j1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hkind⟩))
      | z =>
        exact absurd hR1 (hR1_no_z s hs j1
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, Prod.ext hkind heq⟩))
      | o =>
        exact absurd ((hR1_o_eq_p s hs j1
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, Prod.ext hkind heq⟩) hR1) ▸ hs) hp_not
      | b =>
        have hbw_s := hbf hkind
        obtain ⟨jbs, _, hbw_s', _, _, hin_s⟩ := (hv'.2.2.2.2.2.1 s hs).1
        have hjs : j1 = jbs := by omega
        have hwm := hR1_mem_w j1 hj1 hR1
        rw [hjs] at hwm
        have hmem_s : w = d'.zroot s ∨ w = d'.oroot s := by
          rcases hin_s with h | h <;> rw [h] at hwm <;> simp at hwm <;> tauto
        rcases hmem_s with hzs | hos
        · have hsv : s = v := zroot_inj hv' hs hv_cov (hzs.symm.trans hwv)
          subst hsv; omega
        · exact absurd ((hR1_b_oroot_eq_p s hs j1 hj1 hbw_s hR1 hos) ▸ hs) hp_not
  have hno_tie_to_v : ∀ s ∈ d'.cover, d'.tie s ≠ some v := by
    intro s hs htie
    have hown := (hv'.2.2.2.1 s v htie).2
    exact hp_not (((hown_v s).mp hown) ▸ hs)
  have hZv_empty : gatesOf d' C' Kind.z v.val = ∅ := by
    have hc := tree_card n C' _ _ _ (hv'.2.2.2.2.2.1 v hv_cov).2.1
    rw [zLeaves_card hv' v] at hc
    have h0 : (d'.cover.filter (fun s => d'.tie s = some v)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hno_tie_to_v)
    exact Finset.card_eq_zero.mp (by omega)
  have hzv_eq : d'.zroot v = v.val := by
    have hr := (hv'.2.2.2.2.2.1 v hv_cov).2.1.2.2.2
    rw [if_pos hZv_empty] at hr
    have hmem : v.val ∈ zLeaves d' v := Finset.mem_insert_self _ _
    rw [hr, Finset.mem_singleton] at hmem; exact hmem.symm
  have hw_eq_v : w = v.val := hwv.trans hzv_eq
  have hOv_empty : gatesOf d' C' Kind.o v.val = ∅ := by
    have hc := tree_card n C' _ _ _ (hv'.2.2.2.2.2.1 v hv_cov).2.2.1
    rw [oLeaves_card hv' v hv_cov] at hc
    have hfilt : Finset.univ.filter (fun r => d'.owns v r = true) = {p} := by
      ext r; simp [hown_v]
    rw [hfilt, Finset.card_singleton] at hc
    exact Finset.card_eq_zero.mp (by omega)
  have hov_eq : d'.oroot v = p.val := by
    have hr := (hv'.2.2.2.2.2.1 v hv_cov).2.2.1.2.2.2
    rw [if_pos hOv_empty] at hr
    have hmem : d'.lam v p ∈ oLeaves d' v := by
      simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, (hown_v p).mpr rfl, rfl⟩
    rw [hr, Finset.mem_singleton] at hmem
    have hlam := (hv'.2.2.2.2.2.1 v hv_cov).2.2.2 p ((hown_v p).mpr rfl)
    unfold LamOK at hlam; rw [if_neg hp_not] at hlam
    exact hmem.symm.trans hlam
  have hvp_ne : v ≠ p := fun e => hp_not (e ▸ hv_cov)
  have hvl_ne : v ≠ l := fun e => hw_nel (hw_eq_v.trans (congrArg Fin.val e))
  have hvp_adj : K.Adj v p := ((hK' v p).mp (hv'.2.2.1.1 v p ((hown_v p).mpr rfl)).1).1
  let d : NCCData n := {
    cover := insert p (d'.cover.erase v)
    owns := fun a b => if a = p then decide (b = l ∨ b = v) else if a = v then false else d'.owns a b
    tie := fun s => if s = p then none else d'.tie s
    role := fun j =>
      if j = j0 then (Kind.o, p.val)
      else if j = shiftG j0 jbv then (Kind.b, p.val)
      else d'.role (unshiftG j0 j)
    bw := fun t => if t = p then shiftW n j0 (d'.bw v) else shiftW n j0 (d'.bw t)
    zroot := fun t => if t = p then p.val else shiftW n j0 (d'.zroot t)
    oroot := fun t => if t = p then n + j0 else shiftW n j0 (d'.oroot t)
    lam := fun t r => if t = p then r.val else shiftW n j0 (d'.lam t r)
  }
  refine ⟨d, hRB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsMinCover K d.cover
    have hcov : K.IsVertexCover (d.cover : Set (Fin n)) := by
      intro a b hab
      by_cases hal : a = l
      · subst hal; rw [(hlp b).mp hab]; exact Or.inr (Finset.mem_insert_self _ _)
      · by_cases hbl : b = l
        · subst hbl; rw [(hlp a).mp hab.symm]; exact Or.inl (Finset.mem_insert_self _ _)
        · have hab' : K'.Adj a b := (hK' a b).mpr ⟨hab, hal, hbl⟩
          have hne := hv'.2.2.1.2 a b hab'
          cases h1 : d'.owns a b with
          | true =>
            have ha := (hv'.2.2.1.1 a b h1).2
            by_cases hav : a = v
            · subst hav; rw [(hown_v b).mp h1]; exact Or.inr (Finset.mem_insert_self _ _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hav, ha⟩))
          | false =>
            have h2 : d'.owns b a = true := by
              rw [h1] at hne; cases h : d'.owns b a with
              | true => rfl
              | false => exact absurd h.symm hne
            have hb := (hv'.2.2.1.1 b a h2).2
            by_cases hbv : b = v
            · subst hbv; rw [(hown_v a).mp h2]; exact Or.inl (Finset.mem_insert_self _ _)
            · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbv, hb⟩))
    have hcard : d.cover.card = d'.cover.card := by
      have hp_not' : p ∉ d'.cover.erase v := fun h => hp_not (Finset.mem_of_mem_erase h)
      change (insert p (d'.cover.erase v)).card = d'.cover.card
      rw [Finset.card_insert_of_notMem hp_not', Finset.card_erase_add_one hv_cov]
    refine ⟨hcov, fun S hS => ?_⟩
    have hT0eq := minCover_card_eq hlp hfree hK' hT0 hv'.2.1
    have hle := hT0.2 S hS
    omega
  · -- OwnerOK K d
    refine ⟨?_, ?_⟩
    · intro a b hab
      dsimp only [d] at hab ⊢
      by_cases hap : a = p
      · subst a
        rw [if_pos rfl] at hab
        have hab' : b = l ∨ b = v := of_decide_eq_true hab
        rcases hab' with rfl | rfl
        · exact ⟨hlp_adj.symm, Finset.mem_insert_self _ _⟩
        · exact ⟨hvp_adj.symm, Finset.mem_insert_self _ _⟩
      · rw [if_neg hap] at hab
        by_cases hav : a = v
        · rw [if_pos hav] at hab; cases hab
        · rw [if_neg hav] at hab
          obtain ⟨hadj', ha'⟩ := hv'.2.2.1.1 a b hab
          exact ⟨((hK' a b).mp hadj').1, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hav, ha'⟩)⟩
    · intro a b hab
      dsimp only [d]
      by_cases hap : a = p
      · subst a
        have hbp : b ≠ p := hab.ne.symm
        by_cases hbl : b = l
        · subst b
          have h2 : d'.owns l p = false := by
            cases h : d'.owns l p with
            | false => rfl
            | true => exact absurd ((hK' l p).mp (hv'.2.2.1.1 l p h).1).2.1 (fun h => h rfl)
          simp [hbp, hvl_ne.symm, h2]
        · by_cases hbv : b = v
          · subst b; simp [hvp_ne]
          · have h1 : decide (b = l ∨ b = v) = false := by simp [hbl, hbv]
            have hab' : K'.Adj p b := (hK' p b).mpr ⟨hab, hl_nep.symm, hbl⟩
            have hba : d'.owns b p = true := by
              have hne := hv'.2.2.1.2 p b hab'
              have hno_ab : d'.owns p b = false := by
                cases h : d'.owns p b with
                | false => rfl
                | true => exact absurd (hv'.2.2.1.1 p b h).2 hp_not
              rw [hno_ab] at hne
              cases h : d'.owns b p with
              | true => rfl
              | false => exact absurd h.symm hne
            simp [hbp, hbl, hbv, h1, hba]
      · by_cases hbp : b = p
        · subst b
          by_cases hal : a = l
          · subst a
            have h2 : d'.owns l p = false := by
              cases h : d'.owns l p with
              | false => rfl
              | true => exact absurd ((hK' l p).mp (hv'.2.2.1.1 l p h).1).2.1 (fun h => h rfl)
            simp [hap, hvl_ne.symm, h2]
          · by_cases hav : a = v
            · subst a; simp [hvp_ne]
            · have h1 : decide (a = l ∨ a = v) = false := by simp [hal, hav]
              have hab' : K'.Adj a p := (hK' a p).mpr ⟨hab, hal, hl_nep.symm⟩
              have hab_own : d'.owns a p = true := by
                have hne := hv'.2.2.1.2 a p hab'
                have hno_ba : d'.owns p a = false := by
                  cases h : d'.owns p a with
                  | false => rfl
                  | true => exact absurd (hv'.2.2.1.1 p a h).2 hp_not
                rw [hno_ba] at hne
                cases h : d'.owns a p with
                | true => rfl
                | false => exact absurd h hne
              simp [hap, hal, hav, h1, hab_own]
        · have hal : a ≠ l := by intro e; rw [e] at hab; exact hbp ((hlp b).mp hab)
          have hbl : b ≠ l := by intro e; rw [e] at hab; exact hap ((hlp a).mp hab.symm)
          have hab' : K'.Adj a b := (hK' a b).mpr ⟨hab, hal, hbl⟩
          have hav_no : a = v → d'.owns a b = false := by
            intro e; rw [e]; cases h : d'.owns v b with
            | false => rfl
            | true => exact absurd ((hown_v b).mp h) hbp
          have hbv_no : b = v → d'.owns b a = false := by
            intro e; rw [e]; cases h : d'.owns v a with
            | false => rfl
            | true => exact absurd ((hown_v a).mp h) hap
          rw [if_neg hap, if_neg hbp]
          by_cases hav : a = v
          · rw [if_pos hav, if_neg (by intro e; exact hab.ne (hav.trans e.symm))]
            rw [← hav_no hav]; exact hv'.2.2.1.2 a b hab'
          · rw [if_neg hav]
            by_cases hbv : b = v
            · rw [if_pos hbv, ← hbv_no hbv]; exact hv'.2.2.1.2 a b hab'
            · rw [if_neg hbv]; exact hv'.2.2.1.2 a b hab'
  · -- TieOK d
    intro s t hst
    dsimp only [d] at hst ⊢
    by_cases hsp : s = p
    · rw [if_pos hsp] at hst; cases hst
    · rw [if_neg hsp] at hst
      obtain ⟨hs', hown'⟩ := hv'.2.2.2.1 s t hst
      have hsv : s ≠ v := by intro e; rw [e, htie_v] at hst; cases hst
      have htv : t ≠ v := fun e => hno_tie_to_v s hs' (e ▸ hst)
      have htp : t ≠ p := fun e => hp_not (e ▸ (hv'.2.2.1.1 t s hown').2)
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsv, hs'⟩), ?_⟩
      rw [if_neg htp, if_neg htv]; exact hown'
  · -- RolesOK n C d
    intro j hj
    dsimp only [d]
    by_cases hj0eq : j = j0
    · rw [if_pos hj0eq]; right
      exact ⟨p, Finset.mem_insert_self _ _, rfl, fun h => by cases h⟩
    · rw [if_neg hj0eq]
      by_cases hjb : j = shiftG j0 jbv
      · rw [if_pos hjb]; right
        exact ⟨p, Finset.mem_insert_self _ _, rfl, fun _ => by rw [if_pos rfl, hbwv, shiftW_add, ← hjb]⟩
      · rw [if_neg hjb]
        set j' := unshiftG j0 j
        have hj' : j' < C'.gates.length := by unfold j' unshiftG; split_ifs <;> omega
        have hsh : shiftG j0 j' = j := shiftG_unshiftG j0 j hj0eq
        by_cases htop : (d'.role j').1 = Kind.top
        · exact Or.inl htop
        · rcases hv'.2.2.2.2.1 j' hj' with h | ⟨t, ht, heq, hbf⟩
          · exact absurd h htop
          · right
            have htv : t ≠ v := by
              intro e; rw [e] at heq hbf
              cases hk : (d'.role j').1 with
              | top => exact absurd hk htop
              | z =>
                have : j' ∈ gatesOf d' C' Kind.z v.val :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', Prod.ext hk heq⟩
                rw [hZv_empty] at this; exact Finset.notMem_empty _ this
              | o =>
                have : j' ∈ gatesOf d' C' Kind.o v.val :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', Prod.ext hk heq⟩
                rw [hOv_empty] at this; exact Finset.notMem_empty _ this
              | b =>
                have := hbf hk
                have : j' = jbv := by omega
                exact hjb (by rw [← hsh, this])
            have htp : t ≠ p := fun e => hp_not (e ▸ ht)
            refine ⟨t, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htv, ht⟩), heq, fun hb => ?_⟩
            rw [if_neg htp, hbf hb, shiftW_add, hsh]
  · -- Per cover vertex t ∈ d.cover
    intro t ht
    rcases Finset.mem_insert.mp ht with htp | ht_er
    · subst t -- Vertex t = p!
      obtain ⟨jbv1, hjbv1, hbwv1, hrv1, hopv, hinv⟩ := (hv'.2.2.2.2.2.1 v hv_cov).1
      have hjeq : jbv = jbv1 := by omega
      subst hjeq
      obtain ⟨hopC, _, _, _⟩ := hgate_C' jbv hjbv
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- TermOK for p
        refine ⟨shiftG j0 jbv, hshG_lt jbv hjbv, ?_, ?_, hopC.trans hopv, ?_⟩
        · dsimp only [d]; rw [if_pos rfl, hbwv, shiftW_add]
        · dsimp only [d]; rw [if_neg (shiftG_ne j0 jbv), if_pos rfl]
        · dsimp only [d]; rw [if_pos rfl, if_pos rfl]
          have hzne : d'.zroot v ≠ d'.oroot v := zroot_ne_oroot hv' hv_cov
          have hpsh : shiftW n j0 p.val = p.val := shiftW_lt_n n j0 p.val p.isLt
          rcases hinv with h | h
          · rcases hR1_ins_cases jbv hjbv hRv (d'.zroot v) (d'.oroot v) h hzne with ⟨_, h2⟩ | ⟨h1, _⟩
            · rw [h2, hov_eq, hpsh]; exact Or.inr rfl
            · exact absurd (h1.trans hwv).symm hzne
          · rcases hR1_ins_cases jbv hjbv hRv (d'.oroot v) (d'.zroot v) h hzne.symm with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact absurd (h1.trans hwv).symm hzne
            · rw [h2, hov_eq, hpsh]; exact Or.inl rfl
      · -- Z_p: empty gate set, leaves {p.val}, root p.val
        have hZp_emp : gatesOf d C Kind.z p.val = ∅ := by
          ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
            iff_false, not_and]
          intro hj hr
          dsimp only [d] at hr
          split_ifs at hr with h1 h2
          · cases hr
          · cases hr
          · have hj' : unshiftG j0 j < C'.gates.length := by unfold unshiftG; split_ifs <;> omega
            rcases hv'.2.2.2.2.1 (unshiftG j0 j) hj' with htop | ⟨s, hs, heq, _⟩
            · rw [hr] at htop; cases htop
            · rw [hr] at heq; exact hp_not ((Fin.ext (by simpa using heq.symm) : s = p) ▸ hs)
        have hZp_leaves : zLeaves d p = {p.val} := by
          ext u
          simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
            Finset.mem_singleton, or_iff_left_iff_imp]
          rintro ⟨s, ⟨hs, hst⟩, _⟩
          exfalso
          dsimp only [d] at hst
          by_cases hsp : s = p
          · rw [if_pos hsp] at hst; cases hst
          · rw [if_neg hsp] at hst
            have hs' : s ∈ d'.cover := by
              rcases Finset.mem_insert.mp hs with rfl | h
              · exact absurd rfl hsp
              · exact Finset.mem_of_mem_erase h
            exact hp_not (hv'.2.2.1.1 p s (hv'.2.2.2.1 s p hst).2).2
        rw [hZp_emp, hZp_leaves]
        dsimp only [d]; rw [if_pos rfl]
        refine ⟨by simp, fun u hu => ?_, by simp, by simp⟩
        simp only [Finset.mem_singleton] at hu; subst hu
        exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h, by simp [readsIn]⟩
      · -- O_p: single gate {j0}, leaves {l.val, v.val}, root n + j0
        have hOp_eq : gatesOf d C Kind.o p.val = {j0} := by
          ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨hj, hr⟩
            dsimp only [d] at hr
            by_cases h1 : j = j0
            · exact h1
            · rw [if_neg h1] at hr
              by_cases h2 : j = shiftG j0 jbv
              · rw [if_pos h2] at hr; cases hr
              · rw [if_neg h2] at hr
                have hj' : unshiftG j0 j < C'.gates.length := by unfold unshiftG; split_ifs <;> omega
                rcases hv'.2.2.2.2.1 (unshiftG j0 j) hj' with htop | ⟨s, hs, heq, _⟩
                · rw [hr] at htop; cases htop
                · have hsp : s = p := Fin.ext (by simpa [hr] using heq.symm)
                  exact absurd (hsp ▸ hs) hp_not
          · rintro rfl; exact ⟨hj0, by dsimp only [d]; rw [if_pos rfl]⟩
        have hOp_leaves : oLeaves d p = {l.val, v.val} := by
          ext u
          simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, d, ite_true, decide_eq_true_eq]
          constructor
          · rintro ⟨r, hrv, rfl⟩; rcases hrv with h | h <;> rw [h] <;> tauto
          · rintro (rfl | rfl); exact ⟨l, Or.inl rfl, rfl⟩; exact ⟨v, Or.inr rfl, rfl⟩
        rw [hOp_eq, hOp_leaves]
        dsimp only [d]; rw [if_pos rfl]
        rw [hw_eq_v] at hj0_ins
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj; simp only [Finset.mem_singleton] at hj; subst j
          refine ⟨hj0_op, by rcases hj0_ins with h | h <;> simp [h], fun i hi => ?_⟩
          left; simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hj0_ins with h | h <;> rw [h] at hi <;> simp at hi <;> tauto
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · refine ⟨fun ⟨h1, _⟩ => by have := l.isLt; omega, ?_⟩
            rw [if_neg (by have := l.isLt; omega)]
            simp only [readsIn, Finset.sum_singleton]
            rcases hj0_ins with h | h <;> rw [h] <;>
              simp [beq_iff_eq, show v.val ≠ l.val from fun e => hvl_ne (Fin.ext e)]
          · refine ⟨fun ⟨h1, _⟩ => by have := v.isLt; omega, ?_⟩
            rw [if_neg (by have := v.isLt; omega)]
            simp only [readsIn, Finset.sum_singleton]
            rcases hj0_ins with h | h <;> rw [h] <;>
              simp [beq_iff_eq, show l.val ≠ v.val from fun e => hvl_ne (Fin.ext e.symm)]
        · intro j hj; simp only [Finset.mem_singleton] at hj; subst j
          rw [if_pos rfl]; simp only [readsIn, Finset.sum_singleton]
          rcases hj0_ins with h | h <;> rw [h] <;>
            simp [beq_iff_eq, show l.val ≠ n + j0 by have := l.isLt; omega,
              show v.val ≠ n + j0 by have := v.isLt; omega]
        · rw [if_neg (Finset.singleton_ne_empty _)]
          exact ⟨j0, Finset.mem_singleton_self _, rfl⟩
      · -- LamOK for p
        intro r hr
        dsimp only [d] at hr
        rw [if_pos rfl] at hr
        have hr' : r = l ∨ r = v := of_decide_eq_true hr
        unfold LamOK
        have hr_not : r ∉ d.cover := by
          rcases hr' with hrl | hrv
          · subst r; intro h
            rcases Finset.mem_insert.mp h with heq | her
            · exact hl_nep heq
            · have hlcov := Finset.mem_of_mem_erase her
              obtain ⟨r1, _, h1⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 hlcov
              exact ((hK' l r1).mp (hv'.2.2.1.1 l r1 h1).1).2.1 rfl
          · subst r; intro h
            rcases Finset.mem_insert.mp h with heq | her
            · exact hvp_ne heq
            · exact (Finset.mem_erase.mp her).1 rfl
        rw [if_neg hr_not]; dsimp only [d]; rw [if_pos rfl]
    · -- Vertex t ∈ d'.cover.erase v!
      obtain ⟨htv, ht'⟩ := Finset.mem_erase.mp ht_er
      have htp : t ≠ p := fun e => hp_not (e ▸ ht')
      have hg_eq : ∀ k : Kind, k ≠ Kind.b →
          gatesOf d C k t.val = (gatesOf d' C' k t.val).image (shiftG j0) := by
        intro k hkb
        ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hj, hr⟩
          dsimp only [d] at hr
          by_cases h1 : j = j0
          · rw [if_pos h1] at hr; exact absurd (Fin.ext (Prod.ext_iff.mp hr).2.symm) htp
          · rw [if_neg h1] at hr
            by_cases h2 : j = shiftG j0 jbv
            · rw [if_pos h2] at hr; exact absurd (Fin.ext (Prod.ext_iff.mp hr).2.symm) htp
            · rw [if_neg h2] at hr
              exact ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
                shiftG_unshiftG j0 j h1⟩
        · rintro ⟨j', ⟨hj', hr'⟩, rfl⟩
          have hne_bv : shiftG j0 j' ≠ shiftG j0 jbv := by
            intro e; have hjj : j' = jbv := shiftG_inj j0 e
            rw [hjj, hrole_jbv] at hr'; exact hkb (Prod.ext_iff.mp hr').1.symm
          exact ⟨hshG_lt j' hj', by
            dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), if_neg hne_bv, unshiftG_shiftG]; exact hr'⟩
      have hnoR_other : ∀ j' < C'.gates.length, j' ≠ jbv →
          (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
          (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0) :=
        fun j' hj' hne => ⟨(hgate_C' j' hj').1, hnot_R1_ins j' hj' (fun h => hne (hR1_only j' hj' h))⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- TermOK for t
        obtain ⟨jb, hjb, hbw, hrb, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht').1
        have hne_bv : jb ≠ jbv := by
          intro e; subst e
          exact htv (bw_injOn hv' d'.cover (Finset.Subset.refl _) ht' hv_cov (hbw.trans hbwv.symm))
        obtain ⟨hopC, hinC⟩ := hnoR_other jb hjb hne_bv
        refine ⟨shiftG j0 jb, hshG_lt jb hjb, ?_, ?_, hopC.trans hop, ?_⟩
        · dsimp only [d]; rw [if_neg htp, hbw, shiftW_add]
        · dsimp only [d]
          rw [if_neg (shiftG_ne j0 jb), if_neg (fun e => hne_bv (shiftG_inj j0 e)), unshiftG_shiftG]
          exact hrb
        · dsimp only [d]; rw [if_neg htp, if_neg htp, hinC]
          rcases hin with h | h <;> rw [h] <;> simp
      · -- IsOrTree Z_t
        rw [hg_eq Kind.z (by intro h; cases h)]
        have hzL : zLeaves d t = (zLeaves d' t).image (shiftW n j0) := by
          ext u
          simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro (rfl | ⟨s, ⟨hs, hst⟩, rfl⟩)
            · exact ⟨t.val, Or.inl rfl, shiftW_lt_n n j0 t.val t.isLt⟩
            · dsimp only [d] at hst ⊢
              by_cases hsp : s = p
              · rw [if_pos hsp] at hst; cases hst
              · rw [if_neg hsp] at hst ⊢
                have hs' : s ∈ d'.cover := by
                  rcases Finset.mem_insert.mp hs with rfl | h
                  · exact absurd rfl hsp
                  · exact Finset.mem_of_mem_erase h
                exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs', hst⟩, rfl⟩, rfl⟩
          · rintro ⟨a, rfl | ⟨s, ⟨hs', hst⟩, rfl⟩, rfl⟩
            · exact Or.inl (shiftW_lt_n n j0 t.val t.isLt)
            · have hsv : s ≠ v := by intro e; rw [e, htie_v] at hst; cases hst
              have hsp : s ≠ p := fun e => hp_not (e ▸ hs')
              right
              exact ⟨s, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsv, hs'⟩),
                by dsimp only [d]; rw [if_neg hsp]; exact hst⟩, by dsimp only [d]; rw [if_neg hsp]⟩
        rw [hzL]; dsimp only [d]; rw [if_neg htp]
        apply orTree_shift (hv'.2.2.2.2.2.1 t ht').2.1
        intro j' hj'
        have hj'lt := hg_lt _ _ j' hj'
        have hne_bv : j' ≠ jbv := by
          intro e; have hrz := (Finset.mem_filter.mp hj').2
          rw [e, hrole_jbv] at hrz; cases hrz
        exact hnoR_other j' hj'lt hne_bv
      · -- IsOrTree O_t
        rw [hg_eq Kind.o (by intro h; cases h)]
        have hoL : oLeaves d t = (oLeaves d' t).image (shiftW n j0) := by
          ext u
          simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            d, if_neg htp, if_neg htv]
          constructor
          · rintro ⟨r, hr, rfl⟩; exact ⟨d'.lam t r, ⟨r, hr, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩
        rw [hoL]; dsimp only [d]; rw [if_neg htp]
        apply orTree_shift (hv'.2.2.2.2.2.1 t ht').2.2.1
        intro j' hj'
        have hj'lt := hg_lt _ _ j' hj'
        have hne_bv : j' ≠ jbv := by
          intro e; have hro := (Finset.mem_filter.mp hj').2
          rw [e, hrole_jbv] at hro; cases hro
        exact hnoR_other j' hj'lt hne_bv
      · -- LamOK for t
        intro r hr
        dsimp only [d] at hr; rw [if_neg htp, if_neg htv] at hr
        have hlam' := (hv'.2.2.2.2.2.1 t ht').2.2.2 r hr
        unfold LamOK at hlam' ⊢
        dsimp only [d]
        rw [if_neg htp]
        by_cases hrp : r = p
        · subst r
          rw [if_neg hp_not] at hlam'
          rw [if_pos (Finset.mem_insert_self _ _), hlam', shiftW_lt_n n j0 p.val p.isLt]
          refine ⟨(isCentred_input C d p).mpr (Finset.mem_insert_self _ _), Or.inl rfl, fun h => ?_⟩
          rw [if_pos rfl] at h; cases h
        · by_cases hrv : r = v
          · subst r
            rw [if_pos hv_cov] at hlam'
            have hr_not : v ∉ insert p (d'.cover.erase v) := by
              intro h; rcases Finset.mem_insert.mp h with heq | her
              · exact hrp heq
              · exact (Finset.mem_erase.mp her).1 rfl
            rw [if_neg hr_not]
            rcases hlam'.2.1 with h1 | ⟨jz, hjz, _, h2⟩
            · rw [h1, shiftW_lt_n n j0 v.val v.isLt]
            · have : jz ∈ gatesOf d' C' Kind.z v.val :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjz, h2⟩
              rw [hZv_empty] at this; exact absurd this (Finset.notMem_empty _)
          · have hr_iff : r ∈ insert p (d'.cover.erase v) ↔ r ∈ d'.cover := by
              simp [hrp, hrv]
            by_cases hr' : r ∈ d'.cover
            · rw [if_pos hr'] at hlam'
              rw [if_pos (hr_iff.mpr hr')]
              have hcen_iff := centred_shift_z (K := K) (d := d) hRB hv' hC'_len hj0 r hr' (hr_iff.mpr hr')
                (fun j' hj' => by
                  have hj'lt := hg_lt _ _ j' hj'
                  have hne_bv : j' ≠ jbv := by
                    intro e; have hrz := (Finset.mem_filter.mp hj').2
                    rw [e, hrole_jbv] at hrz; cases hrz
                  refine ⟨?_, (hnoR_other j' hj'lt hne_bv).2⟩
                  dsimp only [d]
                  rw [if_neg (shiftG_ne j0 j'), if_neg (fun e => hne_bv (shiftG_inj j0 e)),
                    unshiftG_shiftG]
                  exact (Finset.mem_filter.mp hj').2)
                (fun s hs htie => by
                  obtain ⟨jbs, hjbs, hbws, hrbs⟩ := bw_spec hv' s hs
                  have hsv : s ≠ v := by intro e; rw [e, htie_v] at htie; cases htie
                  have hne_bv : jbs ≠ jbv := by
                    intro e; subst e
                    exact hsv (bw_injOn hv' d'.cover (Finset.Subset.refl _) hs hv_cov (hbws.trans hbwv.symm))
                  refine ⟨jbs, hjbs, hbws, ?_⟩
                  dsimp only [d]
                  rw [if_neg (shiftG_ne j0 jbs), if_neg (fun e => hne_bv (shiftG_inj j0 e)),
                    unshiftG_shiftG, hrbs])
              refine ⟨(hcen_iff (d'.lam t r) hlam'.2.1).mpr hlam'.1, ?_, ?_⟩
              · rcases hlam'.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
                · exact Or.inl (by rw [h1, shiftW_lt_n n j0 r.val r.isLt])
                · right
                  have hne_bv : jz ≠ jbv := by
                    intro e; rw [e, hrole_jbv] at h2; cases h2
                  refine ⟨shiftG j0 jz, hshG_lt jz hjz, by rw [h1, shiftW_add], ?_⟩
                  rw [if_neg (shiftG_ne j0 jz), if_neg (fun e => hne_bv (shiftG_inj j0 e)),
                    unshiftG_shiftG, h2]
              · intro htie; rw [if_neg hrp] at htie
                rw [if_neg hrp, hlam'.2.2 htie]
            · rw [if_neg hr'] at hlam'
              rw [if_neg (fun h => hr' (hr_iff.mp h)), hlam', shiftW_lt_n n j0 r.val r.isLt]
  · -- IsOrTree TOP
    have htop_eq : topGates d C = (topGates d' C').image (shiftG j0) := by
      ext j; simp only [topGates, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hr⟩
        dsimp only [d] at hr
        by_cases h1 : j = j0
        · rw [if_pos h1] at hr; cases hr
        · rw [if_neg h1] at hr
          by_cases h2 : j = shiftG j0 jbv
          · rw [if_pos h2] at hr; cases hr
          · rw [if_neg h2] at hr
            exact ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
              shiftG_unshiftG j0 j h1⟩
      · rintro ⟨j', ⟨hj', hr'⟩, rfl⟩
        have hne_bv : j' ≠ jbv := by
          intro e; rw [e, hrole_jbv] at hr'; cases hr'
        exact ⟨hshG_lt j' hj', by
          dsimp only [d]; rw [if_neg (shiftG_ne j0 j'),
            if_neg (fun e => hne_bv (shiftG_inj j0 e)), unshiftG_shiftG]; exact hr'⟩
    have htopL : topLeaves d A = (topLeaves d' A).image (shiftW n j0) := by
      ext u
      simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro (⟨a, ha, rfl⟩ | ⟨s, ⟨hs, hst⟩, rfl⟩)
        · exact ⟨a.val, Or.inl ⟨a, ha, rfl⟩, shiftW_lt_n n j0 a.val a.isLt⟩
        · dsimp only [d] at hst ⊢
          by_cases hsp : s = p
          · subst s; rw [if_pos rfl]
            exact ⟨d'.bw v, Or.inr ⟨v, ⟨hv_cov, htie_v⟩, rfl⟩, rfl⟩
          · rw [if_neg hsp] at hst ⊢
            have hs' : s ∈ d'.cover := by
              rcases Finset.mem_insert.mp hs with rfl | h
              · exact absurd rfl hsp
              · exact Finset.mem_of_mem_erase h
            exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs', hst⟩, rfl⟩, rfl⟩
      · rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨s, ⟨hs', hst⟩, rfl⟩), rfl⟩
        · exact Or.inl ⟨a, ha, (shiftW_lt_n n j0 a.val a.isLt).symm⟩
        · by_cases hsv : s = v
          · subst s; right
            exact ⟨p, ⟨Finset.mem_insert_self _ _, by dsimp only [d]; rw [if_pos rfl]⟩,
              by dsimp only [d]; rw [if_pos rfl]⟩
          · have hsp : s ≠ p := fun e => hp_not (e ▸ hs')
            right
            exact ⟨s, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsv, hs'⟩),
              by dsimp only [d]; rw [if_neg hsp]; exact hst⟩, by dsimp only [d]; rw [if_neg hsp]⟩
    rw [htop_eq, htopL, hout_eq_sh]
    apply orTree_shift hv'.2.2.2.2.2.2
    intro j' hj'
    have hj'lt := htop_lt j' hj'
    exact ⟨(hgate_C' j' hj'lt).1, hnot_R1_ins j' hj'lt (hR1_no_top j' hj')⟩

private lemma fwd_branch_splice {n : ℕ} {K K' : SimpleGraph (Fin n)}
    [DecidableRel K.Adj] [DecidableRel K'.Adj] {A : Finset (Fin n)} {l p : Fin n}
    {C C' : Circuit} {j0 w : ℕ} {d' : NCCData n} {T0 : Finset (Fin n)}
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (hT0 : IsMinCover K T0)
    (hC'_len : C'.gates.length + 1 = C.gates.length)
    (hj0 : j0 < C.gates.length)
    (hw_lt : w < n + j0)
    (hw_nel : w ≠ l.val)
    (hj0_op : (gateAt C j0).op = GateOp.or)
    (hj0_ins : (gateAt C j0).inputs = [l.val, w] ∨ (gateAt C j0).inputs = [w, l.val])
    (hRB : ReadsBack n C)
    (hv' : Valid n K' A C' d')
    (hgate_C' : ∀ j' < C'.gates.length,
      (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs.length = 2 ∧
      (gateAt C' j').inputs = (gateAt C (shiftG j0 j')).inputs.map (remapW n j0 w) ∧
      ∀ i ∈ (gateAt C (shiftG j0 j')).inputs, i < n + shiftG j0 j' ∧ i ≠ l.val)
    (hnot_R1_ins : ∀ j' < C'.gates.length, ¬ readsJ0 n j0 C j' →
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0))
    (hR1_mem_w : ∀ j' < C'.gates.length, readsJ0 n j0 C j' → w ∈ (gateAt C' j').inputs)
    (hR1_ins_cases : ∀ j' < C'.gates.length, readsJ0 n j0 C j' →
      ∀ a b, (gateAt C' j').inputs = [a, b] → a ≠ b →
        (a = w ∧ (gateAt C (shiftG j0 j')).inputs = [n + j0, shiftW n j0 b]) ∨
        (b = w ∧ (gateAt C (shiftG j0 j')).inputs = [shiftW n j0 a, n + j0]))
    (hout_eq_sh : C.output = shiftW n j0 C'.output)
    (hR1_nonempty : ∃ j' < C'.gates.length, readsJ0 n j0 C j')
    (hR1_no_top : ∀ j' ∈ topGates d' C', ¬ readsJ0 n j0 C j')
    (hR1_no_z : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.z t.val, ¬ readsJ0 n j0 C j')
    (hR1_o_eq_p : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.o t.val, readsJ0 n j0 C j' → t = p)
    (hR1_b_oroot_eq_p : ∀ t ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw t = n + jb → readsJ0 n j0 C jb → w = d'.oroot t → t = p)
    (hflip : ∀ v ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw v = n + jb → readsJ0 n j0 C jb → w ≠ d'.zroot v) :
    IsNestedCoverCircuit n K A C := by
  classical
  have hlp_adj : K.Adj l p := (hlp p).mpr rfl
  have hl_nep : l ≠ p := hlp_adj.ne
  have hshG_lt : ∀ j' < C'.gates.length, shiftG j0 j' < C.gates.length := by
    intro j' hj'; unfold shiftG; split_ifs <;> omega
  have htop_lt : ∀ j' ∈ topGates d' C', j' < C'.gates.length :=
    fun j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hg_lt : ∀ k t, ∀ j' ∈ gatesOf d' C' k t, j' < C'.gates.length :=
    fun _ _ j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hR1_in_Op : ∀ j' < C'.gates.length, readsJ0 n j0 C j' →
      p ∈ d'.cover ∧
      (j' ∈ gatesOf d' C' Kind.o p.val ∨ (d'.bw p = n + j' ∧ w = d'.oroot p)) := by
    intro j' hj' hR
    rcases hv'.2.2.2.2.1 j' hj' with htop | ⟨t, ht, heq, hbf⟩
    · exact absurd hR (hR1_no_top j' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', htop⟩))
    · cases hkind : (d'.role j').1 with
      | top =>
        exact absurd hR (hR1_no_top j' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', hkind⟩))
      | z =>
        exact absurd hR (hR1_no_z t ht j'
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', Prod.ext hkind heq⟩))
      | o =>
        have hmem : j' ∈ gatesOf d' C' Kind.o t.val :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', Prod.ext hkind heq⟩
        have htp := hR1_o_eq_p t ht j' hmem hR
        subst htp; exact ⟨ht, Or.inl hmem⟩
      | b =>
        have hbw := hbf hkind
        obtain ⟨jb1, _, hbw1, _, _, hin1⟩ := (hv'.2.2.2.2.2.1 t ht).1
        have hjj : j' = jb1 := by omega
        have hwm := hR1_mem_w j' hj' hR
        rw [hjj] at hwm
        have hmem : w = d'.zroot t ∨ w = d'.oroot t := by
          rcases hin1 with h | h <;> rw [h] at hwm <;> simp at hwm <;> tauto
        rcases hmem with hzw | how
        · exact absurd hzw (hflip t ht j' hj' hbw hR)
        · have htp := hR1_b_oroot_eq_p t ht j' hj' hbw hR how
          subst htp; exact ⟨ht, Or.inr ⟨hbw, how⟩⟩
  obtain ⟨j1, hj1, hR1_ex⟩ := hR1_nonempty
  have hp_cov : p ∈ d'.cover := (hR1_in_Op j1 hj1 hR1_ex).1
  have hOp_tree := (hv'.2.2.2.2.2.1 p hp_cov).2.2.1
  obtain ⟨jbp, hjbp, hbwp, hrbp, hopp, hinp⟩ := (hv'.2.2.2.2.2.1 p hp_cov).1
  have hl_not_oL : l.val ∉ oLeaves d' p := by
    simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and]
    intro r hr heq
    have hlam := (hv'.2.2.2.2.2.1 p hp_cov).2.2.2 r hr
    have hrl : r ≠ l := by
      intro e; exact ((hK' p l).mp (hv'.2.2.1.1 p l (e ▸ hr)).1).2.2 rfl
    unfold LamOK at hlam
    split_ifs at hlam with hrc
    · rcases hlam.2.1 with h1 | ⟨jz, _, h1, _⟩
      · exact hrl (Fin.ext (by omega))
      · have := l.isLt; omega
    · exact hrl (Fin.ext (by omega))
  let d : NCCData n := {
    cover := d'.cover
    owns := fun a b => if a = p ∧ b = l then true else d'.owns a b
    tie := d'.tie
    role := fun j => if j = j0 then (Kind.o, p.val) else d'.role (unshiftG j0 j)
    bw := fun t => shiftW n j0 (d'.bw t)
    zroot := fun t => shiftW n j0 (d'.zroot t)
    oroot := fun t => if t = p ∧ w = d'.oroot p then n + j0 else shiftW n j0 (d'.oroot t)
    lam := fun t r => if t = p ∧ r = l then l.val else shiftW n j0 (d'.lam t r)
  }
  have hnoR_non_Op : ∀ j' < C'.gates.length,
      j' ∉ gatesOf d' C' Kind.o p.val → (j' = jbp → w ≠ d'.oroot p) →
      (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0) := by
    intro j' hj' hnoO hnoB
    refine ⟨(hgate_C' j' hj').1, hnot_R1_ins j' hj' (fun hR => ?_)⟩
    rcases (hR1_in_Op j' hj' hR).2 with h1 | ⟨h1, h2⟩
    · exact hnoO h1
    · exact hnoB (by omega) h2
  refine ⟨d, hRB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsMinCover K d.cover
    have hcov : K.IsVertexCover (d.cover : Set (Fin n)) := by
      intro a b hab
      by_cases hal : a = l
      · subst hal; rw [(hlp b).mp hab]; exact Or.inr hp_cov
      · by_cases hbl : b = l
        · subst hbl; rw [(hlp a).mp hab.symm]; exact Or.inl hp_cov
        · exact hv'.2.1.1 ((hK' a b).mpr ⟨hab, hal, hbl⟩)
    refine ⟨hcov, fun S hS => ?_⟩
    have hT0eq := minCover_card_eq hlp hfree hK' hT0 hv'.2.1
    have hle := hT0.2 S hS
    change d'.cover.card ≤ S.card; omega
  · -- OwnerOK K d
    refine ⟨?_, ?_⟩
    · intro a b hab
      dsimp only [d] at hab ⊢
      by_cases h1 : a = p ∧ b = l
      · obtain ⟨hap, hbl⟩ := h1; subst a; subst b; exact ⟨hlp_adj.symm, hp_cov⟩
      · rw [if_neg h1] at hab
        obtain ⟨hadj', ha'⟩ := hv'.2.2.1.1 a b hab
        exact ⟨((hK' a b).mp hadj').1, ha'⟩
    · intro a b hab
      dsimp only [d]
      by_cases h1 : a = p ∧ b = l
      · obtain ⟨hap, hbl⟩ := h1; subst a; subst b
        have h2 : ¬ (l = p ∧ p = l) := fun h => hl_nep h.1
        have hno : d'.owns l p = false := by
          cases h : d'.owns l p with
          | false => rfl
          | true => exact absurd ((hK' l p).mp (hv'.2.2.1.1 l p h).1).2.1 (fun h => h rfl)
        rw [if_pos ⟨rfl, rfl⟩, if_neg h2, hno]; decide
      · by_cases h2 : b = p ∧ a = l
        · obtain ⟨hbp, hal⟩ := h2; subst b; subst a
          have hno : d'.owns l p = false := by
            cases h : d'.owns l p with
            | false => rfl
            | true => exact absurd ((hK' l p).mp (hv'.2.2.1.1 l p h).1).2.1 (fun h => h rfl)
          rw [if_neg h1, if_pos ⟨rfl, rfl⟩, hno]; decide
        · rw [if_neg h1, if_neg h2]
          have hal : a ≠ l := by intro e; rw [e] at hab; exact h2 ⟨(hlp b).mp hab, e⟩
          have hbl : b ≠ l := by intro e; rw [e] at hab; exact h1 ⟨(hlp a).mp hab.symm, e⟩
          exact hv'.2.2.1.2 a b ((hK' a b).mpr ⟨hab, hal, hbl⟩)
  · -- TieOK d
    intro s t hst
    obtain ⟨hs', hown'⟩ := hv'.2.2.2.1 s t hst
    refine ⟨hs', ?_⟩
    dsimp only [d]
    split_ifs with h
    · rfl
    · exact hown'
  · -- RolesOK n C d
    intro j hj
    dsimp only [d]
    by_cases hj0eq : j = j0
    · rw [if_pos hj0eq]; right; exact ⟨p, hp_cov, rfl, fun h => by cases h⟩
    · rw [if_neg hj0eq]
      have hj' : unshiftG j0 j < C'.gates.length := by unfold unshiftG; split_ifs <;> omega
      rcases hv'.2.2.2.2.1 (unshiftG j0 j) hj' with htop | ⟨t, ht, heq, hbf⟩
      · exact Or.inl htop
      · right
        exact ⟨t, ht, heq, fun hb => by rw [hbf hb, shiftW_add, shiftG_unshiftG j0 j hj0eq]⟩
  · -- Per cover vertex t ∈ d.cover
    intro t ht
    have hzg_eq : gatesOf d C Kind.z t.val = (gatesOf d' C' Kind.z t.val).image (shiftG j0) := by
      ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hr⟩
        dsimp only [d] at hr
        by_cases h1 : j = j0
        · rw [if_pos h1] at hr; cases hr
        · rw [if_neg h1] at hr
          exact ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
            shiftG_unshiftG j0 j h1⟩
      · rintro ⟨j', ⟨hj', hr'⟩, rfl⟩
        exact ⟨hshG_lt j' hj', by
          dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), unshiftG_shiftG]; exact hr'⟩
    have hzL_eq : zLeaves d t = (zLeaves d' t).image (shiftW n j0) := by
      ext u; simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, d]
      constructor
      · rintro (rfl | ⟨s, ⟨hs, hst⟩, rfl⟩)
        · exact ⟨t.val, Or.inl rfl, shiftW_lt_n n j0 t.val t.isLt⟩
        · exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs, hst⟩, rfl⟩, rfl⟩
      · rintro ⟨_, rfl | ⟨s, ⟨hs, hst⟩, rfl⟩, rfl⟩
        · exact Or.inl (shiftW_lt_n n j0 t.val t.isLt)
        · exact Or.inr ⟨s, ⟨hs, hst⟩, rfl⟩
    have hZ_ok : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t) := by
      rw [hzg_eq, hzL_eq]
      apply orTree_shift (hv'.2.2.2.2.2.1 t ht).2.1
      intro j' hj'
      have hj'lt := hg_lt _ _ j' hj'
      exact ⟨(hgate_C' j' hj'lt).1, hnot_R1_ins j' hj'lt (hR1_no_z t ht j' hj')⟩
    have hLam_ok : ∀ r, d.owns t r = true → LamOK n C d t r := by
      intro r hr
      dsimp only [d] at hr
      by_cases hpl : t = p ∧ r = l
      · obtain ⟨htp, hrl⟩ := hpl; subst t; subst r
        have hl_not_cov : l ∉ d'.cover := by
          intro hc
          obtain ⟨r1, _, h1⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 hc
          exact ((hK' l r1).mp (hv'.2.2.1.1 l r1 h1).1).2.1 rfl
        unfold LamOK; dsimp only [d]; rw [if_neg hl_not_cov, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hpl] at hr
        have hlam' := (hv'.2.2.2.2.2.1 t ht).2.2.2 r hr
        unfold LamOK at hlam' ⊢; dsimp only [d]; rw [if_neg hpl]
        by_cases hr' : r ∈ d'.cover
        · rw [if_pos hr'] at hlam' ⊢
          have hcen_iff := centred_shift_z (K := K) (d := d) hRB hv' hC'_len hj0 r hr' hr'
            (fun j' hj' => by
              have hj'lt := hg_lt _ _ j' hj'
              refine ⟨by dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), unshiftG_shiftG]; exact (Finset.mem_filter.mp hj').2,
                hnot_R1_ins j' hj'lt (hR1_no_z r hr' j' hj')⟩)
            (fun s hs _ => by
              obtain ⟨jbs, hjbs, hbws, hrbs⟩ := bw_spec hv' s hs
              exact ⟨jbs, hjbs, hbws, by dsimp only [d]; rw [if_neg (shiftG_ne j0 jbs), unshiftG_shiftG, hrbs]⟩)
          refine ⟨(hcen_iff (d'.lam t r) hlam'.2.1).mpr hlam'.1, ?_, ?_⟩
          · rcases hlam'.2.1 with h1 | ⟨jz, hjz, h1, h2⟩
            · exact Or.inl (by rw [h1, shiftW_lt_n n j0 r.val r.isLt])
            · exact Or.inr ⟨shiftG j0 jz, hshG_lt jz hjz, by rw [h1, shiftW_add], by
                rw [if_neg (shiftG_ne j0 jz), unshiftG_shiftG, h2]⟩
          · intro htie; rw [hlam'.2.2 htie]
        · rw [if_neg hr'] at hlam' ⊢
          rw [hlam', shiftW_lt_n n j0 r.val r.isLt]
    by_cases htp : t = p
    · subst t
      have hog_eq : gatesOf d C Kind.o p.val = insert j0 ((gatesOf d' C' Kind.o p.val).image (shiftG j0)) := by
        ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_image]
        constructor
        · rintro ⟨hj, hr⟩
          dsimp only [d] at hr
          by_cases h1 : j = j0
          · exact Or.inl h1
          · rw [if_neg h1] at hr
            exact Or.inr ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
              shiftG_unshiftG j0 j h1⟩
        · rintro (rfl | ⟨j', ⟨hj', hr'⟩, rfl⟩)
          · exact ⟨hj0, by dsimp only [d]; rw [if_pos rfl]⟩
          · exact ⟨hshG_lt j' hj', by
              dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), unshiftG_shiftG]; exact hr'⟩
      have hoL_eq : oLeaves d p = insert l.val ((oLeaves d' p).image (shiftW n j0)) := by
        ext u
        simp only [oLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and, d]
        constructor
        · rintro ⟨r, hr, rfl⟩
          by_cases hrl : r = l
          · subst r; rw [if_pos rfl]; exact Or.inl rfl
          · rw [if_neg hrl] at hr ⊢
            exact Or.inr ⟨d'.lam p r, ⟨r, hr, rfl⟩, rfl⟩
        · rintro (rfl | ⟨_, ⟨r, hr, rfl⟩, rfl⟩)
          · exact ⟨l, by rw [if_pos rfl], by rw [if_pos rfl]⟩
          · have hrl : r ≠ l := by
              intro e; exact ((hK' p l).mp (hv'.2.2.1.1 p l (e ▸ hr)).1).2.2 rfl
            exact ⟨r, by rw [if_neg hrl]; exact hr, by rw [if_neg hrl]⟩
      by_cases hwo : w = d'.oroot p
      · -- Subcase A1: w = d'.oroot p!
        have hnoR_Op : ∀ j' ∈ gatesOf d' C' Kind.o p.val, ¬ readsJ0 n j0 C j' := by
          intro j' hj' hR
          have hwm := hR1_mem_w j' (hg_lt _ _ j' hj') hR
          have hcnt : 0 < (gateAt C' j').inputs.count w := List.count_pos_iff.mpr hwm
          have h0 : readsIn C' (gatesOf d' C' Kind.o p.val) (d'.oroot p) = 0 := by
            rcases orTree_top_mem hOp_tree with hL | ⟨h1, h2⟩
            · have := (hOp_tree.2.1 (d'.oroot p) hL).2; rw [if_pos rfl] at this; exact this
            · have hsub : n + (d'.oroot p - n) = d'.oroot p := by omega
              have := hOp_tree.2.2.1 (d'.oroot p - n) h2; rw [hsub, if_pos rfl] at this; exact this
          have hle : (gateAt C' j').inputs.count (d'.oroot p) ≤
              readsIn C' (gatesOf d' C' Kind.o p.val) (d'.oroot p) :=
            Finset.single_le_sum (f := fun j => (gateAt C' j).inputs.count (d'.oroot p))
              (fun _ _ => Nat.zero_le _) hj'
          rw [hwo] at hcnt; omega
        have hRb_p : readsJ0 n j0 C jbp := by
          rcases (hR1_in_Op j1 hj1 hR1_ex).2 with h1 | ⟨h1, _⟩
          · exact absurd hR1_ex (hnoR_Op j1 h1)
          · have : j1 = jbp := by omega
            exact this ▸ hR1_ex
        refine ⟨?_, hZ_ok, ?_, hLam_ok⟩
        · -- TermOK for p (B_p reads n + j0 instead of d'.oroot p)
          obtain ⟨hopC, _, _, _⟩ := hgate_C' jbp hjbp
          have hzne : d'.zroot p ≠ d'.oroot p := zroot_ne_oroot hv' hp_cov
          refine ⟨shiftG j0 jbp, hshG_lt jbp hjbp, by dsimp only [d]; rw [hbwp, shiftW_add],
            by dsimp only [d]; rw [if_neg (shiftG_ne j0 jbp), unshiftG_shiftG, hrbp],
            hopC.trans hopp, ?_⟩
          dsimp only [d]; rw [if_pos ⟨rfl, hwo⟩]
          rcases hinp with h | h
          · rcases hR1_ins_cases jbp hjbp hRb_p (d'.zroot p) (d'.oroot p) h hzne with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact absurd (h1.trans hwo) hzne
            · exact Or.inl h2
          · rcases hR1_ins_cases jbp hjbp hRb_p (d'.oroot p) (d'.zroot p) h hzne.symm with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact Or.inr h2
            · exact absurd (h1.trans hwo) hzne
        · -- IsOrTree O_p (splice at root)
          rw [hog_eq, hoL_eq]; dsimp only [d]; rw [if_pos ⟨rfl, hwo⟩]
          have hOp_w : IsOrTree n C' (gatesOf d' C' Kind.o p.val) (oLeaves d' p) w := hwo ▸ hOp_tree
          exact orTree_splice_root hOp_w hw_lt hw_nel hl_not_oL hj0_op hj0_ins
            (fun j' hj' => ⟨(hgate_C' j' (hg_lt _ _ j' hj')).1,
              hnot_R1_ins j' (hg_lt _ _ j' hj') (hnoR_Op j' hj')⟩)
      · -- Subcase A2: w ≠ d'.oroot p!
        have hj1_O : j1 ∈ gatesOf d' C' Kind.o p.val := by
          rcases (hR1_in_Op j1 hj1 hR1_ex).2 with h1 | ⟨_, h2⟩
          · exact h1
          · exact absurd h2 hwo
        have hwm1 : w ∈ (gateAt C' j1).inputs := hR1_mem_w j1 hj1 hR1_ex
        have hw_mem_Op : w ∈ oLeaves d' p ∨ (n ≤ w ∧ w - n ∈ gatesOf d' C' Kind.o p.val) :=
          (hOp_tree.1 j1 hj1_O).2.2 w hwm1
        have hrc_w : readsIn C' (gatesOf d' C' Kind.o p.val) w = 1 := by
          rcases hw_mem_Op with hwL | ⟨h1, h2⟩
          · have := (hOp_tree.2.1 w hwL).2; rw [if_neg hwo] at this; exact this
          · have hsub : n + (w - n) = w := by omega
            have := hOp_tree.2.2.1 (w - n) h2; rw [hsub, if_neg hwo] at this; exact this
        have hcnt1 : (gateAt C' j1).inputs.count w = 1 := by
          have hpos : 0 < (gateAt C' j1).inputs.count w := List.count_pos_iff.mpr hwm1
          have hle : (gateAt C' j1).inputs.count w ≤ readsIn C' (gatesOf d' C' Kind.o p.val) w :=
            Finset.single_le_sum (f := fun j => (gateAt C' j).inputs.count w)
              (fun _ _ => Nat.zero_le _) hj1_O
          omega
        have hother_noR : ∀ j' ∈ gatesOf d' C' Kind.o p.val, j' ≠ j1 → ¬ readsJ0 n j0 C j' := by
          intro j' hj' hne hR'
          have hwm' : w ∈ (gateAt C' j').inputs := hR1_mem_w j' (hg_lt _ _ j' hj') hR'
          have hpos' : 0 < (gateAt C' j').inputs.count w := List.count_pos_iff.mpr hwm'
          have hsum_er := Finset.add_sum_erase (gatesOf d' C' Kind.o p.val)
            (fun j => (gateAt C' j).inputs.count w) hj1_O
          have hle' : (gateAt C' j').inputs.count w ≤
              ∑ j ∈ (gatesOf d' C' Kind.o p.val).erase j1, (gateAt C' j).inputs.count w :=
            Finset.single_le_sum (f := fun j => (gateAt C' j).inputs.count w)
              (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, hj'⟩)
          change readsIn C' (gatesOf d' C' Kind.o p.val) w = 1 at hrc_w
          unfold readsIn at hrc_w; omega
        have hg1_in : ∃ b, b ≠ w ∧
            ((gateAt C' j1).inputs = [w, b] ∧ (gateAt C (shiftG j0 j1)).inputs = [n + j0, shiftW n j0 b] ∨
             (gateAt C' j1).inputs = [b, w] ∧ (gateAt C (shiftG j0 j1)).inputs = [shiftW n j0 b, n + j0]) := by
          have hlen1 := (hOp_tree.1 j1 hj1_O).2.1
          rcases h : (gateAt C' j1).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · simp [h] at hlen1
          · simp [h] at hlen1
          · rw [h] at hwm1 hcnt1
            have hab : a ≠ b := by
              intro e; subst e
              have hwa : w = a := by simpa using hwm1
              rw [hwa] at hcnt1; simp at hcnt1
            rcases hR1_ins_cases j1 hj1 hR1_ex a b h hab with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
            · exact ⟨b, hab.symm, Or.inl ⟨rfl, h2⟩⟩
            · exact ⟨a, hab, Or.inr ⟨rfl, h2⟩⟩
          · simp [h] at hlen1
        refine ⟨?_, hZ_ok, ?_, hLam_ok⟩
        · -- TermOK for p (B_p unchanged!)
          have hjb_notO : jbp ∉ gatesOf d' C' Kind.o p.val := by
            intro h; have hro := (Finset.mem_filter.mp h).2; rw [hrbp] at hro; cases hro
          obtain ⟨hopC, hinC⟩ := hnoR_non_Op jbp hjbp hjb_notO (fun _ => hwo)
          refine ⟨shiftG j0 jbp, hshG_lt jbp hjbp, by dsimp only [d]; rw [hbwp, shiftW_add],
            by dsimp only [d]; rw [if_neg (shiftG_ne j0 jbp), unshiftG_shiftG, hrbp],
            hopC.trans hopp, ?_⟩
          dsimp only [d]; rw [if_neg (fun h => hwo h.2), hinC]
          rcases hinp with h | h <;> rw [h] <;> simp
        · -- IsOrTree O_p (splice at inner node w)
          rw [hog_eq, hoL_eq]; dsimp only [d]; rw [if_neg (fun h => hwo h.2)]
          exact orTree_splice_inner hOp_tree hwo hw_lt hw_nel hl_not_oL hw_mem_Op hj1_O
            (hgate_C' j1 hj1).1 hg1_in hj0_op hj0_ins
            (fun j' hj' hne => ⟨(hgate_C' j' (hg_lt _ _ j' hj')).1,
              hnot_R1_ins j' (hg_lt _ _ j' hj') (hother_noR j' hj' hne)⟩)
    · -- Vertex t ≠ p: everything simply shifts!
      have hog_eq : gatesOf d C Kind.o t.val = (gatesOf d' C' Kind.o t.val).image (shiftG j0) := by
        ext j; simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hj, hr⟩
          dsimp only [d] at hr
          by_cases h1 : j = j0
          · rw [if_pos h1] at hr; exact absurd (Fin.ext (Prod.ext_iff.mp hr).2.symm) htp
          · rw [if_neg h1] at hr
            exact ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
              shiftG_unshiftG j0 j h1⟩
        · rintro ⟨j', ⟨hj', hr'⟩, rfl⟩
          exact ⟨hshG_lt j' hj', by
            dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), unshiftG_shiftG]; exact hr'⟩
      have hoL_eq : oLeaves d t = (oLeaves d' t).image (shiftW n j0) := by
        ext u
        simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, d,
          show ¬ (t = p ∧ _) from fun h => htp h.1, ↓reduceIte]
        constructor
        · rintro ⟨r, hr, rfl⟩; exact ⟨d'.lam t r, ⟨r, hr, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩
      refine ⟨?_, hZ_ok, ?_, hLam_ok⟩
      · obtain ⟨jb, hjb, hbw, hrb, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
        have hnotO : jb ∉ gatesOf d' C' Kind.o p.val := by
          intro h; have hro := (Finset.mem_filter.mp h).2; rw [hrb] at hro; cases hro
        have hne_bp : jb ≠ jbp := by
          intro e; subst e
          exact htp (bw_injOn hv' d'.cover (Finset.Subset.refl _) ht hp_cov (hbw.trans hbwp.symm))
        obtain ⟨hopC, hinC⟩ := hnoR_non_Op jb hjb hnotO (fun h => absurd h hne_bp)
        refine ⟨shiftG j0 jb, hshG_lt jb hjb, by dsimp only [d]; rw [hbw, shiftW_add],
          by dsimp only [d]; rw [if_neg (shiftG_ne j0 jb), unshiftG_shiftG, hrb],
          hopC.trans hop, ?_⟩
        dsimp only [d]; rw [if_neg (fun h => htp h.1), hinC]
        rcases hin with h | h <;> rw [h] <;> simp
      · rw [hog_eq, hoL_eq]; dsimp only [d]; rw [if_neg (fun h => htp h.1)]
        apply orTree_shift (hv'.2.2.2.2.2.1 t ht).2.2.1
        intro j' hj'
        have hj'lt := hg_lt _ _ j' hj'
        exact ⟨(hgate_C' j' hj'lt).1,
          hnot_R1_ins j' hj'lt (fun hR => htp (hR1_o_eq_p t ht j' hj' hR))⟩
  · -- IsOrTree TOP
    have htop_eq : topGates d C = (topGates d' C').image (shiftG j0) := by
      ext j; simp only [topGates, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hr⟩
        dsimp only [d] at hr
        by_cases h1 : j = j0
        · rw [if_pos h1] at hr; cases hr
        · rw [if_neg h1] at hr
          exact ⟨unshiftG j0 j, ⟨by unfold unshiftG; split_ifs <;> omega, hr⟩,
            shiftG_unshiftG j0 j h1⟩
      · rintro ⟨j', ⟨hj', hr'⟩, rfl⟩
        exact ⟨hshG_lt j' hj', by
          dsimp only [d]; rw [if_neg (shiftG_ne j0 j'), unshiftG_shiftG]; exact hr'⟩
    have htopL : topLeaves d A = (topLeaves d' A).image (shiftW n j0) := by
      ext u; simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter, d]
      constructor
      · rintro (⟨a, ha, rfl⟩ | ⟨s, ⟨hs, hst⟩, rfl⟩)
        · exact ⟨a.val, Or.inl ⟨a, ha, rfl⟩, shiftW_lt_n n j0 a.val a.isLt⟩
        · exact ⟨d'.bw s, Or.inr ⟨s, ⟨hs, hst⟩, rfl⟩, rfl⟩
      · rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨s, ⟨hs, hst⟩, rfl⟩), rfl⟩
        · exact Or.inl ⟨a, ha, (shiftW_lt_n n j0 a.val a.isLt).symm⟩
        · exact Or.inr ⟨s, ⟨hs, hst⟩, rfl⟩
    rw [htop_eq, htopL, hout_eq_sh]
    apply orTree_shift hv'.2.2.2.2.2.2
    intro j' hj'
    have hj'lt := htop_lt j' hj'
    exact ⟨(hgate_C' j' hj'lt).1, hnot_R1_ins j' hj'lt (hR1_no_top j' hj')⟩

private lemma main_dir_fwd {n : ℕ} (K K' : SimpleGraph (Fin n))
    [DecidableRel K.Adj] [DecidableRel K'.Adj] (A : Finset (Fin n)) (l p : Fin n)
    (hK_tf : ∀ a b c : Fin n, K.Adj a b → K.Adj b c → K.Adj c a → False)
    (hA : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (hIH : ∀ C : Circuit, (IsMinimalCircuit n C ∧ circuitFun n C = graphFun K' A) ↔
      IsNestedCoverCircuit n K' A C)
    (C : Circuit) (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C = graphFun K A) :
    IsNestedCoverCircuit n K A C := by
  classical
  have hlp_adj : K.Adj l p := (hlp p).mpr rfl
  have hl_nep : l ≠ p := hlp_adj.ne
  have hl_notA : l ∉ A := fun h => hA l h p hlp_adj
  have hp_notA : p ∉ A := fun h => hA p h l hlp_adj.symm
  obtain ⟨q0, hq0l, hpq0⟩ := exists_neighbor_of_free_leaf hlp hfree
  have hpq0' : K'.Adj p q0 := (hK' p q0).mpr ⟨hpq0, hl_nep.symm, hq0l⟩
  obtain ⟨T0, hT0⟩ := exists_minCover K
  obtain ⟨C0, hC0f, hC0fun, hC0sz⟩ := exists_circuit_bound K A T0 hT0 ⟨l, p, hlp_adj⟩
  have hEdgeEq : K.edgeFinset.card = K'.edgeFinset.card + 1 := edgeFinset_card_K_eq hlp hK'
  have hdep : ∃ x : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update x l true) := by
    let x : Fin n → Bool := fun i => decide (i = p)
    refine ⟨x, ?_⟩
    rw [hfun, graphFun_update_l_false hA hlp hK', graphFun_update_l_true hA hlp hK']
    have hxp : x p = true := by simp [x]
    have hF0 : graphFun K' A x = false := by
      unfold graphFun
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      constructor
      · rintro ⟨a, ha, hxa⟩
        have : a = p := by simpa [x] using hxa
        exact hp_notA (this ▸ ha)
      · rintro ⟨u, v, huv, hxu, hxv⟩
        have hu : u = p := by simpa [x] using hxu
        have hv : v = p := by simpa [x] using hxv
        exact huv.ne (hu.trans hv.symm)
    rw [hxp, hF0]; decide
  have hnc : ∃ x y : Fin n → Bool, circuitFun n C (Function.update x l false) ≠
      circuitFun n C (Function.update y l false) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [hfun, graphFun_update_l_false hA hlp hK', graphFun_update_l_false hA hlp hK']
    have h0 : graphFun K' A (fun _ => false) = false := by unfold graphFun; simp
    have h1 : graphFun K' A (fun _ => true) = true := by
      unfold graphFun; simp; exact Or.inr ⟨p, q0, hpq0'⟩
    rw [h0, h1]; decide
  have htight : ∀ D : Circuit, FanInTwo D →
      circuitFun n D = (fun x => circuitFun n C (Function.update x l false)) →
      C.size ≤ D.size + 1 := by
    intro D hDf hDfun
    obtain ⟨Dmin, hDmin, hDmin_fun, hDmin_le⟩ := exists_minimal_of_circuit D hDf
    have hDmin_K' : circuitFun n Dmin = graphFun K' A := by
      rw [hDmin_fun, hDfun]; funext x; rw [hfun]; exact graphFun_update_l_false hA hlp hK' x
    obtain ⟨dD, hvD⟩ := (hIH Dmin).mp ⟨hDmin, hDmin_K'⟩
    have hDsz := ncc_size hvD
    have hT_eq : T0.card = dD.cover.card := minCover_card_eq hlp hfree hK' hT0 hvD.2.1
    have hCle : C.size ≤ C0.size := hmin.2 C0 hC0f (hC0fun.trans hfun.symm)
    omega
  obtain ⟨C', j0, w, hC'_min, hC'_fun, hC'_len, hj0, hw_lt, hw_nel, hj0_op, hj0_ins,
    hout_lt, hout_nel, hout_remap, hgate_rel⟩ :=
    tight_elim_structure hmin hdep hnc htight
  have hC'_K' : circuitFun n C' = graphFun K' A := by
    rw [hC'_fun]; funext x; rw [hfun]; exact graphFun_update_l_false hA hlp hK' x
  obtain ⟨d', hv'⟩ := (hIH C').mp ⟨hC'_min, hC'_K'⟩
  -- Gate correspondence for every gate j' of C'
  have hshG_lt : ∀ j' < C'.gates.length, shiftG j0 j' < C.gates.length := by
    intro j' hj'; unfold shiftG; split_ifs <;> omega
  have hgate_C' : ∀ j' < C'.gates.length,
      (gateAt C (shiftG j0 j')).op = (gateAt C' j').op ∧
      (gateAt C (shiftG j0 j')).inputs.length = 2 ∧
      (gateAt C' j').inputs = (gateAt C (shiftG j0 j')).inputs.map (remapW n j0 w) ∧
      ∀ i ∈ (gateAt C (shiftG j0 j')).inputs, i < n + shiftG j0 j' ∧ i ≠ l.val := by
    intro j' hj'
    have hrel := hgate_rel (shiftG j0 j') (hshG_lt j' hj') (shiftG_ne j0 j')
    have hun : (if shiftG j0 j' < j0 then shiftG j0 j' else shiftG j0 j' - 1) = j' :=
      unshiftG_shiftG j0 j'
    dsimp only at hrel; rw [hun] at hrel
    have hne_not : (gateAt C' j').op ≠ GateOp.not := by
      rcases valid_gate_op hv' j' hj' with h | h <;> rw [h] <;> intro e <;> cases e
    obtain ⟨hlen, hmap, hlt⟩ := hrel.2 hne_not
    exact ⟨hrel.1.symm, hlen, hmap, hlt⟩
  have hRB : ReadsBack n C := by
    intro j hj i hi
    by_cases hjj : j = j0
    · subst hjj
      rcases hj0_ins with h | h <;> rw [h] at hi <;> simp at hi <;>
        rcases hi with rfl | rfl <;> (try exact hw_lt) <;> have := l.isLt <;> omega
    · set j' := unshiftG j0 j
      have hj' : j' < C'.gates.length := by unfold j' unshiftG; split_ifs <;> omega
      have hsh : shiftG j0 j' = j := shiftG_unshiftG j0 j hjj
      rw [← hsh] at hi ⊢
      exact ((hgate_C' j' hj').2.2.2 i hi).1
  have hnot_R1_ins : ∀ j' < C'.gates.length, ¬ readsJ0 n j0 C j' →
      (gateAt C (shiftG j0 j')).inputs = (gateAt C' j').inputs.map (shiftW n j0) := by
    intro j' hj' hno
    rw [(hgate_C' j' hj').2.2.1, List.map_map]
    have hmap_eq : ((gateAt C (shiftG j0 j')).inputs).map (shiftW n j0 ∘ remapW n j0 w) =
        ((gateAt C (shiftG j0 j')).inputs).map id :=
      List.map_congr_left fun i hi =>
        shiftW_remapW_of_ne n j0 w i (fun e => hno (by unfold readsJ0; rw [← e]; exact hi))
    rw [hmap_eq, List.map_id]
  have hR1_mem_w : ∀ j' < C'.gates.length, readsJ0 n j0 C j' → w ∈ (gateAt C' j').inputs := by
    intro j' hj' hr
    rw [(hgate_C' j' hj').2.2.1]
    exact List.mem_map.mpr ⟨n + j0, hr, by simp [remapW]⟩
  have hR1_ins_cases : ∀ j' < C'.gates.length, readsJ0 n j0 C j' →
      ∀ a b, (gateAt C' j').inputs = [a, b] → a ≠ b →
        (a = w ∧ (gateAt C (shiftG j0 j')).inputs = [n + j0, shiftW n j0 b]) ∨
        (b = w ∧ (gateAt C (shiftG j0 j')).inputs = [shiftW n j0 a, n + j0]) := by
    intro j' hj' hr a b hab hne
    obtain ⟨_, hlen, hmap, _⟩ := hgate_C' j' hj'
    rcases hins : (gateAt C (shiftG j0 j')).inputs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩
    · simp [hins] at hlen
    · simp [hins] at hlen
    · rw [hins, hab] at hmap
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
      have hr' : n + j0 = x1 ∨ n + j0 = x2 := by simpa [readsJ0, hins] using hr
      rcases hr' with rfl | rfl
      · have ha : a = w := by simpa [remapW] using hmap.1
        have hx2_ne : x2 ≠ n + j0 := by
          intro e; subst e
          have hb : b = w := by simpa [remapW] using hmap.2
          exact hne (ha.trans hb.symm)
        have hx2 : x2 = shiftW n j0 b := by
          rcases remapW_eq_iff n j0 w x2 b hmap.2.symm with h | ⟨_, h⟩
          · exact h
          · exact absurd h hx2_ne
        exact Or.inl ⟨ha, by rw [hx2]⟩
      · have hb : b = w := by simpa [remapW] using hmap.2
        have hx1_ne : x1 ≠ n + j0 := by
          intro e; subst e
          have ha : a = w := by simpa [remapW] using hmap.1
          exact hne (ha.trans hb.symm)
        have hx1 : x1 = shiftW n j0 a := by
          rcases remapW_eq_iff n j0 w x1 a hmap.1.symm with h | ⟨_, h⟩
          · exact h
          · exact absurd h hx1_ne
        exact Or.inr ⟨hb, by rw [hx1]⟩
    · simp [hins] at hlen
  -- Evaluation lemmas for C
  have hwval_j0 : ∀ x : Fin n → Bool, wval C x (n + j0) = (x l || wval C x w) := by
    intro x
    rw [wval_gate C hRB x j0 hj0, hj0_op]
    rcases hj0_ins with h | h <;> rw [h] <;>
      simp [GateOp.eval, wval_input C x l.val l.isLt, Bool.or_comm]
  have hwval_ge : ∀ x : Fin n → Bool, ∀ a < n + C'.gates.length,
      wval C' x a = true → wval C x (shiftW n j0 a) = true := by
    intro x a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro halt hwa
      by_cases han : a < n
      · rw [shiftW_lt_n n j0 a han, wval_input C x a han]
        rw [wval_input C' x a han] at hwa; exact hwa
      · set j' := a - n
        have ha_eq : a = n + j' := by omega
        have hj' : j' < C'.gates.length := by omega
        obtain ⟨hopC, hlenC, hmapC, _⟩ := hgate_C' j' hj'
        rw [ha_eq, shiftW_add, wval_gate C hRB x (shiftG j0 j') (hshG_lt j' hj'), hopC]
        rw [ha_eq, wval_gate C' hv'.1 x j' hj'] at hwa
        have hstep : ∀ i ∈ (gateAt C (shiftG j0 j')).inputs,
            wval C' x (remapW n j0 w i) = true → wval C x i = true := by
          intro i hi hwr
          have hrem_mem : remapW n j0 w i ∈ (gateAt C' j').inputs := by
            rw [hmapC]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
          have hrem_lt : remapW n j0 w i < a := by rw [ha_eq]; exact hv'.1 j' hj' _ hrem_mem
          have hih := ih (remapW n j0 w i) hrem_lt (by omega) hwr
          rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with hi_eq | ⟨hw_eq, hi_eq⟩
          · rw [hi_eq]; exact hih
          · rw [hw_eq, show shiftW n j0 w = w by unfold shiftW; rw [if_pos hw_lt]] at hih
            rw [hi_eq, hwval_j0, hih]; simp
        rcases valid_gate_op hv' j' hj' with hop | hop
        · rw [hop] at hwa ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwa ⊢
          obtain ⟨r, hr, hwr⟩ := hwa
          rw [hmapC] at hr
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
          exact ⟨i, hi, hstep i hi hwr⟩
        · rw [hop] at hwa ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hwa ⊢
          intro i hi
          have hr : remapW n j0 w i ∈ (gateAt C' j').inputs := by
            rw [hmapC]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
          exact hstep i hi (hwa _ hr)
  have horTree_climb_C : ∀ {G L : Finset ℕ} {ρ : ℕ},
      (∀ j' ∈ G, j' < C'.gates.length) → IsOrTree n C' G L ρ →
      ∀ (x : Fin n → Bool), x l = true →
      ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) →
        wval C x (shiftW n j0 u) = true → wval C x (shiftW n j0 ρ) = true := by
    intro G L ρ hGlt htree x hxl u hu hwu
    by_cases huρ0 : u = ρ
    · exact huρ0 ▸ hwu
    have hub : u ≤ n + C'.gates.length := by
      rcases hu with huL | ⟨h1, h2⟩
      · have hr := (htree.2.1 u huL).2; rw [if_neg huρ0] at hr
        have hex : ∃ j' ∈ G, u ∈ (gateAt C' j').inputs := by
          by_contra hno; push Not at hno
          have h0 : readsIn C' G u = 0 :=
            Finset.sum_eq_zero (fun j' hj' => List.count_eq_zero.mpr (hno j' hj'))
          omega
        obtain ⟨j', hj', hmem⟩ := hex
        have := hv'.1 j' (hGlt j' hj') u hmem; have := hGlt j' hj'; omega
      · have := hGlt (u - n) h2; omega
    clear huρ0
    generalize hk : n + C'.gates.length - u = k
    induction k using Nat.strong_induction_on generalizing u with
    | _ k ih =>
      by_cases huρ : u = ρ
      · exact huρ ▸ hwu
      · have hrc : readsIn C' G u = 1 := by
          rcases hu with huL | ⟨h1, h2⟩
          · have := (htree.2.1 u huL).2; rw [if_neg huρ] at this; exact this
          · have hsub : n + (u - n) = u := by omega
            have := htree.2.2.1 (u - n) h2; rw [hsub, if_neg huρ] at this; exact this
        have hex : ∃ j' ∈ G, u ∈ (gateAt C' j').inputs := by
          by_contra hno; push Not at hno
          have h0 : readsIn C' G u = 0 :=
            Finset.sum_eq_zero (fun j' hj' => List.count_eq_zero.mpr (hno j' hj'))
          omega
        obtain ⟨j', hj', hmem⟩ := hex
        have hj'lt := hGlt j' hj'
        have hult : u < n + j' := hv'.1 j' hj'lt u hmem
        obtain ⟨hopC, _, hmapC, _⟩ := hgate_C' j' hj'lt
        rw [hmapC] at hmem
        obtain ⟨i, hi, hrem⟩ := List.mem_map.mp hmem
        have hwi : wval C x i = true := by
          rcases remapW_eq_iff n j0 w i u hrem with rfl | ⟨_, rfl⟩
          · exact hwu
          · rw [hwval_j0, hxl]; rfl
        have hval : wval C x (shiftW n j0 (n + j')) = true := by
          rw [shiftW_add, wval_gate C hRB x (shiftG j0 j') (hshG_lt j' hj'lt), hopC,
            (htree.1 j' hj').1]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨i, hi, hwi⟩
        exact ih (n + C'.gates.length - (n + j')) (by omega) (n + j')
          (Or.inr ⟨Nat.le_add_right _ _, by simpa using hj'⟩) hval (by omega) rfl
  have horTree_R1_C : ∀ {G L : Finset ℕ} {ρ : ℕ},
      (∀ j' ∈ G, j' < C'.gates.length) → IsOrTree n C' G L ρ →
      ∀ (x : Fin n → Bool), x l = true →
      (∃ j' ∈ G, readsJ0 n j0 C j') → wval C x (shiftW n j0 ρ) = true := by
    intro G L ρ hGlt htree x hxl ⟨j', hj', hR⟩
    have hj'lt := hGlt j' hj'
    obtain ⟨hopC, _, _, _⟩ := hgate_C' j' hj'lt
    have hval : wval C x (shiftW n j0 (n + j')) = true := by
      rw [shiftW_add, wval_gate C hRB x (shiftG j0 j') (hshG_lt j' hj'lt), hopC,
        (htree.1 j' hj').1]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      exact ⟨n + j0, hR, by rw [hwval_j0, hxl]; rfl⟩
    exact horTree_climb_C hGlt htree x hxl (n + j')
      (Or.inr ⟨Nat.le_add_right _ _, by simpa using hj'⟩) hval
  have htop_lt : ∀ j' ∈ topGates d' C', j' < C'.gates.length :=
    fun j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hg_lt : ∀ k t, ∀ j' ∈ gatesOf d' C' k t, j' < C'.gates.length :=
    fun _ _ j' hj' => Finset.mem_range.mp (Finset.mem_filter.mp hj').1
  have hbw_prop_C : ∀ (x : Fin n → Bool), x l = true → ∀ t ∈ d'.cover,
      wval C x (shiftW n j0 (d'.bw t)) = true →
      wval C x (shiftW n j0 (d'.zroot t)) = true →
      wval C x (shiftW n j0 C'.output) = true := by
    intro x hxl t ht hbt hzt
    have hub : d'.bw t ≤ n + C'.gates.length := by
      obtain ⟨jb, hjb, hbw, _⟩ := bw_spec hv' t ht; omega
    generalize hk : n + C'.gates.length - d'.bw t = k
    induction k using Nat.strong_induction_on generalizing t with
    | _ k ih =>
      cases htie : d'.tie t with
      | none =>
        refine horTree_climb_C htop_lt hv'.2.2.2.2.2.2 x hxl (d'.bw t) (Or.inl ?_) hbt
        simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        exact Or.inr ⟨t, ⟨ht, htie⟩, rfl⟩
      | some t' =>
        have hown : d'.owns t' t = true := (hv'.2.2.2.1 t t' htie).2
        have ht' : t' ∈ d'.cover := (hv'.2.2.1.1 t' t hown).2
        have hlam_eq : d'.lam t' t = d'.zroot t := by
          have hl := (hv'.2.2.2.2.2.1 t' ht').2.2.2 t hown
          unfold LamOK at hl; rw [if_pos ht] at hl; exact hl.2.2 htie
        have hor_t' : wval C x (shiftW n j0 (d'.oroot t')) = true := by
          refine horTree_climb_C (hg_lt _ _) (hv'.2.2.2.2.2.1 t' ht').2.2.1 x hxl (d'.lam t' t)
            (Or.inl ?_) (by rw [hlam_eq]; exact hzt)
          simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨t, hown, rfl⟩
        have hbt_in : d'.bw t ∈ zLeaves d' t' := by
          simp only [zLeaves, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
          exact Or.inr ⟨t, ⟨ht, htie⟩, rfl⟩
        have hzr_t' : wval C x (shiftW n j0 (d'.zroot t')) = true :=
          horTree_climb_C (hg_lt _ _) (hv'.2.2.2.2.2.1 t' ht').2.1 x hxl (d'.bw t) (Or.inl hbt_in) hbt
        obtain ⟨jb', hjb', hbw', _, hop', hin'⟩ := (hv'.2.2.2.2.2.1 t' ht').1
        obtain ⟨hopC, _, hmapC, _⟩ := hgate_C' jb' hjb'
        have hbt' : wval C x (shiftW n j0 (d'.bw t')) = true := by
          rw [hbw', shiftW_add, wval_gate C hRB x (shiftG j0 jb') (hshG_lt jb' hjb'), hopC, hop']
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro i hi
          have hrem : remapW n j0 w i ∈ (gateAt C' jb').inputs := by
            rw [hmapC]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
          have hmem : remapW n j0 w i = d'.zroot t' ∨ remapW n j0 w i = d'.oroot t' := by
            rcases hin' with h | h <;> rw [h] at hrem <;> simp at hrem <;> tauto
          rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with hi_eq | ⟨_, hi_eq⟩
          · rw [hi_eq]; rcases hmem with h1 | h1 <;> rw [h1]
            · exact hzr_t'
            · exact hor_t'
          · rw [hi_eq, hwval_j0, hxl]; rfl
        have hle_z : d'.bw t ≤ d'.zroot t' :=
          orTree_le_top hv'.1 (hg_lt _ _) (hv'.2.2.2.2.2.1 t' ht').2.1 (d'.bw t) (Or.inl hbt_in)
        have hlt_b : d'.zroot t' < d'.bw t' := by
          rw [hbw']
          exact hv'.1 jb' hjb' (d'.zroot t') (by rcases hin' with h | h <;> rw [h] <;> simp)
        exact ih (n + C'.gates.length - d'.bw t') (by omega) t' ht' hbt' hzr_t' (by omega) rfl
  -- Prove C.output ≠ n + j0!
  have hout_ne_j0 : C.output ≠ n + j0 := by
    intro heq
    let el : Fin n → Bool := fun i => decide (i = l)
    have hC1 : wval C el C.output = true := by
      rw [heq, hwval_j0]; simp [el]
    have hC2 : wval C el C.output = graphFun K A el := congrFun hfun el
    have hF0 : graphFun K A el = false := by
      unfold graphFun; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      constructor
      · rintro ⟨a, ha, hxa⟩
        have : a = l := by simpa [el] using hxa
        exact hl_notA (this ▸ ha)
      · rintro ⟨u, v, huv, hu, hv⟩
        have h1 : u = l := by simpa [el] using hu
        have h2 : v = l := by simpa [el] using hv
        exact huv.ne (h1.trans h2.symm)
    rw [hC1, hF0] at hC2; cases hC2
  have hout_eq_sh : C.output = shiftW n j0 C'.output := by
    rcases remapW_eq_iff n j0 w C.output C'.output hout_remap with h | ⟨_, h⟩
    · exact h
    · exact absurd h hout_ne_j0
  -- Prove ∃ j' < C'.gates.length, readsJ0 n j0 C j'!
  have hR1_nonempty : ∃ j' < C'.gates.length, readsJ0 n j0 C j' := by
    by_contra hno; push Not at hno
    obtain ⟨x, hx⟩ := hdep
    apply hx
    change (wiresFrom C.gates (List.ofFn (Function.update x l false))).getD C.output false =
      (wiresFrom C.gates (List.ofFn (Function.update x l true))).getD C.output false
    have hsplit : C.gates = C.gates.take j0 ++ gateAt C j0 :: C.gates.drop (j0 + 1) := by
      have htake := List.take_append_drop j0 C.gates
      have hdrop : C.gates.drop j0 = gateAt C j0 :: C.gates.drop (j0 + 1) := by
        rw [List.drop_eq_getElem_cons hj0]; congr 1; exact (List.getD_eq_getElem _ _ hj0).symm
      rw [← hdrop, htake]
    rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons]
    have hno_pre : ∀ g ∈ C.gates.take j0, ∀ i ∈ g.inputs, i ≠ l.val := by
      intro g hg i hi
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      have hk_j0 : k < j0 := by simp at hk; omega
      have hk_len : k < C'.gates.length := by omega
      have hshk : shiftG j0 k = k := by unfold shiftG; rw [if_pos hk_j0]
      have hgk : (C.gates.take j0)[k] = gateAt C (shiftG j0 k) := by
        rw [hshk, List.getElem_take]; exact (List.getD_eq_getElem _ _ (by omega)).symm
      rw [hgk] at hi
      exact ((hgate_C' k hk_len).2.2.2 i hi).2
    have hno_post : ∀ g ∈ C.gates.drop (j0 + 1), ∀ i ∈ g.inputs, i ≠ l.val ∧ i ≠ n + j0 := by
      intro g hg i hi
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      have hk_len : j0 + k < C'.gates.length := by simp at hk; omega
      have hshk : shiftG j0 (j0 + k) = j0 + 1 + k := by unfold shiftG; rw [if_neg (by omega)]; omega
      have hgk : (C.gates.drop (j0 + 1))[k] = gateAt C (shiftG j0 (j0 + k)) := by
        rw [hshk, List.getElem_drop]; exact (List.getD_eq_getElem _ _ (by omega)).symm
      rw [hgk] at hi
      refine ⟨((hgate_C' (j0 + k) hk_len).2.2.2 i hi).2,
        fun e => hno (j0 + k) hk_len (by unfold readsJ0; rw [← e]; exact hi)⟩
    have hpre_ag := wires_agree (C.gates.take j0) (fun i => i = l.val)
      (List.ofFn (Function.update x l false)) (List.ofFn (Function.update x l true))
      (by simp)
      (fun i hi => by
        by_cases hilt : i < n
        · have hne : (⟨i, hilt⟩ : Fin n) ≠ l := fun e => hi (congrArg Fin.val e)
          simp [List.getD, hilt, Function.update_of_ne hne]
        · simp [List.getD, hilt])
      (fun g hg i hi e => hno_pre g hg i hi e)
    have hlen1 : (wiresFrom (C.gates.take j0) (List.ofFn (Function.update x l false))).length = n + j0 := by
      rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0)]
    have hlen2 : (wiresFrom (C.gates.take j0) (List.ofFn (Function.update x l true))).length = n + j0 := by
      rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0)]
    refine wires_agree (C.gates.drop (j0 + 1)) (fun i => i = l.val ∨ i = n + j0) _ _
      (by simp [hlen1, hlen2]) (fun i hi => ?_)
      (fun g hg i hi h => by
        obtain ⟨h1, h2⟩ := hno_post g hg i hi
        rcases h with rfl | rfl; exact h1 rfl; exact h2 rfl)
      C.output (fun h => by rcases h with h | h; exact hout_nel h; exact hout_ne_j0 h)
    have h1 : i ≠ l.val := fun e => hi (Or.inl e)
    have h2 : i ≠ n + j0 := fun e => hi (Or.inr e)
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    exact hpre_ag i h1
  -- Pair evaluation helper: graphFun K A (pair l v) = decide (v = p) when v ∉ A
  have hpair_eval : ∀ v : Fin n, v ∉ A →
      graphFun K A (fun i => decide (i = l ∨ i = v)) = decide (v = p) := by
    intro v hvA
    apply Bool.eq_iff_iff.mpr
    unfold graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨a, ha, ha1 | ha2⟩ | ⟨a, b, hab, ha1 | ha2, hb1 | hb2⟩)
      · exact absurd (ha1 ▸ ha) hl_notA
      · exact absurd (ha2 ▸ ha) hvA
      · rw [ha1, hb1] at hab; exact absurd rfl hab.ne
      · rw [ha1, hb2] at hab; exact (hlp v).mp hab
      · rw [ha2, hb1] at hab; exact (hlp v).mp hab.symm
      · rw [ha2, hb2] at hab; exact absurd rfl hab.ne
    · intro hvp; rw [hvp]; exact Or.inr ⟨l, p, hlp_adj, Or.inl rfl, Or.inr rfl⟩
  have hcover_notA : ∀ t ∈ d'.cover, t ∉ A := by
    intro t ht htA
    obtain ⟨r, _, hown⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 ht
    exact hA t htA r ((hK' t r).mp (hv'.2.2.1.1 t r hown).1).1
  have howned_notA : ∀ t r : Fin n, d'.owns t r = true → r ∉ A := by
    intro t r hown hrA
    exact hA r hrA t ((hK' t r).mp (hv'.2.2.1.1 t r hown).1).1.symm
  -- Helper: x_r = true implies oroot t = true in C
  have horoot_of_xr : ∀ (x : Fin n → Bool) (t r : Fin n), t ∈ d'.cover →
      d'.owns t r = true → x r = true → wval C x (shiftW n j0 (d'.oroot t)) = true := by
    intro x t r ht hown hxr
    have hlam_val : wval C' x (d'.lam t r) = true := by
      have hlam := (hv'.2.2.2.2.2.1 t ht).2.2.2 r hown
      unfold LamOK at hlam
      split_ifs at hlam with hr
      · exact centred_eval hv' hr x hxr (d'.lam t r) hlam.2.1 hlam.1
      · rw [hlam, wval_input C' x r.val r.isLt]; exact hxr
    have hor' : wval C' x (d'.oroot t) = true := by
      refine orTree_eval_up hv'.1 (hg_lt _ _) (hv'.2.2.2.2.2.1 t ht).2.2.1 x (d'.lam t r)
        (Or.inl ?_) hlam_val
      simp only [oLeaves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨r, hown, rfl⟩
    have hor_lt : d'.oroot t < n + C'.gates.length := by
      obtain ⟨jb, hjb, _, _, _, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
      have := hv'.1 jb hjb (d'.oroot t) (by rcases hin with h | h <;> rw [h] <;> simp)
      omega
    exact hwval_ge x (d'.oroot t) hor_lt hor'
  have hzroot_of_xt : ∀ (x : Fin n → Bool) (t : Fin n), t ∈ d'.cover → x t = true →
      wval C x (shiftW n j0 (d'.zroot t)) = true := by
    intro x t ht hxt
    have hzr' : wval C' x (d'.zroot t) = true :=
      orTree_eval_up hv'.1 (hg_lt _ _) (hv'.2.2.2.2.2.1 t ht).2.1 x t.val
        (Or.inl (Finset.mem_insert_self _ _)) (by rw [wval_input C' x t.val t.isLt]; exact hxt)
    have hzr_lt : d'.zroot t < n + C'.gates.length := by
      obtain ⟨jb, hjb, _, _, _, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
      have := hv'.1 jb hjb (d'.zroot t) (by rcases hin with h | h <;> rw [h] <;> simp)
      omega
    exact hwval_ge x (d'.zroot t) hzr_lt hzr'
  -- Classification of readsJ0!
  -- 1. No TOP gate in readsJ0
  have hR1_no_top : ∀ j' ∈ topGates d' C', ¬ readsJ0 n j0 C j' := by
    intro j' hj' hR
    let el : Fin n → Bool := fun i => decide (i = l)
    have hval := horTree_R1_C htop_lt hv'.2.2.2.2.2.2 el (by simp [el]) ⟨j', hj', hR⟩
    rw [← hout_eq_sh] at hval
    have heq : wval C el C.output = graphFun K A el := congrFun hfun el
    have hF0 : graphFun K A el = false := by
      unfold graphFun; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      constructor
      · rintro ⟨a, ha, hxa⟩; exact hl_notA ((by simpa [el] using hxa : a = l) ▸ ha)
      · rintro ⟨u, v, huv, hu, hv⟩
        exact huv.ne ((by simpa [el] using hu : u = l).trans (by simpa [el] using hv : v = l).symm)
    rw [hval, hF0] at heq; cases heq
  -- 2. No Z gate in readsJ0
  have hR1_no_z : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.z t.val, ¬ readsJ0 n j0 C j' := by
    intro t ht j' hj' hR
    have hown_p : ∀ r, d'.owns t r = true → r = p := by
      intro r hown
      let x : Fin n → Bool := fun i => decide (i = l ∨ i = r)
      have hxl : x l = true := by simp [x]
      have hxr : x r = true := by simp [x]
      have hzr := horTree_R1_C (hg_lt _ _) (hv'.2.2.2.2.2.1 t ht).2.1 x hxl ⟨j', hj', hR⟩
      have hor := horoot_of_xr x t r ht hown hxr
      obtain ⟨jb, hjb, hbw, _, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
      obtain ⟨hopC, _, hmapC, _⟩ := hgate_C' jb hjb
      have hbt : wval C x (shiftW n j0 (d'.bw t)) = true := by
        rw [hbw, shiftW_add, wval_gate C hRB x (shiftG j0 jb) (hshG_lt jb hjb), hopC, hop]
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        intro i hi
        have hrem : remapW n j0 w i ∈ (gateAt C' jb).inputs := by
          rw [hmapC]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
        have hmem : remapW n j0 w i = d'.zroot t ∨ remapW n j0 w i = d'.oroot t := by
          rcases hin with h | h <;> rw [h] at hrem <;> simp at hrem <;> tauto
        rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with hi_eq | ⟨_, hi_eq⟩
        · rw [hi_eq]; rcases hmem with h1 | h1 <;> rw [h1]; exact hzr; exact hor
        · rw [hi_eq, hwval_j0, hxl]; rfl
      have hout := hbw_prop_C x hxl t ht hbt hzr
      rw [← hout_eq_sh] at hout
      have hev : wval C x C.output = decide (r = p) :=
        (congrFun hfun x).trans (hpair_eval r (howned_notA t r hown))
      rw [hout] at hev
      exact decide_eq_true_eq.mp hev.symm
    obtain ⟨r0, hr0_not, hr0_own⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 ht
    have hp_not : p ∉ d'.cover := hown_p r0 hr0_own ▸ hr0_not
    have hcard_z := tree_card n C' _ _ _ (hv'.2.2.2.2.2.1 t ht).2.1
    rw [zLeaves_card hv' t] at hcard_z
    have hpos : 0 < (gatesOf d' C' Kind.z t.val).card := Finset.card_pos.mpr ⟨j', hj'⟩
    have htie_ne : (d'.cover.filter (fun s => d'.tie s = some t)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨s, hs⟩ := htie_ne
    obtain ⟨hs_cov, hs_tie⟩ := Finset.mem_filter.mp hs
    have hs_own : d'.owns t s = true := (hv'.2.2.2.1 s t hs_tie).2
    exact hp_not (hown_p s hs_own ▸ hs_cov)
  -- 3. Any O gate in readsJ0 must be for p
  have hR1_o_eq_p : ∀ t ∈ d'.cover, ∀ j' ∈ gatesOf d' C' Kind.o t.val, readsJ0 n j0 C j' → t = p := by
    intro t ht j' hj' hR
    let x : Fin n → Bool := fun i => decide (i = l ∨ i = t)
    have hxl : x l = true := by simp [x]
    have hxt : x t = true := by simp [x]
    have hzr := hzroot_of_xt x t ht hxt
    have hor := horTree_R1_C (hg_lt _ _) (hv'.2.2.2.2.2.1 t ht).2.2.1 x hxl ⟨j', hj', hR⟩
    obtain ⟨jb, hjb, hbw, _, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
    obtain ⟨hopC, _, hmapC, _⟩ := hgate_C' jb hjb
    have hbt : wval C x (shiftW n j0 (d'.bw t)) = true := by
      rw [hbw, shiftW_add, wval_gate C hRB x (shiftG j0 jb) (hshG_lt jb hjb), hopC, hop]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro i hi
      have hrem : remapW n j0 w i ∈ (gateAt C' jb).inputs := by
        rw [hmapC]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
      have hmem : remapW n j0 w i = d'.zroot t ∨ remapW n j0 w i = d'.oroot t := by
        rcases hin with h | h <;> rw [h] at hrem <;> simp at hrem <;> tauto
      rcases remapW_eq_iff n j0 w i (remapW n j0 w i) rfl with hi_eq | ⟨_, hi_eq⟩
      · rw [hi_eq]; rcases hmem with h1 | h1 <;> rw [h1]; exact hzr; exact hor
      · rw [hi_eq, hwval_j0, hxl]; rfl
    have hout := hbw_prop_C x hxl t ht hbt hzr
    rw [← hout_eq_sh] at hout
    have hev : wval C x C.output = decide (t = p) :=
      (congrFun hfun x).trans (hpair_eval t (hcover_notA t ht))
    rw [hout] at hev
    exact decide_eq_true_eq.mp hev.symm
  -- 4. Any B gate in readsJ0 with w = d'.oroot t must have t = p
  have hR1_b_oroot_eq_p : ∀ t ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw t = n + jb → readsJ0 n j0 C jb → w = d'.oroot t → t = p := by
    intro t ht jb hjb hbw hR hwo
    let x : Fin n → Bool := fun i => decide (i = l ∨ i = t)
    have hxl : x l = true := by simp [x]
    have hxt : x t = true := by simp [x]
    have hzr := hzroot_of_xt x t ht hxt
    obtain ⟨jb1, hjb1, hbw1, _, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
    have hjj : jb = jb1 := by omega
    subst hjj
    obtain ⟨hopC, _, _, _⟩ := hgate_C' jb hjb
    have hzne : d'.zroot t ≠ d'.oroot t := zroot_ne_oroot hv' ht
    have hbt : wval C x (shiftW n j0 (d'.bw t)) = true := by
      rw [hbw, shiftW_add, wval_gate C hRB x (shiftG j0 jb) (hshG_lt jb hjb), hopC, hop]
      rcases hin with h | h
      · rcases hR1_ins_cases jb hjb hR (d'.zroot t) (d'.oroot t) h hzne with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd (h1.trans hwo) hzne
        · rw [h2]; simp [GateOp.eval, hzr, hwval_j0, hxl]
      · rcases hR1_ins_cases jb hjb hR (d'.oroot t) (d'.zroot t) h hzne.symm with ⟨_, h2⟩ | ⟨h1, _⟩
        · rw [h2]; simp [GateOp.eval, hzr, hwval_j0, hxl]
        · exact absurd (h1.trans hwo) hzne
    have hout := hbw_prop_C x hxl t ht hbt hzr
    rw [← hout_eq_sh] at hout
    have hev : wval C x C.output = decide (t = p) :=
      (congrFun hfun x).trans (hpair_eval t (hcover_notA t ht))
    rw [hout] at hev
    exact decide_eq_true_eq.mp hev.symm
  -- 5. Any B gate in readsJ0 with w = d'.zroot t forces d'.tie t = none, p ∉ d'.cover, owns t r ↔ r = p!
  have hR1_b_zroot_spec : ∀ t ∈ d'.cover, ∀ jb < C'.gates.length,
      d'.bw t = n + jb → readsJ0 n j0 C jb → w = d'.zroot t →
      d'.tie t = none ∧ p ∉ d'.cover ∧ ∀ r, d'.owns t r = true ↔ r = p := by
    intro t ht jb hjb hbw hR hwz
    obtain ⟨jb1, hjb1, hbw1, _, hop, hin⟩ := (hv'.2.2.2.2.2.1 t ht).1
    have hjj : jb = jb1 := by omega
    subst hjj
    obtain ⟨hopC, _, _, _⟩ := hgate_C' jb hjb
    have hzne : d'.zroot t ≠ d'.oroot t := zroot_ne_oroot hv' ht
    have hbt_of_oroot : ∀ x : Fin n → Bool, x l = true →
        wval C x (shiftW n j0 (d'.oroot t)) = true → wval C x (shiftW n j0 (d'.bw t)) = true := by
      intro x hxl hor
      rw [hbw, shiftW_add, wval_gate C hRB x (shiftG j0 jb) (hshG_lt jb hjb), hopC, hop]
      rcases hin with h | h
      · rcases hR1_ins_cases jb hjb hR (d'.zroot t) (d'.oroot t) h hzne with ⟨_, h2⟩ | ⟨h1, _⟩
        · rw [h2]; simp [GateOp.eval, hor, hwval_j0, hxl]
        · exact absurd (h1.trans hwz).symm hzne
      · rcases hR1_ins_cases jb hjb hR (d'.oroot t) (d'.zroot t) h hzne.symm with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd (h1.trans hwz).symm hzne
        · rw [h2]; simp [GateOp.eval, hor, hwval_j0, hxl]
    have htie_none : d'.tie t = none :=
      fwd_b_zroot_tie_none hK_tf hA hlp hK' hfun hC'_len hj0 hRB hv' hgate_C' hnot_R1_ins
        hR1_mem_w hR1_ins_cases hwval_j0 horTree_climb_C hbw_prop_C hout_eq_sh hpair_eval
        horoot_of_xr hR1_no_top hR1_no_z hR1_o_eq_p hR1_b_oroot_eq_p ht hjb hbw hR hwz hbt_of_oroot
    have hown_imp : ∀ r, d'.owns t r = true → r = p := by
      intro r hown
      let x : Fin n → Bool := fun i => decide (i = l ∨ i = r)
      have hxl : x l = true := by simp [x]
      have hxr : x r = true := by simp [x]
      have hbt := hbt_of_oroot x hxl (horoot_of_xr x t r ht hown hxr)
      have hout : wval C x (shiftW n j0 C'.output) = true := by
        refine horTree_climb_C htop_lt hv'.2.2.2.2.2.2 x hxl (d'.bw t) (Or.inl ?_) hbt
        simp only [topLeaves, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        exact Or.inr ⟨t, ⟨ht, htie_none⟩, rfl⟩
      rw [← hout_eq_sh] at hout
      have hev : wval C x C.output = decide (r = p) :=
        (congrFun hfun x).trans (hpair_eval r (howned_notA t r hown))
      rw [hout] at hev
      exact decide_eq_true_eq.mp hev.symm
    obtain ⟨r0, hr0_not, hr0_own⟩ := exists_owned_not_in_cover hv'.2.1 hv'.2.2.1 ht
    have hr0_eq : r0 = p := hown_imp r0 hr0_own
    subst hr0_eq
    exact ⟨htie_none, hr0_not, fun r => ⟨hown_imp r, fun h => h ▸ hr0_own⟩⟩
  -- NOW SPLIT INTO THE TWO CASES: Branch B (cover-flip) vs Branch A (splice into O_p)!
  by_cases hflip : ∃ v ∈ d'.cover, ∃ jb < C'.gates.length,
      d'.bw v = n + jb ∧ readsJ0 n j0 C jb ∧ w = d'.zroot v
  · obtain ⟨v, hv_cov, jbv, hjbv, hbwv, hRv, hwv⟩ := hflip
    obtain ⟨htie_v, hp_not, hown_v⟩ := hR1_b_zroot_spec v hv_cov jbv hjbv hbwv hRv hwv
    exact fwd_branch_flip hlp hfree hK' hT0 hC'_len hj0 hw_nel hj0_op hj0_ins hRB hv' hgate_C'
      hnot_R1_ins hR1_mem_w hR1_ins_cases hout_eq_sh hR1_no_top hR1_no_z hR1_o_eq_p
      hR1_b_oroot_eq_p hv_cov hjbv hbwv hRv hwv htie_v hp_not hown_v
  · push Not at hflip
    exact fwd_branch_splice hlp hfree hK' hT0 hC'_len hj0 hw_lt hw_nel hj0_op hj0_ins hRB hv'
      hgate_C' hnot_R1_ins hR1_mem_w hR1_ins_cases hout_eq_sh hR1_nonempty hR1_no_top hR1_no_z
      hR1_o_eq_p hR1_b_oroot_eq_p hflip

private lemma main_dir_bwd {n : ℕ} (K K' : SimpleGraph (Fin n))
    [DecidableRel K.Adj] [DecidableRel K'.Adj] (A : Finset (Fin n)) (l p : Fin n)
    (hA : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (hlp : ∀ v : Fin n, K.Adj l v ↔ v = p)
    (hfree : ∀ T : Finset (Fin n), IsMinCover K T → l ∉ T)
    (hK' : ∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l)
    (hIH : ∀ C : Circuit, (IsMinimalCircuit n C ∧ circuitFun n C = graphFun K' A) ↔
      IsNestedCoverCircuit n K' A C)
    (C : Circuit) (hC : IsNestedCoverCircuit n K A C) :
    IsMinimalCircuit n C ∧ circuitFun n C = graphFun K A := by
  classical
  obtain ⟨d, hv⟩ := hC
  have hfun : circuitFun n C = graphFun K A := valid_eval hv
  have hfan : FanInTwo C := valid_fanInTwo hv
  have hsz := ncc_size hv
  have hlp_adj : K.Adj l p := (hlp p).mpr rfl
  have hl_nep : l ≠ p := hlp_adj.ne
  have hp_notA : p ∉ A := fun h => hA p h l hlp_adj.symm
  obtain ⟨q0, hq0l, hpq0⟩ := exists_neighbor_of_free_leaf hlp hfree
  have hpq0' : K'.Adj p q0 := (hK' p q0).mpr ⟨hpq0, hl_nep.symm, hq0l⟩
  have hEdgeEq : K.edgeFinset.card = K'.edgeFinset.card + 1 := edgeFinset_card_K_eq hlp hK'
  refine ⟨⟨hfan, fun D hDf hDfun => ?_⟩, hfun⟩
  have hDK : circuitFun n D = graphFun K A := hDfun.trans hfun
  have hdep : ∃ x : Fin n → Bool, circuitFun n D (Function.update x l false) ≠
      circuitFun n D (Function.update x l true) := by
    let x : Fin n → Bool := fun i => decide (i = p)
    refine ⟨x, ?_⟩
    rw [hDK, graphFun_update_l_false hA hlp hK', graphFun_update_l_true hA hlp hK']
    have hxp : x p = true := by simp [x]
    have hF0 : graphFun K' A x = false := by
      unfold graphFun; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      constructor
      · rintro ⟨a, ha, hxa⟩; exact hp_notA ((by simpa [x] using hxa : a = p) ▸ ha)
      · rintro ⟨u, v, huv, hxu, hxv⟩
        exact huv.ne ((by simpa [x] using hxu : u = p).trans (by simpa [x] using hxv : v = p).symm)
    rw [hxp, hF0]; decide
  have hnc : ∃ x y : Fin n → Bool, circuitFun n D (Function.update x l false) ≠
      circuitFun n D (Function.update y l false) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [hDK, graphFun_update_l_false hA hlp hK', graphFun_update_l_false hA hlp hK']
    have h0 : graphFun K' A (fun _ => false) = false := by unfold graphFun; simp
    have h1 : graphFun K' A (fun _ => true) = true := by
      unfold graphFun; simp; exact Or.inr ⟨p, q0, hpq0'⟩
    rw [h0, h1]; decide
  obtain ⟨D', hD'f, hD'fun, hD'le⟩ := elim_one_at hDf hdep hnc
  obtain ⟨Dmin, hDmin, hDmin_fun, hDmin_le⟩ := exists_minimal_of_circuit D' hD'f
  have hDmin_K' : circuitFun n Dmin = graphFun K' A := by
    rw [hDmin_fun, hD'fun]; funext x; rw [hDK]; exact graphFun_update_l_false hA hlp hK' x
  obtain ⟨dD, hvD⟩ := (hIH Dmin).mp ⟨hDmin, hDmin_K'⟩
  have hDsz := ncc_size hvD
  have hTeq : d.cover.card = dD.cover.card := minCover_card_eq hlp hfree hK' hv.2.1 hvD.2.1
  omega

end PEqualNP.Outside.L_meta_539_aux

theorem PEqualNP.Outside.L_meta_539 : ∀ (n : ℕ) (K K' : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K'.Adj] (A : Finset (Fin n)) (l p : Fin n), ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k → Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj) → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (∀ v : Fin n, K.Adj l v ↔ v = p) → (∀ T : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover K T → l ∉ T) → (∀ u v : Fin n, K'.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K' A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K' A C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C) := by
  intro n K K' _ _ A l p k m H hk hemb hA hlp hfree hK' hIH C
  exact ⟨fun ⟨hmin, hfun⟩ => PEqualNP.Outside.L_meta_539_aux.main_dir_fwd K K' A l p
      (PEqualNP.Outside.L_meta_539_aux.triangle_free_of_subdiv hk hemb) hA hlp hfree hK' hIH C hmin hfun,
    fun hC => PEqualNP.Outside.L_meta_539_aux.main_dir_bwd K K' A l p hA hlp hfree hK' hIH C hC⟩


