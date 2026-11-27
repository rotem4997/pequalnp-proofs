import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_535_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- The length of a list is the sum of the multiplicities of its entries over any set holding them.
theorem length_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    l.length = ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := h a (by simp)
    have ih' := ih (fun i hi => h i (by simp [hi]))
    simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib]
    rw [← ih']
    simp [ha]

-- A binary OR tree has one gate less than leaves.
theorem tree_card (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ) (h : IsOrTree n C G L ρ) :
    L.card = G.card + 1 := by
  obtain ⟨hg, hl, hgg, hroot⟩ := h
  by_cases hG : G = ∅
  · rw [if_pos hG] at hroot
    rw [hroot, hG]
    simp
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
    have hlen : ∀ j ∈ G, (gateAt C j).inputs.length
        = ∑ w ∈ L ∪ G.image (fun k => n + k), (gateAt C j).inputs.count w := by
      intro j hj
      apply length_eq_sum_count
      intro i hi
      rcases (hg j hj).2.2 i hi with h1 | ⟨h1, h2⟩
      · exact Finset.mem_union_left _ h1
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i - n, h2, by omega⟩
    have h1 : ∑ j ∈ G, (gateAt C j).inputs.length
        = ∑ w ∈ L ∪ G.image (fun k => n + k), readsIn C G w := by
      rw [Finset.sum_congr rfl hlen, Finset.sum_comm]
      rfl
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
      rw [Finset.sum_congr rfl e]
      rw [← Finset.add_sum_erase G _ hj0]
      rw [Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
      simp only [if_true, Finset.sum_const, smul_eq_mul, Nat.mul_one, Nat.zero_add]
      have := Finset.card_erase_add_one hj0
      omega
    rw [h1, Finset.sum_union hdisj, h2] at hsum
    omega

-- The facts used about a valid labelling.
theorem bw_spec {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) (ht : t ∈ d.cover) :
    ∃ j < C.gates.length, d.bw t = n + j ∧ d.role j = (Kind.b, t.val) := by
  obtain ⟨j, hj, h1, h2, _⟩ := (hv.2.2.2.2.2.1 t ht).1
  exact ⟨j, hj, h1, h2⟩

theorem bw_injOn {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (S : Finset (Fin n)) (hS : S ⊆ d.cover) :
    Set.InjOn d.bw (S : Set (Fin n)) := by
  intro s hs t ht h
  obtain ⟨j, _, h1, h2⟩ := bw_spec hv s (hS hs)
  obtain ⟨j', _, h1', h2'⟩ := bw_spec hv t (hS ht)
  have hj : j = j' := by omega
  subst hj
  rw [h2] at h2'
  exact Fin.ext (Prod.ext_iff.mp h2').2

theorem zLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) :
    (zLeaves d t).card = (d.cover.filter (fun s => d.tie s = some t)).card + 1 := by
  unfold zLeaves
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn
    (bw_injOn hv _ (Finset.filter_subset _ _))]
  intro hin
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hin
  obtain ⟨j, _, h1, _⟩ := bw_spec hv s (Finset.mem_filter.mp hs).1
  have := t.isLt
  omega

theorem topLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
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
  have := a.isLt
  omega

theorem oLeaves_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
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
  have hlt := r.isLt
  have hlt' := r'.isLt
  rcases key r hr1 with h1 | ⟨j, h1, h2⟩ <;> rcases key r' hr1' with h1' | ⟨j', h1', h2'⟩
  · exact Fin.ext (by omega)
  · omega
  · omega
  · have hj : j = j' := by omega
    subst hj
    rw [h2] at h2'
    exact Fin.ext (Prod.ext_iff.mp h2').2

-- The term gate of a cover vertex is the only gate with its role.
theorem bGates_card {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
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
    · rw [hr] at htop
      simp at htop
    · rw [hr] at e1 e2
      have : t' = t := Fin.ext e1.symm
      subst this
      have := e2 rfl
      omega
  · rintro rfl
    exact ⟨hj, h2⟩

-- Every gate is a gate of TOP or has one of three roles at a cover vertex.
theorem gates_split {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) :
    C.gates.length = (topGates d C).card + ∑ t ∈ d.cover,
      ((gatesOf d C Kind.z t.val).card + (gatesOf d C Kind.o t.val).card
        + (gatesOf d C Kind.b t.val).card) := by
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
    congr 1
    ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hj, _⟩, hr⟩
      exact ⟨hj, hr⟩
    · rintro ⟨hj, hr⟩
      refine ⟨⟨hj, ?_⟩, hr⟩
      rw [hr]
      have hk1 := (Finset.mem_product.mp hk).1
      intro e
      simp only at e
      rw [e] at hk1
      simp at hk1
  rw [Finset.sum_congr rfl hfib, Finset.sum_product] at h1
  dsimp only at h1
  have h2 : ∑ k ∈ ({Kind.z, Kind.o, Kind.b} : Finset Kind), ∑ v ∈ d.cover.image Fin.val,
      (gatesOf d C k v).card
      = ∑ t ∈ d.cover, ((gatesOf d C Kind.z t.val).card + (gatesOf d C Kind.o t.val).card
        + (gatesOf d C Kind.b t.val).card) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Finset.sum_image (fun a _ b _ h => Fin.val_injective h)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    omega
  have h3 : ((Finset.range C.gates.length).filter (fun j => (d.role j).1 = Kind.top)).card
      = (topGates d C).card := rfl
  omega

-- Tied and untied cover vertices together are the cover.
theorem tie_split {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} (hv : Valid n K A C d) :
    d.cover.card = (d.cover.filter (fun t => d.tie t = none)).card
      + ∑ t ∈ d.cover, (d.cover.filter (fun s => d.tie s = some t)).card := by
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

-- Each edge has one owner, so the owned pairs count the edges.
theorem owned_card {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj] {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
    ∑ t ∈ d.cover, (Finset.univ.filter (fun r => d.owns t r = true)).card
      = K.edgeFinset.card := by
  have hown := hv.2.2.1
  have hP : ∀ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2 = true)),
      p.1 ∈ d.cover := by
    intro p hp
    exact (hown.1 p.1 p.2 (Finset.mem_filter.mp hp).2).2
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
    · intro a _ b _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨u, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨h1, h2⟩ := hp
      subst h2
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
    · exfalso
      simp only at h1 h2
      subst h1
      subst h2
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

end PEqualNP.Outside.L_meta_535_aux

open PEqualNP.Outside.L_meta_535_aux PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_535 : ∀ (n t : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C → (∃ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) ∧ S.card = t) → (∀ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) → t ≤ S.card) → C.size + 1 = A.card + K.edgeFinset.card + t := by
  intro n t K _ A C hC hex hmin
  obtain ⟨d, hv⟩ := hC
  obtain ⟨S, hS, hSt⟩ := hex
  have hcov : d.cover.card = t := by
    have h1 := hv.2.1.2 S hS
    have h2 := hmin d.cover hv.2.1.1
    omega
  have hsize : C.size = C.gates.length := rfl
  have hsplit := gates_split hv
  have htop := tree_card n C _ _ _ hv.2.2.2.2.2.2
  rw [topLeaves_card hv] at htop
  have hper : ∀ u ∈ d.cover, (gatesOf d C Kind.z u.val).card + (gatesOf d C Kind.o u.val).card
      + (gatesOf d C Kind.b u.val).card
      = (d.cover.filter (fun s => d.tie s = some u)).card
        + (Finset.univ.filter (fun r => d.owns u r = true)).card := by
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
