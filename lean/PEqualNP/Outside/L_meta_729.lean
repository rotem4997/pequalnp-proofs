import PEqualNP.Defs
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_729_aux

def Walk {n : ℕ} (D : Fin n → Fin n → Prop) (S : Finset (Fin n)) (m : ℕ) (u v : Fin n) : Prop :=
  ∃ p : ℕ → Fin n, p 0 = u ∧ p m = v ∧
    (∀ i, i ≤ m → p i ∈ S) ∧ (∀ i, i < m → D (p i) (p (i + 1)))

def Reach {n : ℕ} (D : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ m, Walk D S m u v

def EvenReach {n : ℕ} (D : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ k, Walk D S (2 * k) u v

lemma walk_refl {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ S) : Walk D S 0 u u := by
  refine ⟨fun _ => u, rfl, rfl, ?_, ?_⟩
  · intro i _
    exact hu
  · intro i hi
    omega

lemma walk_single {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ S) (hv : v ∈ S) (huv : D u v) : Walk D S 1 u v := by
  refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_, ?_⟩
  · intro i _
    by_cases h : i = 0
    · simp [h, hu]
    · simp [h, hv]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using huv

lemma walk_append {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)}
    {m1 m2 : ℕ} {u v w : Fin n}
    (h1 : Walk D S m1 u v) (h2 : Walk D S m2 v w) : Walk D S (m1 + m2) u w := by
  rcases h1 with ⟨p, hp0, hpm, hpS, hpD⟩
  rcases h2 with ⟨q, hq0, hqm, hqS, hqD⟩
  refine ⟨fun i => if i ≤ m1 then p i else q (i - m1), ?_, ?_, ?_, ?_⟩
  · simp [hp0]
  · by_cases h : m1 + m2 ≤ m1
    · have hm2 : m2 = 0 := by omega
      subst hm2
      simp [hpm, hq0.symm.trans hqm]
    · simp [h, hqm]
  · intro i hi
    by_cases h : i ≤ m1
    · simp [h, hpS i h]
    · simp [h]
      exact hqS (i - m1) (by omega)
  · intro i hi
    by_cases hlt : i < m1
    · have hle1 : i ≤ m1 := by omega
      have hle2 : i + 1 ≤ m1 := by omega
      simp [hle1, hle2, hpD i hlt]
    · by_cases heq : i = m1
      · have hle1 : i ≤ m1 := by omega
        have hnot : ¬ (i + 1 ≤ m1) := by omega
        have hm2 : 0 < m2 := by omega
        have hsub : i + 1 - m1 = 1 := by omega
        simp [hle1, hnot, hsub, heq, hpm, ← hq0]
        exact hqD 0 hm2
      · have hnot1 : ¬ (i ≤ m1) := by omega
        have hnot2 : ¬ (i + 1 ≤ m1) := by omega
        have hsub : i + 1 - m1 = (i - m1) + 1 := by omega
        have hlt2 : i - m1 < m2 := by omega
        simp [hnot1, hnot2, hsub]
        exact hqD (i - m1) hlt2

lemma reach_refl {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ S) : Reach D S u u :=
  ⟨0, walk_refl hu⟩

lemma reach_trans {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u v w : Fin n}
    (h1 : Reach D S u v) (h2 : Reach D S v w) : Reach D S u w := by
  rcases h1 with ⟨m1, hm1⟩
  rcases h2 with ⟨m2, hm2⟩
  exact ⟨m1 + m2, walk_append hm1 hm2⟩

lemma reach_step {n : ℕ} {D : Fin n → Fin n → Prop} {S : Finset (Fin n)} {u v w : Fin n}
    (h1 : Reach D S u v) (hv : v ∈ S) (hw : w ∈ S) (hvw : D v w) : Reach D S u w :=
  reach_trans h1 ⟨1, walk_single hv hw hvw⟩

lemma finset_exists_min {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hne : S.Nonempty) : ∃ r ∈ S, ∀ u ∈ S, f r ≤ f u := by
  induction S using Finset.induction_on with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rcases ih hs with ⟨r, hr, hmin⟩
      by_cases hfa : f a ≤ f r
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hus
        · exact le_refl _
        · exact le_trans hfa (hmin u hus)
      · refine ⟨r, Finset.mem_insert_of_mem hr, ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hus
        · omega
        · exact hmin u hus
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_singleton_self a, ?_⟩
      intro u hu
      rw [Finset.mem_singleton.mp hu]

lemma no_odd_closed_in_S {n : ℕ} {D : Fin n → Fin n → Prop}
    (hodd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1)))
    {S : Finset (Fin n)} {m : ℕ} {u : Fin n}
    (hw : Walk D S m u u) : m % 2 = 0 := by
  by_contra hne
  have hmod : m % 2 = 1 := by omega
  have hm : m = 2 * (m / 2) + 1 := by omega
  rcases hw with ⟨p, hp0, hpm, _, hpD⟩
  apply hodd
  refine ⟨m / 2, p, ?_, ?_⟩
  · rw [← hm, hpm, hp0]
  · intro i hi
    exact hpD i (by omega)

lemma exists_kernel_finset {n : ℕ} (D : Fin n → Fin n → Prop)
    (hodd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card ≤ k →
      ∃ K : Finset (Fin n), K ⊆ S ∧
        (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
        (∀ v ∈ S, v ∉ K → ∃ a ∈ K, D v a) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S hcard
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    subst hS
    refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro v hv; exact absurd hv (Finset.notMem_empty v)
  | succ k ih =>
    intro S hcard
    by_cases hne : S.Nonempty
    · let R : Fin n → Finset (Fin n) := fun u => S.filter (fun v => Reach D S u v)
      rcases finset_exists_min S (fun u => (R u).card) hne with ⟨r, hrS, hrmin⟩
      let C : Finset (Fin n) := R r
      have hrC : r ∈ C := Finset.mem_filter.mpr ⟨hrS, reach_refl hrS⟩
      have hCS : C ⊆ S := Finset.filter_subset _ _
      have hCout : ∀ u ∈ C, ∀ v ∈ S, D u v → v ∈ C := by
        intro u huC v hvS huv
        have huS : u ∈ S := (Finset.mem_filter.mp huC).1
        have hru : Reach D S r u := (Finset.mem_filter.mp huC).2
        exact Finset.mem_filter.mpr ⟨hvS, reach_step hru huS hvS huv⟩
      have hCstrong : ∀ u ∈ C, Reach D S u r := by
        intro u huC
        have huS : u ∈ S := (Finset.mem_filter.mp huC).1
        have hru : Reach D S r u := (Finset.mem_filter.mp huC).2
        have hsub : R u ⊆ C := by
          intro w hw
          have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
          have huw : Reach D S u w := (Finset.mem_filter.mp hw).2
          exact Finset.mem_filter.mpr ⟨hwS, reach_trans hru huw⟩
        have hle : C.card ≤ (R u).card := hrmin u huS
        have heq : R u = C := Finset.eq_of_subset_of_card_le hsub hle
        have hrRu : r ∈ R u := heq ▸ hrC
        exact (Finset.mem_filter.mp hrRu).2
      let A : Finset (Fin n) := C.filter (fun u => EvenReach D S r u)
      have hAC : A ⊆ C := Finset.filter_subset _ _
      have hAS : A ⊆ S := Finset.Subset.trans hAC hCS
      have hrA : r ∈ A := Finset.mem_filter.mpr ⟨hrC, ⟨0, walk_refl hrS⟩⟩
      have hAindep : ∀ u ∈ A, ∀ v ∈ A, ¬ D u v := by
        intro u huA v hvA huv
        have huC : u ∈ C := (Finset.mem_filter.mp huA).1
        have hvC : v ∈ C := (Finset.mem_filter.mp hvA).1
        have huS : u ∈ S := hCS huC
        have hvS : v ∈ S := hCS hvC
        rcases (Finset.mem_filter.mp huA).2 with ⟨a, ha⟩
        rcases (Finset.mem_filter.mp hvA).2 with ⟨b, hb⟩
        rcases hCstrong v hvC with ⟨m, hm⟩
        have hclosed1 : Walk D S (2 * b + m) r r := walk_append hb hm
        have hm_even : (2 * b + m) % 2 = 0 := no_odd_closed_in_S hodd hclosed1
        have hru1 : Walk D S (2 * a + 1) r v := walk_append ha (walk_single huS hvS huv)
        have hclosed2 : Walk D S (2 * a + 1 + m) r r := walk_append hru1 hm
        have hmod2 : (2 * a + 1 + m) % 2 = 0 := no_odd_closed_in_S hodd hclosed2
        omega
      have hAabsorbC : ∀ v ∈ C, v ∉ A → ∃ a ∈ A, D v a := by
        intro v hvC hvnotA
        have hvS : v ∈ S := hCS hvC
        have hvr_ne : v ≠ r := by
          intro h
          subst h
          exact hvnotA hrA
        rcases hCstrong v hvC with ⟨m, p, hp0, hpm, hpS, hpD⟩
        have hmpos : 0 < m := by
          by_contra hm0
          have hmzero : m = 0 := by omega
          subst hmzero
          exact hvr_ne (hp0.symm.trans hpm)
        let u : Fin n := p 1
        have huS : u ∈ S := hpS 1 (by omega)
        have hvu : D v u := by
          have h0 := hpD 0 hmpos
          simpa [hp0, u] using h0
        have huC : u ∈ C := hCout v hvC u huS hvu
        rcases (Finset.mem_filter.mp hvC).2 with ⟨d, hd⟩
        have hd_odd : d % 2 = 1 := by
          by_contra hnotodd
          have hdeven : d = 2 * (d / 2) := by omega
          apply hvnotA
          refine Finset.mem_filter.mpr ⟨hvC, ⟨d / 2, ?_⟩⟩
          rwa [← hdeven]
        have hru : Walk D S (d + 1) r u := walk_append hd (walk_single hvS huS hvu)
        have huA : u ∈ A := by
          refine Finset.mem_filter.mpr ⟨huC, ⟨(d + 1) / 2, ?_⟩⟩
          have hd1 : 2 * ((d + 1) / 2) = d + 1 := by omega
          rwa [hd1]
        exact ⟨u, huA, hvu⟩
      let S' : Finset (Fin n) := S.filter (fun v => v ∉ A ∧ ¬ ∃ a ∈ A, D v a)
      have hS'S : S' ⊆ S := Finset.filter_subset _ _
      have hrnotS' : r ∉ S' := by
        intro hr'
        exact (Finset.mem_filter.mp hr').2.1 hrA
      have hS'card : S'.card ≤ k := by
        have hlt : S'.card < S.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS'S, fun h => hrnotS' (h ▸ hrS)⟩)
        omega
      rcases ih S' hS'card with ⟨K', hK'S', hK'indep, hK'abs⟩
      refine ⟨A ∪ K', Finset.union_subset hAS (Finset.Subset.trans hK'S' hS'S), ?_, ?_⟩
      · intro u hu v hv huv
        rcases Finset.mem_union.mp hu with huA | huK'
        · rcases Finset.mem_union.mp hv with hvA | hvK'
          · exact hAindep u huA v hvA huv
          · have hvS' : v ∈ S' := hK'S' hvK'
            have hvS : v ∈ S := hS'S hvS'
            have hvC : v ∈ C := hCout u (hAC huA) v hvS huv
            have hvnotA : v ∉ A := (Finset.mem_filter.mp hvS').2.1
            have hvnoA : ¬ ∃ a ∈ A, D v a := (Finset.mem_filter.mp hvS').2.2
            exact hvnoA (hAabsorbC v hvC hvnotA)
        · rcases Finset.mem_union.mp hv with hvA | hvK'
          · have huS' : u ∈ S' := hK'S' huK'
            exact (Finset.mem_filter.mp huS').2.2 ⟨v, hvA, huv⟩
          · exact hK'indep u huK' v hvK' huv
      · intro v hvS hvnotK
        have hvnotA : v ∉ A := fun h => hvnotK (Finset.mem_union_left K' h)
        have hvnotK' : v ∉ K' := fun h => hvnotK (Finset.mem_union_right A h)
        by_cases habs : ∃ a ∈ A, D v a
        · rcases habs with ⟨a, haA, hva⟩
          exact ⟨a, Finset.mem_union_left K' haA, hva⟩
        · have hvS' : v ∈ S' := Finset.mem_filter.mpr ⟨hvS, hvnotA, habs⟩
          rcases hK'abs v hvS' hvnotK' with ⟨a, haK', hva⟩
          exact ⟨a, Finset.mem_union_right A haK', hva⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
      · intro u hu; exact absurd hu (Finset.notMem_empty u)
      · intro v hv; exact absurd hv (Finset.notMem_empty v)

theorem main :
    ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
      (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
      (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ hodd
  rcases exists_kernel_finset D hodd (Finset.univ : Finset (Fin n)).card Finset.univ (le_refl _) with
    ⟨K, _, hind, habs⟩
  refine ⟨(K : Set (Fin n)), ?_, ?_⟩
  · intro u hu v hv
    exact hind u hu v hv
  · intro v hv
    rcases habs v (Finset.mem_univ v) hv with ⟨a, ha, hva⟩
    exact ⟨a, ha, hva⟩

end PEqualNP.Outside.L_meta_729_aux

theorem PEqualNP.Outside.L_meta_729 :
    ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
      (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
      (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k :=
  PEqualNP.Outside.L_meta_729_aux.main
