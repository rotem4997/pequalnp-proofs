import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class: residuals of `F` and the drops of the potential (`L-meta-115`, builder B4)

Proofs of the plan pieces `ToolRes0`, `ToolRes1`, `ToolResA`, `ToolResPair` (the function
`F G A` with inputs fixed is again of the class) and `ToolDrop0`, `ToolDrop1`, `ToolDropPair`
(the potential `Phi1` drops by at most 3, 4, 5 under those residuals, and the edge count drops).
Paper: `routes/lifting/lgp/FO1-monotone-direct.md` E0 to E2, `gadv32-class.md` S1.
-/

namespace PEqualNP.MetaComplexity.Loc.Res

open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Helpers.Forest SimpleGraph

/-! ## Residuals -/

theorem ToolRes0_proof : ToolRes0 := by
  intro n G A v x hv
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hav] at h⟩
    · rintro ⟨a, ha, h⟩
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hav]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hiv : i ≠ v := by rintro rfl; simp at hi
      have hjv : j ≠ v := by rintro rfl; simp at hj
      refine ⟨i, j, (delV_adj G {v} i j).2 ⟨hij, by simpa using hiv, by simpa using hjv⟩,
        by rwa [Function.update_of_ne hiv] at hi, by rwa [Function.update_of_ne hjv] at hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨hij, hiv, hjv⟩ := (delV_adj G {v} i j).1 hij
      have hiv' : i ≠ v := by simpa using hiv
      have hjv' : j ≠ v := by simpa using hjv
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hiv'], by rwa [Function.update_of_ne hjv']⟩

theorem ToolRes1_proof : ToolRes1 := by
  intro n G A v N x hv hN
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact Or.inl ⟨a, Finset.mem_union_left _ ha, by rwa [Function.update_of_ne hav] at h⟩
    · by_cases hiv : i = v
      · subst hiv
        exact Or.inl ⟨j, Finset.mem_union_right _ ((hN j).1 hij),
          by rwa [Function.update_of_ne hij.ne.symm] at hj⟩
      by_cases hjv : j = v
      · subst hjv
        exact Or.inl ⟨i, Finset.mem_union_right _ ((hN i).1 hij.symm),
          by rwa [Function.update_of_ne hij.ne] at hi⟩
      rw [Function.update_of_ne hiv] at hi
      rw [Function.update_of_ne hjv] at hj
      by_cases hiN : i ∈ N
      · exact Or.inl ⟨i, Finset.mem_union_right _ hiN, hi⟩
      by_cases hjN : j ∈ N
      · exact Or.inl ⟨j, Finset.mem_union_right _ hjN, hj⟩
      exact Or.inr ⟨i, j, (delV_adj G _ i j).2 ⟨hij, by simp [hiv, hiN], by simp [hjv, hjN]⟩,
        hi, hj⟩
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_union.1 ha with ha | ha
      · have hav : a ≠ v := fun e => hv (e ▸ ha)
        exact Or.inl ⟨a, ha, by rwa [Function.update_of_ne hav]⟩
      · have hva := (hN a).2 ha
        exact Or.inr ⟨v, a, hva, by simp, by rwa [Function.update_of_ne hva.ne.symm]⟩
    · obtain ⟨hij, hi', hj'⟩ := (delV_adj G _ i j).1 hij
      simp only [Finset.mem_insert, not_or] at hi' hj'
      exact Or.inr ⟨i, j, hij, by rwa [Function.update_of_ne hi'.1],
        by rwa [Function.update_of_ne hj'.1]⟩

theorem ToolResA_proof : ToolResA := by
  intro n G A a x hfree ha
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a', ha', h⟩
      have hne : a' ≠ a := by rintro rfl; simp at h
      exact ⟨a', Finset.mem_erase.2 ⟨hne, ha'⟩, by rwa [Function.update_of_ne hne] at h⟩
    · rintro ⟨a', ha', h⟩
      obtain ⟨hne, ha'⟩ := Finset.mem_erase.1 ha'
      exact ⟨a', ha', by rwa [Function.update_of_ne hne]⟩
  · have hi : ∀ i j, G.Adj i j → i ≠ a := fun i j hij e => hfree i j hij (e ▸ ha)
    constructor
    · rintro ⟨i, j, hij, h1, h2⟩
      exact ⟨i, j, hij, by rwa [Function.update_of_ne (hi i j hij)] at h1,
        by rwa [Function.update_of_ne (hi j i hij.symm)] at h2⟩
    · rintro ⟨i, j, hij, h1, h2⟩
      exact ⟨i, j, hij, by rwa [Function.update_of_ne (hi i j hij)],
        by rwa [Function.update_of_ne (hi j i hij.symm)]⟩

theorem ToolResPair_proof : ToolResPair := by
  intro n G A s t b x hst hbs hsA htA hbA ht
  have htb : G.Adj t b := (ht b).2 (Or.inr rfl)
  have hbt : b ≠ t := htb.ne.symm
  have hys : Function.update (Function.update x t true) s false s = false := by simp
  have hyt : Function.update (Function.update x t true) s false t = true := by
    rw [Function.update_of_ne hst.symm]; simp
  have hy : ∀ w, w ≠ s → w ≠ t → Function.update (Function.update x t true) s false w = x w := by
    intro w h1 h2
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have h1 : a ≠ s := fun e => hsA (e ▸ ha)
      have h2 : a ≠ t := fun e => htA (e ▸ ha)
      exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hy a h1 h2] at h⟩
    · have his : i ≠ s := by rintro rfl; rw [hys] at hi; exact absurd hi (by simp)
      have hjs : j ≠ s := by rintro rfl; rw [hys] at hj; exact absurd hj (by simp)
      have hxb : (Function.update (Function.update x t true) s false b = true) → x b = true :=
        fun h => by rwa [hy b hbs hbt] at h
      by_cases hit : i = t
      · subst hit
        rcases (ht j).1 hij with rfl | rfl
        · exact absurd rfl hjs
        · exact Or.inl ⟨j, Finset.mem_insert_self _ _, hxb hj⟩
      by_cases hjt : j = t
      · subst hjt
        rcases (ht i).1 hij.symm with rfl | rfl
        · exact absurd rfl his
        · exact Or.inl ⟨i, Finset.mem_insert_self _ _, hxb hi⟩
      rw [hy i his hit] at hi
      rw [hy j hjs hjt] at hj
      by_cases hib : i = b
      · subst hib; exact Or.inl ⟨i, Finset.mem_insert_self _ _, hi⟩
      by_cases hjb : j = b
      · subst hjb; exact Or.inl ⟨j, Finset.mem_insert_self _ _, hj⟩
      exact Or.inr ⟨i, j, (delV_adj G _ i j).2 ⟨hij, by simp [his, hit, hib],
        by simp [hjs, hjt, hjb]⟩, hi, hj⟩
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · exact Or.inr ⟨t, a, htb, hyt, by rwa [hy a hbs hbt]⟩
      · have h1 : a ≠ s := fun e => hsA (e ▸ ha)
        have h2 : a ≠ t := fun e => htA (e ▸ ha)
        exact Or.inl ⟨a, ha, by rwa [hy a h1 h2]⟩
    · obtain ⟨hij, hi', hj'⟩ := (delV_adj G _ i j).1 hij
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi' hj'
      exact Or.inr ⟨i, j, hij, by rwa [hy i hi'.1 hi'.2.1], by rwa [hy j hj'.1 hj'.2.1]⟩

/-! ## Counting lemmas for the drops -/

/-- If every edge with an end in `X` lies in `S`, deleting the edges at `X` removes at most
`|S|` edges. -/
theorem edges_le {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (S : Finset (Sym2 (Fin n))) (h : ∀ i j, G.Adj i j → i ∈ X → s(i, j) ∈ S) :
    G.edgeSet.ncard ≤ (delV G X).edgeSet.ncard + S.card := by
  have hsub : G.edgeSet ⊆ (delV G X).edgeSet ∪ (S : Set (Sym2 (Fin n))) := by
    intro e he
    induction e using Sym2.ind with
    | _ i j =>
      have hij : G.Adj i j := G.mem_edgeSet.1 he
      by_cases hi : i ∈ X
      · exact Or.inr (Finset.mem_coe.2 (h i j hij hi))
      by_cases hj : j ∈ X
      · have := h j i hij.symm hj
        rw [Sym2.eq_swap] at this
        exact Or.inr (Finset.mem_coe.2 this)
      exact Or.inl ((delV G X).mem_edgeSet.2 ((delV_adj G X i j).2 ⟨hij, hi, hj⟩))
  calc G.edgeSet.ncard ≤ ((delV G X).edgeSet ∪ (S : Set (Sym2 (Fin n)))).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (delV G X).edgeSet.ncard + (S : Set (Sym2 (Fin n))).ncard := Set.ncard_union_le _ _
    _ = (delV G X).edgeSet.ncard + S.card := by rw [Set.ncard_coe_finset]

/-- An edge with an end in `X` is deleted. -/
theorem edges_lt {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n)
    (hij : G.Adj i j) (hi : i ∈ X) : (delV G X).edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  rw [Set.ssubset_iff_of_subset (edgeSet_subset_edgeSet.2 (delV_le G X))]
  refine ⟨s(i, j), G.mem_edgeSet.2 hij, fun hmem => ?_⟩
  exact ((delV_adj G X i j).1 ((delV G X).mem_edgeSet.1 hmem)).2.1 hi

/-- If every edge with an end in `X` has an end in `Y`, a cover of the residual plus `Y`
covers `G`. -/
theorem tau_delV {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (h : ∀ i j, G.Adj i j → i ∈ X → i ∈ Y ∨ j ∈ Y) :
    tau G ≤ tau (delV G X) + Y.card := by
  obtain ⟨T, hT, hc⟩ := tau_attained (delV G X)
  have hcov : Cov G (T ∪ Y) := by
    intro i j hij
    by_cases hi : i ∈ X
    · rcases h i j hij hi with h' | h'
      · exact Or.inl (Finset.mem_union_right _ h')
      · exact Or.inr (Finset.mem_union_right _ h')
    by_cases hj : j ∈ X
    · rcases h j i hij.symm hj with h' | h'
      · exact Or.inr (Finset.mem_union_right _ h')
      · exact Or.inl (Finset.mem_union_right _ h')
    rcases hT i j ((delV_adj G X i j).2 ⟨hij, hi, hj⟩) with h' | h'
    · exact Or.inl (Finset.mem_union_left _ h')
    · exact Or.inr (Finset.mem_union_left _ h')
  calc tau G ≤ (T ∪ Y).card := tau_le G _ hcov
    _ ≤ T.card + Y.card := Finset.card_union_le _ _
    _ = tau (delV G X) + Y.card := by rw [hc]

theorem card_le_two' {α : Type*} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

theorem card_le_four' {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  exact Nat.succ_le_succ (card_le_two' c d)

/-! ## Drops -/

theorem ToolDrop0_proof : ToolDrop0 := by
  intro n G A v u1 u2 h1 hv
  refine ⟨?_, edges_lt G {v} v u1 h1 (Finset.mem_singleton_self v)⟩
  have hE := edges_le G {v} {s(v, u1), s(v, u2)} (by
    intro i j hij hi
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases hv j hij with rfl | rfl <;> simp)
  have hT := tau_delV G {v} {v} (fun i j _ hi => Or.inl hi)
  have hS := card_le_two' (s(v, u1)) (s(v, u2))
  rw [Finset.card_singleton] at hT
  unfold Phi1
  omega

theorem ToolDrop1_proof : ToolDrop1 := by
  intro n G A v u1 u2 c1 c2 hv h1 h2 hu1 hu2
  have hvu1 : G.Adj v u1 := (hv u1).2 (Or.inl rfl)
  refine ⟨?_, edges_lt G _ v u1 hvu1 (Finset.mem_insert_self _ _)⟩
  have hE := edges_le G (insert v {u1, u2}) {s(v, u1), s(v, u2), s(u1, c1), s(u2, c2)} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · rcases h1 j hij with rfl | rfl <;> simp [Sym2.eq_swap]
    · rcases h2 j hij with rfl | rfl <;> simp [Sym2.eq_swap])
  have hT := tau_delV G (insert v {u1, u2}) {u1, u2} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · simp
    · simp)
  have hS := card_le_four' (s(v, u1)) (s(v, u2)) (s(u1, c1)) (s(u2, c2))
  have hdis : A ∩ {u1, u2} = ∅ := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro hw (rfl | rfl)
    · exact hu1 hw
    · exact hu2 hw
  have hA := Finset.card_union_add_card_inter A {u1, u2}
  rw [hdis, Finset.card_empty] at hA
  unfold Phi1
  omega

theorem ToolDropPair_proof : ToolDropPair := by
  intro n G A a s t b c _ hs ht hb hbA
  have hts : G.Adj t s := (ht s).2 (Or.inl rfl)
  refine ⟨?_, edges_lt G _ t s hts (by simp)⟩
  have hE := edges_le G {s, t, b} {s(s, a), s(s, t), s(t, b), s(b, c)} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases hs j hij with rfl | rfl <;> simp
    · rcases (ht j).1 hij with rfl | rfl <;> simp [Sym2.eq_swap]
    · rcases hb j hij with rfl | rfl <;> simp [Sym2.eq_swap])
  have hT := tau_delV G {s, t, b} {s, b} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp
    · rcases (ht j).1 hij with rfl | rfl <;> simp
    · simp)
  have hS := card_le_four' (s(s, a)) (s(s, t)) (s(t, b)) (s(b, c))
  have hY := card_le_two' s b
  have hA := Finset.card_insert_of_notMem hbA
  unfold Phi1
  omega

end PEqualNP.MetaComplexity.Loc.Res
