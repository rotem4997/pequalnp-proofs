import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
    unfold step
    exact List.getD_append _ _ _ _ hi

lemma wires_sem : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate), gs[j]? = some g →
    (∀ i ∈ g.inputs, i < w.length + j) →
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
  intro gs
  induction gs with
  | nil =>
    intro w j g h
    simp at h
  | cons g0 gs ih =>
    intro w j g h hin
    cases j with
    | zero =>
      have hg : g0 = g := by simpa using h
      rw [← hg] at hin ⊢
      rw [List.foldl_cons, Nat.add_zero, fold_pre gs (step w g0) w.length (by simp [step])]
      have e1 : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := by
        unfold step
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_pre gs (step w g0) i (by simp [step]; omega)]
      unfold step
      exact (List.getD_append _ _ _ _ (by omega)).symm
    | succ j =>
      have h' : gs[j]? = some g := by simpa using h
      have hih := ih (step w g0) j g h' (fun i hi => by
        have := hin i hi
        simp [step]
        omega)
      rw [List.foldl_cons]
      have e : w.length + (j + 1) = (step w g0).length + j := by
        simp [step]
        omega
      rw [e]
      exact hih

lemma gate_sem (C : Circuit) (N : ℕ) (hrb : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h := wires_sem C.gates x j (gateAt C j)
    (by unfold gateAt; rw [List.getD_eq_getElem?_getD]; simp [List.getElem?_eq_getElem hj])
    (by intro i hi; rw [hx]; exact hrb j hj i hi)
  rw [hx] at h
  exact h

def inp (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) : List Bool :=
  List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))

lemma inp_len (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) :
    (inp n m P L).length = n + m := by
  simp [inp]

lemma inp_left (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) (p : Fin n) :
    (inp n m P L).getD p.val false = decide (p ∈ P) := by
  unfold inp
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

lemma inp_right (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) (l : Fin m) :
    (inp n m P L).getD (n + l.val) false = decide (l ∈ L) := by
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

lemma inp_get_lt (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) (u : ℕ) (h : u < n) :
    (inp n m P L).getD u false = decide ((⟨u, h⟩ : Fin n) ∈ P) :=
  inp_left n m P L ⟨u, h⟩

lemma inp_get_ge (n m : ℕ) (P : Finset (Fin n)) (L : Finset (Fin m)) (u : ℕ) (h1 : n ≤ u)
    (h2 : u - n < m) :
    (inp n m P L).getD u false = decide ((⟨u - n, h2⟩ : Fin m) ∈ L) := by
  have h := inp_right n m P L ⟨u - n, h2⟩
  have e : n + (u - n) = u := by omega
  have h' : (inp n m P L).getD (n + (u - n)) false = decide ((⟨u - n, h2⟩ : Fin m) ∈ L) := h
  rw [e] at h'
  exact h'

lemma U {γ ι : Type} [DecidableEq γ] {s : ℕ} (S : Fin s → Finset γ)
    (hS : ∀ j, ∃ X Y, S j ⊆ X ∪ Y ∧ (X.card ≤ 1 ∨ ∃ j', j' < j ∧ X ⊆ S j') ∧
      (Y.card ≤ 1 ∨ ∃ j', j' < j ∧ Y ⊆ S j'))
    (K : Finset ι) (τ : ι → Finset γ) (hτ : ∀ t ∈ K, (τ t).card ≤ 1 ∨ ∃ j, τ t ⊆ S j) :
    ∀ (N : ℕ) (P : Finset γ), P.card = N → P ⊆ K.biUnion τ →
      P.card ≤ (Finset.univ.filter (fun j => 2 ≤ (S j ∩ P).card)).card + K.card := by
  intro N
  induction N with
  | zero => intro P h _; omega
  | succ N ih =>
    intro P hc hsub
    by_cases hr : ∃ j, 2 ≤ (S j ∩ P).card
    · obtain ⟨j1, hj1m, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter (fun j : Fin s => 2 ≤ (S j ∩ P).card)) (fun j => j.val)
        (by obtain ⟨j, hj⟩ := hr; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)
      have hj1 : 2 ≤ (S j1 ∩ P).card := (Finset.mem_filter.mp hj1m).2
      have hlt : ∀ j', j' < j1 → (S j' ∩ P).card ≤ 1 := by
        intro j' hj'
        by_contra hcon
        have h1 := hmin j' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
        have h2 : j'.val < j1.val := hj'
        omega
      obtain ⟨X, Y, hXY, hX, hY⟩ := hS j1
      have hXP : (X ∩ P).card ≤ 1 := by
        rcases hX with h | ⟨j', hj', hs'⟩
        · exact le_trans (Finset.card_le_card Finset.inter_subset_left) h
        · exact le_trans (Finset.card_le_card (Finset.inter_subset_inter hs' subset_rfl)) (hlt j' hj')
      have hYP : (Y ∩ P).card ≤ 1 := by
        rcases hY with h | ⟨j', hj', hs'⟩
        · exact le_trans (Finset.card_le_card Finset.inter_subset_left) h
        · exact le_trans (Finset.card_le_card (Finset.inter_subset_inter hs' subset_rfl)) (hlt j' hj')
      have h2 : (S j1 ∩ P).card ≤ 2 := by
        have hs2 : S j1 ∩ P ⊆ (X ∩ P) ∪ (Y ∩ P) := by
          intro x hx
          rw [Finset.mem_inter] at hx
          have := hXY hx.1
          rw [Finset.mem_union] at this
          rcases this with h | h
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hx.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, hx.2⟩)
        have := Finset.card_le_card hs2
        have := Finset.card_union_le (X ∩ P) (Y ∩ P)
        omega
      obtain ⟨v, hv⟩ : (S j1 ∩ P).Nonempty := Finset.card_pos.mp (by omega)
      have hvP : v ∈ P := (Finset.mem_inter.mp hv).2
      have hc' : (P.erase v).card = N := by
        rw [Finset.card_erase_of_mem hvP]; omega
      have hih := ih (P.erase v) hc' ((Finset.erase_subset _ _).trans hsub)
      have hj1' : (S j1 ∩ P.erase v).card ≤ 1 := by
        rw [Finset.inter_erase, Finset.card_erase_of_mem hv]; omega
      have hfs : Finset.univ.filter (fun j => 2 ≤ (S j ∩ P.erase v).card) ⊆
          (Finset.univ.filter (fun j => 2 ≤ (S j ∩ P).card)).erase j1 := by
        intro j hj
        have hj2 := (Finset.mem_filter.mp hj).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · intro e
          rw [e] at hj2
          omega
        · exact le_trans hj2 (Finset.card_le_card
            (Finset.inter_subset_inter subset_rfl (Finset.erase_subset _ _)))
      have h3 := Finset.card_le_card hfs
      rw [Finset.card_erase_of_mem hj1m] at h3
      have h4 : 0 < (Finset.univ.filter (fun j => 2 ≤ (S j ∩ P).card)).card :=
        Finset.card_pos.mpr ⟨j1, hj1m⟩
      have h5 : (P.erase v).card = P.card - 1 := Finset.card_erase_of_mem hvP
      omega
    · push Not at hr
      have h0 : Finset.univ.filter (fun j => 2 ≤ (S j ∩ P).card) = ∅ := by
        apply Finset.subset_empty.mp
        intro j hj
        have := (Finset.mem_filter.mp hj).2
        have := hr j
        omega
      have h1 : P.card ≤ (K.biUnion (fun t => τ t ∩ P)).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp (hsub hx)
        exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_inter.mpr ⟨hxt, hx⟩⟩
      have h2 : (K.biUnion (fun t => τ t ∩ P)).card ≤ ∑ t ∈ K, (τ t ∩ P).card :=
        Finset.card_biUnion_le
      have h3 : ∑ t ∈ K, (τ t ∩ P).card ≤ ∑ t ∈ K, 1 := by
        apply Finset.sum_le_sum
        intro t ht
        rcases hτ t ht with h | ⟨j, hj⟩
        · exact le_trans (Finset.card_le_card Finset.inter_subset_left) h
        · have := hr j
          have := Finset.card_le_card (Finset.inter_subset_inter hj (subset_refl P))
          omega
      have h4 : ∑ t ∈ K, 1 = K.card := by simp
      omega

lemma card3 {α : Type} [Fintype α] [DecidableEq α] (X Y Z : Finset α) (h1 : Disjoint X Y)
    (h2 : Disjoint X Z) (h3 : Disjoint Y Z) : X.card + Y.card + Z.card ≤ Fintype.card α := by
  have h := Finset.card_le_univ (X ∪ Y ∪ Z)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h2, h3⟩),
    Finset.card_union_of_disjoint h1] at h
  exact h

lemma bound2 (n m s k : ℕ) (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) (SP : Fin s → Finset (Fin n)) (SL : Fin s → Finset (Fin m))
    (hq : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (hG : ∀ j, ∃ (XP YP : Finset (Fin n)) (XL YL : Finset (Fin m)), SP j = XP ∪ YP ∧
      SL j = XL ∪ YL ∧ (XP.card + XL.card ≤ 1 ∨ ∃ j', j' < j ∧ XP = SP j' ∧ XL = SL j') ∧
      (YP.card + YL.card ≤ 1 ∨ ∃ j', j' < j ∧ YP = SP j' ∧ YL = SL j'))
    (hA : ∀ t, (A t).card ≤ 1 ∨ ∃ j, SL j = ∅ ∧ SP j = A t)
    (T : Finset (Fin n × Fin m))
    (hT : ∀ q ∈ T, ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g q.2 = true) :
    ∃ (G : Finset (Fin s)) (K : Finset (Fin k)), T.card ≤ G.card + K.card ∧
      (∀ j ∈ G, SL j = ∅ ∧ ∃ t f, SP j ⊆ A t ∧ f ∈ B t ∧ (∀ g ∈ A t, inc g f = true) ∧
        2 ≤ (SP j).card) ∧
      (∀ t ∈ K, 2 ≤ (A t).card ∧ ∃ f ∈ B t, ∀ g ∈ A t, inc g f = true) := by
  classical
  let S2 : Fin s → Finset (Fin n × Fin m) := fun j => Finset.univ.filter (fun q =>
    q.1 ∈ SP j ∧ SL j = ∅ ∧ 2 ≤ (SP j).card ∧
      ∃ t, SP j ⊆ A t ∧ q.2 ∈ B t ∧ ∀ g ∈ A t, inc g q.2 = true)
  have mS2 : ∀ j q, q ∈ S2 j ↔ (q.1 ∈ SP j ∧ SL j = ∅ ∧ 2 ≤ (SP j).card ∧
      ∃ t, SP j ⊆ A t ∧ q.2 ∈ B t ∧ ∀ g ∈ A t, inc g q.2 = true) := by
    intro j q
    simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and]
  let K : Finset (Fin k) := Finset.univ.filter (fun t =>
    2 ≤ (A t).card ∧ ∃ f ∈ B t, ∀ g ∈ A t, inc g f = true)
  have mK : ∀ t, t ∈ K ↔ (2 ≤ (A t).card ∧ ∃ f ∈ B t, ∀ g ∈ A t, inc g f = true) := by
    intro t
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  let τ : Fin k → Finset (Fin n × Fin m) := fun t =>
    (A t ×ˢ B t).filter (fun q => ∀ g ∈ A t, inc g q.2 = true)
  have mτ : ∀ t q, q ∈ τ t ↔ ((q.1 ∈ A t ∧ q.2 ∈ B t) ∧ ∀ g ∈ A t, inc g q.2 = true) := by
    intro t q
    simp only [τ, Finset.mem_filter, Finset.mem_product]
  have uniq : ∀ (X : Finset (Fin n)) (f f' : Fin m), 2 ≤ X.card →
      (∀ g ∈ X, inc g f = true) → (∀ g ∈ X, inc g f' = true) → f = f' := by
    intro X f f' hX h1 h2
    by_contra hne
    obtain ⟨g, hg, g', hg', hgg⟩ := Finset.one_lt_card.mp hX
    exact hq g g' f f' hgg hne (h1 g hg) (h1 g' hg') (h2 g hg) (h2 g' hg')
  have hS : ∀ j, ∃ X Y, S2 j ⊆ X ∪ Y ∧ (X.card ≤ 1 ∨ ∃ j', j' < j ∧ X ⊆ S2 j') ∧
      (Y.card ≤ 1 ∨ ∃ j', j' < j ∧ Y ⊆ S2 j') := by
    intro j
    obtain ⟨XP, YP, XL, YL, hP, hL, hX, hY⟩ := hG j
    have key : ∀ (ZP : Finset (Fin n)) (ZL : Finset (Fin m)), ZP ⊆ SP j → ZL ⊆ SL j →
        (ZP.card + ZL.card ≤ 1 ∨ ∃ j', j' < j ∧ ZP = SP j' ∧ ZL = SL j') →
        (((S2 j).filter (fun q => q.1 ∈ ZP)).card ≤ 1 ∨
          ∃ j', j' < j ∧ (S2 j).filter (fun q => q.1 ∈ ZP) ⊆ S2 j') := by
      intro ZP ZL hZP hZL hZ
      by_cases hc : ZP.card ≤ 1
      · left
        rw [Finset.card_le_one]
        intro q hq1 q' hq2
        obtain ⟨hqS, hz⟩ := Finset.mem_filter.mp hq1
        obtain ⟨hq'S, hz'⟩ := Finset.mem_filter.mp hq2
        obtain ⟨-, -, h2, t, ht, -, hinc⟩ := (mS2 j q).mp hqS
        obtain ⟨-, -, -, t', ht', -, hinc'⟩ := (mS2 j q').mp hq'S
        have e1 : q.1 = q'.1 := Finset.card_le_one.mp hc _ hz _ hz'
        have e2 : q.2 = q'.2 := uniq (SP j) _ _ h2 (fun g hg => hinc g (ht hg))
          (fun g hg => hinc' g (ht' hg))
        exact Prod.ext e1 e2
      · right
        rcases hZ with h | ⟨j', hj', e1, e2⟩
        · omega
        · refine ⟨j', hj', ?_⟩
          intro q hq1
          obtain ⟨hqS, hz⟩ := Finset.mem_filter.mp hq1
          obtain ⟨-, hl, -, t, ht, hb, hinc⟩ := (mS2 j q).mp hqS
          refine (mS2 j' q).mpr ⟨by rw [← e1]; exact hz, ?_, by rw [← e1]; omega, t, ?_, hb, hinc⟩
          · rw [← e2]
            exact Finset.subset_empty.mp (by rw [← hl]; exact hZL)
          · rw [← e1]
            exact hZP.trans ht
    refine ⟨(S2 j).filter (fun q => q.1 ∈ XP), (S2 j).filter (fun q => q.1 ∈ YP), ?_,
      key XP XL ?_ ?_ hX, key YP YL ?_ ?_ hY⟩
    · intro q hq1
      have h1 : q.1 ∈ SP j := ((mS2 j q).mp hq1).1
      rw [hP, Finset.mem_union] at h1
      rcases h1 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq1, h⟩)
    · rw [hP]; exact Finset.subset_union_left
    · rw [hL]; exact Finset.subset_union_left
    · rw [hP]; exact Finset.subset_union_right
    · rw [hL]; exact Finset.subset_union_right
  have hτ : ∀ t ∈ K, (τ t).card ≤ 1 ∨ ∃ j, τ t ⊆ S2 j := by
    intro t ht
    have ht' := (mK t).mp ht
    right
    rcases hA t with h | ⟨j, hj1, hj2⟩
    · omega
    · refine ⟨j, ?_⟩
      intro q hq1
      have hq2 := (mτ t q).mp hq1
      exact (mS2 j q).mpr ⟨by rw [hj2]; exact hq2.1.1, hj1, by rw [hj2]; exact ht'.1, t,
        by rw [hj2], hq2.1.2, hq2.2⟩
  have hsub : T ⊆ K.biUnion τ := by
    intro q hqT
    obtain ⟨t, h1, h2, h3, h4⟩ := hT q hqT
    exact Finset.mem_biUnion.mpr ⟨t, (mK t).mpr ⟨h3, q.2, h2, h4⟩, (mτ t q).mpr ⟨⟨h1, h2⟩, h4⟩⟩
  refine ⟨Finset.univ.filter (fun j => 2 ≤ (S2 j ∩ T).card), K,
    U S2 hS K τ hτ T.card T rfl hsub, ?_, ?_⟩
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    obtain ⟨q, hqm⟩ : (S2 j ∩ T).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨-, hl, h2, t, ht, hb, hinc⟩ := (mS2 j q).mp (Finset.mem_inter.mp hqm).1
    exact ⟨hl, t, q.2, ht, hb, hinc, h2⟩
  · intro t ht
    exact (mK t).mp ht

lemma bound4 (n m s k : ℕ) (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) (SP : Fin s → Finset (Fin n)) (SL : Fin s → Finset (Fin m))
    (hq : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (hG : ∀ j, ∃ (XP YP : Finset (Fin n)) (XL YL : Finset (Fin m)), SP j = XP ∪ YP ∧
      SL j = XL ∪ YL ∧ (XP.card + XL.card ≤ 1 ∨ ∃ j', j' < j ∧ XP = SP j' ∧ XL = SL j') ∧
      (YP.card + YL.card ≤ 1 ∨ ∃ j', j' < j ∧ YP = SP j' ∧ YL = SL j'))
    (hA : ∀ t, (A t).card ≤ 1 ∨ ∃ j, SL j = ∅ ∧ SP j = A t)
    (hM1 : ∀ i j, i ≠ j → ∀ p, p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true))
    (T : Finset (Fin n × Fin m))
    (hT : ∀ q ∈ T, inc q.1 q.2 = true ∧ ∃ i j, q.1 ∈ A i ∧ B i = {q.2} ∧
      (∃ g ∈ A i, inc g q.2 = false) ∧ A j = {q.1} ∧ q.2 ∈ B j ∧ (∃ e ∈ B j, inc q.1 e = false)) :
    ∃ (G : Finset (Fin s)) (K : Finset (Fin k)), T.card ≤ G.card + K.card ∧
      (∀ j ∈ G, SL j = ∅ ∧ ∃ l p p', p ≠ p' ∧ p ∈ SP j ∧ p' ∈ SP j ∧ (p, l) ∈ T ∧ (p', l) ∈ T) ∧
      (∀ t ∈ K, (B t).card = 1 ∧ ∃ g ∈ A t, ∃ l ∈ B t, inc g l = false) := by
  classical
  have F4 : ∀ q ∈ T, ∀ (t : Fin k) (l' : Fin m), q.1 ∈ A t → B t = {l'} → inc q.1 l' = true := by
    intro q hqT t l' hpt hBt
    obtain ⟨hinc, i, j, -, -, -, hAj, hlj, e, he, hne⟩ := hT q hqT
    by_cases htj : t = j
    · have h := hlj
      rw [← htj, hBt, Finset.mem_singleton] at h
      rw [← h]
      exact hinc
    · rcases hM1 t j htj q.1 hpt (by rw [hAj]; exact Finset.mem_singleton_self _) with h | h
      · exact h l' (by rw [hBt]; exact Finset.mem_singleton_self _)
      · rw [h e he] at hne
        exact absurd hne (by simp)
  let S4 : Fin s → Finset (Fin n × Fin m) := fun j => T.filter (fun q =>
    q.1 ∈ SP j ∧ SL j = ∅ ∧ (∃ i, B i = {q.2} ∧ SP j ⊆ A i) ∧
      ∃ p' ∈ SP j, p' ≠ q.1 ∧ (p', q.2) ∈ T)
  have mS4 : ∀ j q, q ∈ S4 j ↔ (q ∈ T ∧ q.1 ∈ SP j ∧ SL j = ∅ ∧
      (∃ i, B i = {q.2} ∧ SP j ⊆ A i) ∧ ∃ p' ∈ SP j, p' ≠ q.1 ∧ (p', q.2) ∈ T) := by
    intro j q
    simp only [S4, Finset.mem_filter]
  let K : Finset (Fin k) := Finset.univ.filter (fun t =>
    (B t).card = 1 ∧ ∃ g ∈ A t, ∃ l ∈ B t, inc g l = false)
  have mK : ∀ t, t ∈ K ↔ ((B t).card = 1 ∧ ∃ g ∈ A t, ∃ l ∈ B t, inc g l = false) := by
    intro t
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  let τ : Fin k → Finset (Fin n × Fin m) := fun t => T.filter (fun q => q.1 ∈ A t ∧ B t = {q.2})
  have mτ : ∀ t q, q ∈ τ t ↔ (q ∈ T ∧ q.1 ∈ A t ∧ B t = {q.2}) := by
    intro t q
    simp only [τ, Finset.mem_filter]
  have U4 : ∀ j, ∀ q ∈ S4 j, ∀ q' ∈ S4 j, q.2 = q'.2 := by
    intro j q hq1 q' hq2
    obtain ⟨hqT, hp, -, -, p', hp', hpne, hp'T⟩ := (mS4 j q).mp hq1
    obtain ⟨hq'T, -, -, ⟨i2, hB2, hsub2⟩, -⟩ := (mS4 j q').mp hq2
    by_contra hne
    exact hq p' q.1 q.2 q'.2 hpne hne (hT _ hp'T).1 (hT q hqT).1
      (F4 _ hp'T i2 q'.2 (hsub2 hp') hB2) (F4 q hqT i2 q'.2 (hsub2 hp) hB2)
  have two : ∀ (Z : Finset (Fin n × Fin m)), ¬ Z.card ≤ 1 → ∃ q ∈ Z, ∃ q' ∈ Z, q ≠ q' := by
    intro Z hZ
    exact Finset.one_lt_card.mp (by omega)
  have hS : ∀ j, ∃ X Y, S4 j ⊆ X ∪ Y ∧ (X.card ≤ 1 ∨ ∃ j', j' < j ∧ X ⊆ S4 j') ∧
      (Y.card ≤ 1 ∨ ∃ j', j' < j ∧ Y ⊆ S4 j') := by
    intro j
    obtain ⟨XP, YP, XL, YL, hP, hL, hX, hY⟩ := hG j
    have key : ∀ (ZP : Finset (Fin n)) (ZL : Finset (Fin m)), ZP ⊆ SP j → ZL ⊆ SL j →
        (ZP.card + ZL.card ≤ 1 ∨ ∃ j', j' < j ∧ ZP = SP j' ∧ ZL = SL j') →
        (((S4 j).filter (fun q => q.1 ∈ ZP)).card ≤ 1 ∨
          ∃ j', j' < j ∧ (S4 j).filter (fun q => q.1 ∈ ZP) ⊆ S4 j') := by
      intro ZP ZL hZP hZL hZ
      by_cases hc : ((S4 j).filter (fun q => q.1 ∈ ZP)).card ≤ 1
      · left; exact hc
      · right
        obtain ⟨q, hq1, q', hq2, hne⟩ := two _ hc
        obtain ⟨hqS, hqZ⟩ := Finset.mem_filter.mp hq1
        obtain ⟨hq'S, hq'Z⟩ := Finset.mem_filter.mp hq2
        have e2 : q.2 = q'.2 := U4 j q hqS q' hq'S
        have e1 : q.1 ≠ q'.1 := fun h => hne (Prod.ext h e2)
        have hZc : 2 ≤ ZP.card := Finset.one_lt_card.mpr ⟨q.1, hqZ, q'.1, hq'Z, e1⟩
        rcases hZ with h | ⟨j', hj', eP, eL⟩
        · omega
        · refine ⟨j', hj', ?_⟩
          intro r hr
          obtain ⟨hrS, hrZ⟩ := Finset.mem_filter.mp hr
          have er : r.2 = q.2 := U4 j r hrS q hqS
          have hqT : q ∈ T := ((mS4 j q).mp hqS).1
          have hq'T : q' ∈ T := ((mS4 j q').mp hq'S).1
          obtain ⟨hrT, -, hl, ⟨i, hBi, hsubi⟩, -⟩ := (mS4 j r).mp hrS
          refine (mS4 j' r).mpr ⟨hrT, by rw [← eP]; exact hrZ, ?_,
            ⟨i, hBi, by rw [← eP]; exact hZP.trans hsubi⟩, ?_⟩
          · rw [← eL]
            exact Finset.subset_empty.mp (by rw [← hl]; exact hZL)
          · by_cases h1 : q.1 = r.1
            · refine ⟨q'.1, by rw [← eP]; exact hq'Z, fun h => e1 (h1.trans h.symm), ?_⟩
              have e3 : (q'.1, r.2) = q' := Prod.ext rfl (by show r.2 = q'.2; rw [er, e2])
              rw [e3]
              exact hq'T
            · refine ⟨q.1, by rw [← eP]; exact hqZ, h1, ?_⟩
              have e3 : (q.1, r.2) = q := Prod.ext rfl er
              rw [e3]
              exact hqT
    refine ⟨(S4 j).filter (fun q => q.1 ∈ XP), (S4 j).filter (fun q => q.1 ∈ YP), ?_,
      key XP XL ?_ ?_ hX, key YP YL ?_ ?_ hY⟩
    · intro q hq1
      have h1 : q.1 ∈ SP j := ((mS4 j q).mp hq1).2.1
      rw [hP, Finset.mem_union] at h1
      rcases h1 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq1, h⟩)
    · rw [hP]; exact Finset.subset_union_left
    · rw [hL]; exact Finset.subset_union_left
    · rw [hP]; exact Finset.subset_union_right
    · rw [hL]; exact Finset.subset_union_right
  have hτ : ∀ t ∈ K, (τ t).card ≤ 1 ∨ ∃ j, τ t ⊆ S4 j := by
    intro t _
    by_cases hc : (τ t).card ≤ 1
    · left; exact hc
    · right
      obtain ⟨q, hq1, q', hq2, hne⟩ := two _ hc
      obtain ⟨hqT, hqA, hqB⟩ := (mτ t q).mp hq1
      obtain ⟨hq'T, hq'A, hq'B⟩ := (mτ t q').mp hq2
      have e2 : q.2 = q'.2 := by
        have h : q.2 ∈ B t := by rw [hqB]; exact Finset.mem_singleton_self _
        rw [hq'B] at h
        exact Finset.mem_singleton.mp h
      have e1 : q.1 ≠ q'.1 := fun h => hne (Prod.ext h e2)
      have hAc : 2 ≤ (A t).card := Finset.one_lt_card.mpr ⟨q.1, hqA, q'.1, hq'A, e1⟩
      rcases hA t with h | ⟨j, hj1, hj2⟩
      · omega
      · refine ⟨j, ?_⟩
        intro r hr
        obtain ⟨hrT, hrA, hrB⟩ := (mτ t r).mp hr
        have er : r.2 = q.2 := by
          have h : r.2 ∈ B t := by rw [hrB]; exact Finset.mem_singleton_self _
          rw [hqB] at h
          exact Finset.mem_singleton.mp h
        refine (mS4 j r).mpr ⟨hrT, by rw [hj2]; exact hrA, hj1, ⟨t, hrB, by rw [hj2]⟩, ?_⟩
        by_cases h1 : q.1 = r.1
        · refine ⟨q'.1, by rw [hj2]; exact hq'A, fun h => e1 (h1.trans h.symm), ?_⟩
          have e3 : (q'.1, r.2) = q' := Prod.ext rfl (by show r.2 = q'.2; rw [er, e2])
          rw [e3]
          exact hq'T
        · refine ⟨q.1, by rw [hj2]; exact hqA, h1, ?_⟩
          have e3 : (q.1, r.2) = q := Prod.ext rfl er
          rw [e3]
          exact hqT
  have hsub : T ⊆ K.biUnion τ := by
    intro q hqT
    obtain ⟨-, i, j, hAi, hBi, ⟨g, hg, hgf⟩, -⟩ := hT q hqT
    refine Finset.mem_biUnion.mpr ⟨i, (mK i).mpr ⟨by rw [hBi]; exact Finset.card_singleton _,
      g, hg, q.2, by rw [hBi]; exact Finset.mem_singleton_self _, hgf⟩, (mτ i q).mpr ⟨hqT, hAi, hBi⟩⟩
  refine ⟨Finset.univ.filter (fun j => 2 ≤ (S4 j ∩ T).card), K,
    U S4 hS K τ hτ T.card T rfl hsub, ?_, ?_⟩
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    obtain ⟨q, hq1, q', hq2, hne⟩ := Finset.one_lt_card.mp (show 1 < (S4 j ∩ T).card by omega)
    have hqS := (Finset.mem_inter.mp hq1).1
    have hq'S := (Finset.mem_inter.mp hq2).1
    have e2 : q.2 = q'.2 := U4 j q hqS q' hq'S
    have e1 : q.1 ≠ q'.1 := fun h => hne (Prod.ext h e2)
    obtain ⟨hqT, hp, hl, -, -⟩ := (mS4 j q).mp hqS
    obtain ⟨hq'T, hp', -, -, -⟩ := (mS4 j q').mp hq'S
    refine ⟨hl, q.2, q.1, q'.1, e1, hp, hp', hqT, ?_⟩
    have e3 : (q'.1, q.2) = q' := Prod.ext rfl e2
    rw [e3]
    exact hq'T
  · intro t ht
    exact (mK t).mp ht

lemma core (n m s k : ℕ) (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) (SP : Fin s → Finset (Fin n)) (SL : Fin s → Finset (Fin m))
    (hq : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (hG : ∀ j, ∃ (XP YP : Finset (Fin n)) (XL YL : Finset (Fin m)), SP j = XP ∪ YP ∧
      SL j = XL ∪ YL ∧ (XP.card + XL.card ≤ 1 ∨ ∃ j', j' < j ∧ XP = SP j' ∧ XL = SL j') ∧
      (YP.card + YL.card ≤ 1 ∨ ∃ j', j' < j ∧ YP = SP j' ∧ YL = SL j'))
    (hA : ∀ t, (A t).card ≤ 1 ∨ ∃ j, SL j = ∅ ∧ SP j = A t)
    (hB : ∀ t, (B t).card ≤ 1 ∨ ∃ j, SP j = ∅ ∧ SL j = B t)
    (hM1 : ∀ i j, i ≠ j → ∀ p, p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true))
    (hM2 : ∀ i j, i ≠ j → ∀ l, l ∈ B i → l ∈ B j →
      (∀ p ∈ A i, inc p l = true) ∨ (∀ p ∈ A j, inc p l = true))
    (Q : Finset (Fin n × Fin m))
    (hQ : ∀ q ∈ Q, inc q.1 q.2 = true ∧
      ∃ i j, i ≠ j ∧ q.1 ∈ A i ∧ q.2 ∈ B i ∧ q.1 ∈ A j ∧ q.2 ∈ B j)
    (Dset : Finset (Fin k))
    (hD : ∀ t, (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) →
      (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true) → t ∈ Dset) :
    Q.card ≤ s + k + Dset.card := by
  classical
  let T1 : Finset (Fin n × Fin m) := Q.filter (fun q =>
    ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc q.1 e = true)
  let T2 : Finset (Fin n × Fin m) := Q.filter (fun q =>
    ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g q.2 = true)
  let T3 : Finset (Fin n × Fin m) := Q.filter (fun q => ∃ t, A t = {q.1} ∧ B t = {q.2})
  let T4 : Finset (Fin n × Fin m) := Q.filter (fun q =>
    (¬ ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc q.1 e = true) ∧
    (¬ ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g q.2 = true) ∧
    ¬ ∃ t, A t = {q.1} ∧ B t = {q.2})
  have m1 : ∀ q, q ∈ T1 ↔ (q ∈ Q ∧
      ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc q.1 e = true) := by
    intro q; simp only [T1, Finset.mem_filter]
  have m2 : ∀ q, q ∈ T2 ↔ (q ∈ Q ∧
      ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g q.2 = true) := by
    intro q; simp only [T2, Finset.mem_filter]
  have m3 : ∀ q, q ∈ T3 ↔ (q ∈ Q ∧ ∃ t, A t = {q.1} ∧ B t = {q.2}) := by
    intro q; simp only [T3, Finset.mem_filter]
  have m4 : ∀ q, q ∈ T4 ↔ (q ∈ Q ∧
      (¬ ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc q.1 e = true) ∧
      (¬ ∃ t, q.1 ∈ A t ∧ q.2 ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g q.2 = true) ∧
      ¬ ∃ t, A t = {q.1} ∧ B t = {q.2}) := by
    intro q; simp only [T4, Finset.mem_filter]
  have hcover : Q.card ≤ T1.card + T2.card + T3.card + T4.card := by
    have hs : Q ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := by
      intro q hqQ
      by_cases h1 : q ∈ T1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h1))
      · by_cases h2 : q ∈ T2
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h2))
        · by_cases h3 : q ∈ T3
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h3)
          · refine Finset.mem_union_right _ ((m4 q).mpr ⟨hqQ, ?_, ?_, ?_⟩)
            · exact fun h => h1 ((m1 q).mpr ⟨hqQ, h⟩)
            · exact fun h => h2 ((m2 q).mpr ⟨hqQ, h⟩)
            · exact fun h => h3 ((m3 q).mpr ⟨hqQ, h⟩)
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le (T1 ∪ T2 ∪ T3) T4
    have h3 := Finset.card_union_le (T1 ∪ T2) T3
    have h4 := Finset.card_union_le T1 T2
    omega
  have hq' : ∀ p p' : Fin m, ∀ l l' : Fin n, p ≠ p' → l ≠ l' → inc l p = true → inc l p' = true →
      inc l' p = true → inc l' p' = true → False :=
    fun p p' l l' h1 h2 a b c d => hq l l' p p' h2 h1 a c b d
  have hG' : ∀ j, ∃ (XP YP : Finset (Fin m)) (XL YL : Finset (Fin n)), SL j = XP ∪ YP ∧
      SP j = XL ∪ YL ∧ (XP.card + XL.card ≤ 1 ∨ ∃ j', j' < j ∧ XP = SL j' ∧ XL = SP j') ∧
      (YP.card + YL.card ≤ 1 ∨ ∃ j', j' < j ∧ YP = SL j' ∧ YL = SP j') := by
    intro j
    obtain ⟨XP, YP, XL, YL, hP, hL, hX, hY⟩ := hG j
    refine ⟨XL, YL, XP, YP, hL, hP, ?_, ?_⟩
    · rcases hX with h | ⟨j', h, a, b⟩
      · left; omega
      · right; exact ⟨j', h, b, a⟩
    · rcases hY with h | ⟨j', h, a, b⟩
      · left; omega
      · right; exact ⟨j', h, b, a⟩
  obtain ⟨G1, K1, hb1, hG1, hK1⟩ := bound2 m n s k (fun l p => inc p l) B A SL SP hq' hG' hB
    (T1.image Prod.swap) (by
      intro q hqm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hqm
      obtain ⟨-, t, h1, h2, h3, h4⟩ := (m1 r).mp hr
      exact ⟨t, h2, h1, h3, h4⟩)
  rw [Finset.card_image_of_injective _ Prod.swap_injective] at hb1
  obtain ⟨G2, K2, hb2, hG2, hK2⟩ := bound2 n m s k inc A B SP SL hq hG hA T2 (by
    intro q hqm
    exact ((m2 q).mp hqm).2)
  have hT4 : ∀ q ∈ T4, inc q.1 q.2 = true ∧ ∃ i j, q.1 ∈ A i ∧ B i = {q.2} ∧
      (∃ g ∈ A i, inc g q.2 = false) ∧ A j = {q.1} ∧ q.2 ∈ B j ∧
      (∃ e ∈ B j, inc q.1 e = false) := by
    intro q hqm
    obtain ⟨hqQ, hn1, hn2, hn3⟩ := (m4 q).mp hqm
    obtain ⟨hinc, i, j, hij, hAi, hBi, hAj, hBj⟩ := hQ q hqQ
    refine ⟨hinc, ?_⟩
    have fB : ∀ t, q.1 ∈ A t → q.2 ∈ B t → (∀ e ∈ B t, inc q.1 e = true) → B t = {q.2} := by
      intro t h1 h2 h3
      have hc : (B t).card ≤ 1 := by
        by_contra hcon
        exact hn1 ⟨t, h1, h2, by omega, h3⟩
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨h2, fun x hx => Finset.card_le_one.mp hc x hx q.2 h2⟩
    have fA : ∀ t, q.1 ∈ A t → q.2 ∈ B t → (∀ g ∈ A t, inc g q.2 = true) → A t = {q.1} := by
      intro t h1 h2 h3
      have hc : (A t).card ≤ 1 := by
        by_contra hcon
        exact hn2 ⟨t, h1, h2, by omega, h3⟩
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨h1, fun x hx => Finset.card_le_one.mp hc x hx q.1 h1⟩
    have exA : ∀ t, q.1 ∈ A t → q.2 ∈ B t → B t = {q.2} → ∃ g ∈ A t, inc g q.2 = false := by
      intro t h1 h2 h3
      by_contra hcon
      push Not at hcon
      exact hn3 ⟨t, fA t h1 h2 (fun g hg => by simpa using hcon g hg), h3⟩
    have exB : ∀ t, q.1 ∈ A t → q.2 ∈ B t → A t = {q.1} → ∃ e ∈ B t, inc q.1 e = false := by
      intro t h1 h2 h3
      by_contra hcon
      push Not at hcon
      exact hn3 ⟨t, h3, fB t h1 h2 (fun e he => by simpa using hcon e he)⟩
    rcases hM1 i j hij q.1 hAi hAj with b1 | b1 <;> rcases hM2 i j hij q.2 hBi hBj with a1 | a1
    · exact absurd ⟨i, fA i hAi hBi a1, fB i hAi hBi b1⟩ hn3
    · have e1 := fB i hAi hBi b1
      have e2 := fA j hAj hBj a1
      exact ⟨i, j, hAi, e1, exA i hAi hBi e1, e2, hBj, exB j hAj hBj e2⟩
    · have e1 := fB j hAj hBj b1
      have e2 := fA i hAi hBi a1
      exact ⟨j, i, hAj, e1, exA j hAj hBj e1, e2, hBi, exB i hAi hBi e2⟩
    · exact absurd ⟨j, fA j hAj hBj a1, fB j hAj hBj b1⟩ hn3
  obtain ⟨G4, K4, hb4, hG4, hK4⟩ := bound4 n m s k inc A B SP SL hq hG hA hM1 T4 hT4
  let K3 : Finset (Fin k) := Finset.univ.filter (fun t =>
    (A t).card = 1 ∧ (B t).card = 1 ∧ ∀ g ∈ A t, ∀ l ∈ B t, inc g l = true)
  have mK3 : ∀ t, t ∈ K3 ↔ ((A t).card = 1 ∧ (B t).card = 1 ∧
      ∀ g ∈ A t, ∀ l ∈ B t, inc g l = true) := by
    intro t; simp only [K3, Finset.mem_filter, Finset.mem_univ, true_and]
  have hb3 : T3.card ≤ K3.card := by
    have h1 : T3 ⊆ K3.biUnion (fun t => A t ×ˢ B t) := by
      intro q hqm
      obtain ⟨hqQ, t, hAt, hBt⟩ := (m3 q).mp hqm
      refine Finset.mem_biUnion.mpr ⟨t, (mK3 t).mpr ⟨by rw [hAt]; exact Finset.card_singleton _,
        by rw [hBt]; exact Finset.card_singleton _, ?_⟩, ?_⟩
      · intro g hg l hl
        rw [hAt, Finset.mem_singleton] at hg
        rw [hBt, Finset.mem_singleton] at hl
        rw [hg, hl]
        exact (hQ q hqQ).1
      · rw [Finset.mem_product, hAt, hBt]
        exact ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    have h2 : (K3.biUnion (fun t => A t ×ˢ B t)).card ≤ ∑ t ∈ K3, (A t ×ˢ B t).card :=
      Finset.card_biUnion_le
    have h3 : ∑ t ∈ K3, (A t ×ˢ B t).card ≤ ∑ t ∈ K3, 1 := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨ha, hb, -⟩ := (mK3 t).mp ht
      rw [Finset.card_product, ha, hb]
    have h4 : ∑ t ∈ K3, 1 = K3.card := by simp
    have h5 := Finset.card_le_card h1
    omega
  have hgates : G1.card + G2.card + G4.card ≤ s := by
    have h := card3 G1 G2 G4 ?_ ?_ ?_
    · rw [Fintype.card_fin] at h; exact h
    · rw [Finset.disjoint_left]
      intro j h1 h2
      obtain ⟨e, -⟩ := hG1 j h1
      obtain ⟨-, t, f, -, -, -, hc⟩ := hG2 j h2
      rw [e] at hc
      simp at hc
    · rw [Finset.disjoint_left]
      intro j h1 h2
      obtain ⟨e, -⟩ := hG1 j h1
      obtain ⟨-, l, p, p', -, hp, -⟩ := hG4 j h2
      rw [e] at hp
      simp at hp
    · rw [Finset.disjoint_left]
      intro j h2 h4
      obtain ⟨-, t, f, hsub, hfB, hinc, -⟩ := hG2 j h2
      obtain ⟨-, l, p, p', hne, hp, hp', hpT, hp'T⟩ := hG4 j h4
      obtain ⟨hpQ, -, hn2, -⟩ := (m4 _).mp hpT
      obtain ⟨hp'Q, -⟩ := (m4 _).mp hp'T
      have i1 : inc p l = true := (hQ _ hpQ).1
      have i2 : inc p' l = true := (hQ _ hp'Q).1
      have hfl : f = l := by
        by_contra hfl
        exact hq p p' f l hne hfl (hinc p (hsub hp)) (hinc p' (hsub hp')) i1 i2
      apply hn2
      refine ⟨t, hsub hp, ?_, Finset.one_lt_card.mpr ⟨p, hsub hp, p', hsub hp', hne⟩, ?_⟩
      · show l ∈ B t
        rw [← hfl]; exact hfB
      · intro g hg
        show inc g l = true
        rw [← hfl]; exact hinc g hg
  have hrects : K1.card + K2.card + K3.card + K4.card ≤ k + Dset.card := by
    have h := card3 (K1 ∪ K2) K3 K4 ?_ ?_ ?_
    · rw [Fintype.card_fin] at h
      have h1 := Finset.card_union_add_card_inter K1 K2
      have h2 : (K1 ∩ K2).card ≤ Dset.card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨ht1, ht2⟩ := Finset.mem_inter.mp ht
        obtain ⟨hc1, c, -, hc⟩ := hK1 t ht1
        obtain ⟨hc2, f, hf, hf2⟩ := hK2 t ht2
        exact hD t ⟨c, hc1, hc⟩ ⟨f, hf, hc2, hf2⟩
      omega
    · rw [Finset.disjoint_left]
      intro t h1 h3
      obtain ⟨ha, hb, -⟩ := (mK3 t).mp h3
      rcases Finset.mem_union.mp h1 with h | h
      · have := (hK1 t h).1; omega
      · have := (hK2 t h).1; omega
    · rw [Finset.disjoint_left]
      intro t h1 h4
      obtain ⟨hb, g, hg, l, hl, hgl⟩ := hK4 t h4
      rcases Finset.mem_union.mp h1 with h | h
      · have := (hK1 t h).1; omega
      · obtain ⟨-, f, hf, hf2⟩ := hK2 t h
        have e : f = l := Finset.card_le_one.mp (by omega) f hf l hl
        rw [← e, hf2 g hg] at hgl
        simp at hgl
    · rw [Finset.disjoint_left]
      intro t h3 h4
      obtain ⟨-, -, h⟩ := (mK3 t).mp h3
      obtain ⟨-, g, hg, l, hl, hgl⟩ := hK4 t h4
      rw [h g hg l hl] at hgl
      simp at hgl
  omega

end PEqualNP.Outside.L_meta_3063

open PEqualNP.Outside.L_meta_3063 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_3063 : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  intro n m inc C s k T a b A B hq _ hrb hsize hk hor hrect heval hrej
  have hlen : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)), (inp n m P L).length = n + m :=
    fun P L => inp_len n m P L
  have hglen : C.gates.length = s + k + T := hsize
  have hrw : ∀ (i : Fin k) (x : List Bool), x.length = n + m →
      (C.wires x).getD (n + m + s + i.val) false =
        (decide (∃ pa ∈ A i, x.getD pa.val false = true) &&
          decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true)) := by
    intro i x hx
    obtain ⟨-, -, -, -, hop, hin, hsem⟩ := hrect i
    have hg := gate_sem C (n + m) hrb x hx (s + i.val) (by have := i.isLt; omega)
    rw [← add_assoc] at hg
    rw [hg, hop, hin, ← (hsem x hx).1, ← (hsem x hx).2]
    simp [GateOp.eval]
  have hrI : ∀ (i : Fin k) (P : Finset (Fin n)) (L : Finset (Fin m)),
      ((C.wires (inp n m P L)).getD (n + m + s + i.val) false = true ↔
        (∃ pa ∈ A i, pa ∈ P) ∧ ∃ lb ∈ B i, lb ∈ L) := by
    intro i P L
    rw [hrw i _ (hlen P L)]
    simp only [inp_left, inp_right]
    simp
  have hev : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)), (C.eval (inp n m P L) = true ↔
      ∃ i1 j1 : Fin k, i1 < j1 ∧ ((∃ pa ∈ A i1, pa ∈ P) ∧ ∃ lb ∈ B i1, lb ∈ L) ∧
        ((∃ pa ∈ A j1, pa ∈ P) ∧ ∃ lb ∈ B j1, lb ∈ L)) := by
    intro P L
    rw [heval _ (hlen P L), decide_eq_true_iff]
    simp only [hrI]
  have hev2 : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)) (i j : Fin k), i ≠ j →
      ((∃ pa ∈ A i, pa ∈ P) ∧ ∃ lb ∈ B i, lb ∈ L) → ((∃ pa ∈ A j, pa ∈ P) ∧ ∃ lb ∈ B j, lb ∈ L) →
      C.eval (inp n m P L) = true := by
    intro P L i j hij h1 h2
    rcases lt_or_gt_of_ne hij with h | h
    · exact (hev P L).mpr ⟨i, j, h, h1, h2⟩
    · exact (hev P L).mpr ⟨j, i, h, h2, h1⟩
  have hM1 : ∀ i j, i ≠ j → ∀ p, p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true) := by
    intro i j hij p hpi hpj
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨l, hl, hl'⟩, ⟨e, he, he'⟩⟩ := hcon
    have h1 : C.eval (inp n m {p} {l, e}) = false :=
      hrej {p} {l, e} (Or.inl ⟨Finset.card_singleton p, Finset.card_le_two⟩) (by
        intro p' hp' l' hl2
        rw [Finset.mem_singleton] at hp'
        rw [Finset.mem_insert, Finset.mem_singleton] at hl2
        rw [hp']
        rcases hl2 with h | h
        · rw [h]; simpa using hl'
        · rw [h]; simpa using he')
    have h2 := hev2 {p} {l, e} i j hij
      ⟨⟨p, hpi, Finset.mem_singleton_self _⟩, ⟨l, hl, by simp⟩⟩
      ⟨⟨p, hpj, Finset.mem_singleton_self _⟩, ⟨e, he, by simp⟩⟩
    rw [h1] at h2
    exact absurd h2 (by simp)
  have hM2 : ∀ i j, i ≠ j → ∀ l, l ∈ B i → l ∈ B j →
      (∀ p ∈ A i, inc p l = true) ∨ (∀ p ∈ A j, inc p l = true) := by
    intro i j hij l hli hlj
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨p, hp, hp'⟩, ⟨g, hg, hg'⟩⟩ := hcon
    have h1 : C.eval (inp n m {p, g} {l}) = false :=
      hrej {p, g} {l} (Or.inr ⟨Finset.card_le_two, Finset.card_singleton l⟩) (by
        intro p' hp2 l' hl2
        rw [Finset.mem_singleton] at hl2
        rw [Finset.mem_insert, Finset.mem_singleton] at hp2
        rw [hl2]
        rcases hp2 with h | h
        · rw [h]; simpa using hp'
        · rw [h]; simpa using hg')
    have h2 := hev2 {p, g} {l} i j hij
      ⟨⟨p, hp, by simp⟩, ⟨l, hli, Finset.mem_singleton_self _⟩⟩
      ⟨⟨g, hg, by simp⟩, ⟨l, hlj, Finset.mem_singleton_self _⟩⟩
    rw [h1] at h2
    exact absurd h2 (by simp)
  let SPw : ℕ → Finset (Fin n) := fun w => Finset.univ.filter (fun p =>
    (C.wires (inp n m {p} ∅)).getD w false = true)
  let SLw : ℕ → Finset (Fin m) := fun w => Finset.univ.filter (fun l =>
    (C.wires (inp n m ∅ {l})).getD w false = true)
  have mP : ∀ w p, p ∈ SPw w ↔ (C.wires (inp n m {p} ∅)).getD w false = true := by
    intro w p; simp only [SPw, Finset.mem_filter, Finset.mem_univ, true_and]
  have mL : ∀ w l, l ∈ SLw w ↔ (C.wires (inp n m ∅ {l})).getD w false = true := by
    intro w l; simp only [SLw, Finset.mem_filter, Finset.mem_univ, true_and]
  have hwin : ∀ (u : ℕ) (x : List Bool), u < n + m → x.length = n + m →
      (C.wires x).getD u false = x.getD u false :=
    fun u x hu hx => fold_pre C.gates x u (by omega)
  have hin : ∀ u, u < n + m → (SPw u).card + (SLw u).card ≤ 1 := by
    intro u hu
    by_cases h : u < n
    · have e1 : SLw u = ∅ := by
        apply Finset.subset_empty.mp
        intro l hl
        have h1 := (mL u l).mp hl
        rw [hwin u _ hu (hlen _ _), inp_get_lt n m _ _ u h] at h1
        simp at h1
      have e2 : (SPw u).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro p hp p' hp'
        have h1 := (mP u p).mp hp
        have h2 := (mP u p').mp hp'
        rw [hwin u _ hu (hlen _ _), inp_get_lt n m _ _ u h] at h1 h2
        simp at h1 h2
        rw [← h1, ← h2]
      rw [e1, Finset.card_empty]
      omega
    · have hn : n ≤ u := by omega
      have hm : u - n < m := by omega
      have e1 : SPw u = ∅ := by
        apply Finset.subset_empty.mp
        intro p hp
        have h1 := (mP u p).mp hp
        rw [hwin u _ hu (hlen _ _), inp_get_ge n m _ _ u hn hm] at h1
        simp at h1
      have e2 : (SLw u).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro l hl l' hl'
        have h1 := (mL u l).mp hl
        have h2 := (mL u l').mp hl'
        rw [hwin u _ hu (hlen _ _), inp_get_ge n m _ _ u hn hm] at h1 h2
        simp at h1 h2
        rw [← h1, ← h2]
      rw [e1, Finset.card_empty]
      omega
  have hG : ∀ j : Fin s, ∃ (XP YP : Finset (Fin n)) (XL YL : Finset (Fin m)),
      SPw (n + m + j.val) = XP ∪ YP ∧ SLw (n + m + j.val) = XL ∪ YL ∧
      (XP.card + XL.card ≤ 1 ∨ ∃ j' : Fin s, j' < j ∧ XP = SPw (n + m + j'.val) ∧
        XL = SLw (n + m + j'.val)) ∧
      (YP.card + YL.card ≤ 1 ∨ ∃ j' : Fin s, j' < j ∧ YP = SPw (n + m + j'.val) ∧
        YL = SLw (n + m + j'.val)) := by
    intro j
    obtain ⟨hop, hl2⟩ := hor j.val j.isLt
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hl2
    have hjs := j.isLt
    have hjlt : j.val < C.gates.length := by omega
    have hu : u < n + m + j.val := hrb j.val hjlt u (by rw [huv]; simp)
    have hv : v < n + m + j.val := hrb j.val hjlt v (by rw [huv]; simp)
    have hval : ∀ x : List Bool, x.length = n + m → (C.wires x).getD (n + m + j.val) false =
        ((C.wires x).getD u false || (C.wires x).getD v false) := by
      intro x hx
      rw [gate_sem C (n + m) hrb x hx j.val hjlt, hop, huv]
      simp [GateOp.eval]
    have hw : ∀ w, w < n + m + j.val → ((SPw w).card + (SLw w).card ≤ 1 ∨
        ∃ j' : Fin s, j' < j ∧ SPw w = SPw (n + m + j'.val) ∧ SLw w = SLw (n + m + j'.val)) := by
      intro w hw
      by_cases h : w < n + m
      · left; exact hin w h
      · right
        have e : n + m + (w - (n + m)) = w := by omega
        refine ⟨⟨w - (n + m), by omega⟩, Fin.lt_def.mpr (by show w - (n + m) < j.val; omega), ?_, ?_⟩
        · show SPw w = SPw (n + m + (w - (n + m)))
          rw [e]
        · show SLw w = SLw (n + m + (w - (n + m)))
          rw [e]
    refine ⟨SPw u, SPw v, SLw u, SLw v, ?_, ?_, hw u hu, hw v hv⟩
    · ext p
      rw [Finset.mem_union, mP, mP, mP, hval _ (hlen _ _)]
      simp
    · ext l
      rw [Finset.mem_union, mL, mL, mL, hval _ (hlen _ _)]
      simp
  have hA : ∀ t, (A t).card ≤ 1 ∨ ∃ j : Fin s, SLw (n + m + j.val) = ∅ ∧ SPw (n + m + j.val) = A t := by
    intro t
    obtain ⟨-, -, hat, -, -, -, hsem⟩ := hrect t
    have e1 : SPw (a t) = A t := by
      ext p
      rw [mP, (hsem _ (hlen _ _)).1]
      simp only [inp_left]
      simp
    have e2 : SLw (a t) = ∅ := by
      apply Finset.subset_empty.mp
      intro l hl
      have h1 := (mL _ l).mp hl
      rw [(hsem _ (hlen _ _)).1] at h1
      simp only [inp_left] at h1
      simp at h1
    by_cases h : a t < n + m
    · left
      have := hin (a t) h
      rw [e1] at this
      omega
    · right
      have e : n + m + (a t - (n + m)) = a t := by omega
      refine ⟨⟨a t - (n + m), by omega⟩, ?_, ?_⟩
      · show SLw (n + m + (a t - (n + m))) = ∅
        rw [e]; exact e2
      · show SPw (n + m + (a t - (n + m))) = A t
        rw [e]; exact e1
  have hB : ∀ t, (B t).card ≤ 1 ∨ ∃ j : Fin s, SPw (n + m + j.val) = ∅ ∧ SLw (n + m + j.val) = B t := by
    intro t
    obtain ⟨-, -, -, hbt, -, -, hsem⟩ := hrect t
    have e1 : SLw (b t) = B t := by
      ext l
      rw [mL, (hsem _ (hlen _ _)).2]
      simp only [inp_right]
      simp
    have e2 : SPw (b t) = ∅ := by
      apply Finset.subset_empty.mp
      intro p hp
      have h1 := (mP _ p).mp hp
      rw [(hsem _ (hlen _ _)).2] at h1
      simp only [inp_right] at h1
      simp at h1
    by_cases h : b t < n + m
    · left
      have := hin (b t) h
      rw [e1] at this
      omega
    · right
      have e : n + m + (b t - (n + m)) = b t := by omega
      refine ⟨⟨b t - (n + m), by omega⟩, ?_, ?_⟩
      · show SPw (n + m + (b t - (n + m))) = ∅
        rw [e]; exact e2
      · show SLw (n + m + (b t - (n + m))) = B t
        rw [e]; exact e1
  have main : ∀ Dset : Finset (Fin k),
      (∀ t, (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) →
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true) → t ∈ Dset) →
      ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
        C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++
          List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card ≤ s + k + Dset.card := by
    intro Dset hD
    refine core n m s k inc A B (fun j => SPw (n + m + j.val)) (fun j => SLw (n + m + j.val))
      hq hG hA hB hM1 hM2 _ ?_ Dset hD
    intro q hqm
    obtain ⟨-, hinc, hacc⟩ := Finset.mem_filter.mp hqm
    have e : (List.ofFn (fun u : Fin n => decide (u = q.1)) ++
        List.ofFn (fun v : Fin m => decide (v = q.2))) = inp n m {q.1} {q.2} := by
      simp only [inp, Finset.mem_singleton]
    rw [e, hev] at hacc
    obtain ⟨i1, j1, hlt, ⟨⟨pa, hpa, hpa'⟩, lb, hlb, hlb'⟩, ⟨pa2, hpa2, hpa2'⟩, lb2, hlb2, hlb2'⟩ := hacc
    rw [Finset.mem_singleton] at hpa' hlb' hpa2' hlb2'
    subst hpa' hlb'
    rw [hpa2'] at hpa2
    rw [hlb2'] at hlb2
    exact ⟨hinc, i1, j1, ne_of_lt hlt, hpa, hlb, hpa2, hlb2⟩
  refine ⟨main _ (fun t h1 h2 => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩), fun hkT => ?_⟩
  have h := main Finset.univ (fun _ _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [hsize]
  omega
